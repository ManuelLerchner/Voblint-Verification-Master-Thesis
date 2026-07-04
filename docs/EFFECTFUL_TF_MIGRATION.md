# Migration — effectful transfer functions and named global unknowns

Status: **CORE LANDED** (2026-06-17). The effectful infrastructure and the
backward-compatibility bridge are implemented and verified (`Voblint_Analysis`
and `Voblint_Formalization` build green, no `sorry`). Full Gap-1 generalisation
of the downstream pipeline is staged behind the bridge — see §8.

This document records the findings from investigating alignment of our proof
architecture with Goblint's `EqConstrSys` / `Spec` interfaces, and lays out a
concrete migration plan. The goal is thesis alignment: our constraint system should
directly correspond to Goblint's, not merely be morally equivalent.

---

## 1. Motivation: where we are vs. where Goblint is

### 1.1 Goblint's actual constraint system (from source)

Goblint's `src/constraint/constrSys.ml` defines two key interfaces:

**`GlobConstrSys`** — the high-level interface with a locals/globals split:

```ocaml
module type GlobConstrSys = sig
  module LVar : VarType       (* local variables: CFG node × context *)
  module GVar : VarType       (* global variables: analysis-defined names *)
  module D : Lattice.S        (* local domain *)
  module G : Lattice.S        (* global domain *)
  val system : LVar.t
    -> ((LVar.t -> D.t)           (* getl: read local  *)
    ->  (LVar.t -> D.t -> unit)   (* setl: side-effect to local (thread-spawn only) *)
    ->  (GVar.t -> G.t)           (* getg: read named global *)
    ->  (GVar.t -> G.t -> unit)   (* sideg: side-effect named global *)
    ->   D.t) option
end
```

**`EqConstrSys`** — the *flattened* interface used by the TD solver. Locals and globals
are collapsed into one variable type `v = [\`L of LVar.t | \`G of GVar.t]` via `Var2`:

```ocaml
module type EqConstrSys = sig
  type v    (* combined variable: `L node_ctx | `G gvar *)
  type d    (* single domain for all variables *)
  val system : v -> ((v -> d) -> (v -> d -> unit) -> d) option
  (*                  get         side               result *)
end
```

The `system v get side` function is given `get` (read any variable) and `side`
(write any variable) and returns the new value for `v`. Transfer functions call
`side` **inside** this function.

**`Spec`** — the per-analysis signature (what an analysis developer implements):

```ocaml
module type Spec = sig
  module D : Lattice.S        (* local domain  *)
  module G : Lattice.S        (* global domain *)
  module C : Printable.S      (* context type  *)
  module V : SpecSysVar       (* set of global variable names *)
  val assign : (D.t, G.t, C.t, V.t) man -> lval -> exp -> D.t
  val branch : (D.t, G.t, C.t, V.t) man -> exp -> bool -> D.t
  ...
end
```

The `man` (manager) record passed to every transfer function exposes:

```ocaml
type ('d,'g,'c,'v) man = {
  local  : 'd;
  global : 'v -> 'g;        (* read a named global *)
  sideg  : 'v -> 'g -> unit (* side-effect a named global *)
  ask    : 'a Queries.t -> 'a Queries.result;
  ...
}
```

### 1.2 Our current encoding

We implement **`EqConstrSys`** with:

| `EqConstrSys` | Our encoding |
|---|---|
| `v = \`L of LVar.t \| \`G of GVar.t` | `pp + unit` |
| `\`L (node, ctx)` | `Inl v : pp` (no context) |
| `\`G gvar` | `Inr () : unit` — **single** global |
| `get v` | `σ : pp + unit -> 'a abs_state` |
| `side v d` | `Side () contrib` nodes in strategy tree |
| `system v get side = d` | `side_cfg_T_ip g tf bot s0 : pp -> eqsT` |

The strategy tree (`eqsT`) is the tree-encoded form of `system`. Each `Side () v t`
node IS a `side (Inr ()) v` call. The vendored TD solver traverses these trees.

### 1.3 The two gaps

**Gap 1 — single global unknown.**
We use `Inr () : unit`; Goblint uses `Inr g : GVar.t` (arbitrary named globals).
All global contributions go to one pot; cannot route writes to different named
unknowns.

**Gap 2 — pure transfer functions.**
Our `apply_tf tf a σ : 'a abs_state -> 'a abs_state` is pure. The global
contribution is always `restrict_global(apply_tf ...)` — structurally determined,
always fires, always targets `Inr ()`. Goblint's TFs receive `man.global` and
`man.sideg` and call them conditionally inside the function body.

Gap 1 alone is a modest extension (rename `unit` to a name type). Gap 2 is the
meaningful one: it changes *what analyses can express*. This doc covers closing
both gaps together because Gap 2 without Gap 1 has limited practical effect.

---

## 2. Concrete example showing the precision gap

### Program

```
(* IMP2: variables starting with G are global per IMP2_Globals.is_global *)

Gflag := 1;
Gdata := 0;

fun write_data(x) =
  Gdata := x;

main:
  write_data(42);     (* Gdata should be SPos after this *)
  Gflag := 0;
  write_data(-17);    (* Gdata should be SNeg after this *)
```

Both calls go through the **same procedure CFG** for `write_data`. The goal is to
track: "what did Gdata receive when Gflag was 1?" and "what when Gflag was 0?"

### Current approach (Sign domain, single `Inr ()`)

`side_rhs_fold_ip` builds this tree for the `Gdata := x` edge:

```
QueryL u (λsu. QueryG () (λg.
  let res = apply_tf tf (EA_Assign "Gdata" x) (su ⊔ g) in
  Side () (restrict_global res)          (* always to Inr (), no routing *)
    (Answer (restrict_local res))))
```

Both calls fire `Side () ...` into the same `Inr ()`. The fixed point joins:

```
σ(Inr ()) = {Gflag = SPos, Gdata = SPos}   (* from call 1 *)
           ⊔ {Gflag = SZero, Gdata = SNeg}  (* from call 2 *)
           = {Gflag = STop, Gdata = STop}
```

**Result: Gdata = STop. No property is provable.**

### Effectful approach (named globals `Inr "Gdata_flagpos"` / `Inr "Gdata_flagneg"`)

The effectful TF for `Gdata := x` reads `Gflag` and routes:

```isabelle
definition flag_routed_write_tree ::
  "vname => aexp => pp => (vname, sign) edge_tf_tree"
where
  "flag_routed_write_tree target e u =
     QueryL u (\<lambda>local.
       QueryG ''Gflag'' (\<lambda>flag.
         let xval = aval_sign e local in
         if flag = SPos then
           Side ''Gdata_flagpos'' xval (Answer local)
         else
           Side ''Gdata_flagneg'' xval (Answer local)))"
```

The solver maintains two separate global unknowns:

| Unknown | Call sites that contribute | Fixed-point value |
|---|---|---|
| `Inr "Gdata_flagpos"` | only when `Gflag = SPos` | `SPos` |
| `Inr "Gdata_flagneg"` | only when `Gflag = SZero` | `SNeg` |

After `write_data(42)`: combine picks up `Gdata_flagpos = SPos`.
After `write_data(-17)`: combine picks up `Gdata_flagneg = SNeg`.

**Result: both properties are provable. The routing is impossible with pure TFs.**

### Why pure TFs cannot express this

`restrict_global(apply_tf tf a σ)` always fires exactly one `Side () contrib` into
`Inr ()`. There is no way to:
- Read one named global (`Gflag`) to decide which other global to write
- Conditionally *skip* contributing (emit no `Side`)
- Route to different target unknowns based on analysis state

The effectful TF tree can do all three via `QueryG g (λv. if ... then Side g1 ... else Side g2 ...)`.

### Broader pattern

The same flag-routed example is the template for:

- **Lock-sensitive analysis** — `sideg "Gdata_locked" x` only when `global "Glock" = Held`.
  The "locked" unknown stays precise; the merged one widens.
- **Analysis-invented tracking unknowns** — a TF side-effects `"Gdata_ever_neg"`
  (Boolean lattice) independently of `"Gdata"` (value). After widening destroys
  value precision, the property unknown survives.
- **Per-origin widening (update-rules, Stemmler et al. PLDI 2025)** — each call
  context contributes to `Inr (ctx, "Gdata")`. Toxic contributions from dead paths
  are retracted without touching live ones.

---

## 3. Migration plan

The vendored TD solver already handles arbitrary `Side`/`Query` patterns in strategy
trees. Only the *construction* of those trees needs to change.

### Step 1 — Monadic bind for strategy trees (`Strategy_Tree_Monad.thy`)

The missing ingredient: sequencing two trees — run tree `t`, take its `Answer v`,
pass `v` to continuation `k`. This is monadic bind:

```isabelle
fun seqcomp_tree ::
  "(pp, 'g, 'd) strategy_tree
   => ('d => (pp, 'g, 'd) strategy_tree)
   => (pp, 'g, 'd) strategy_tree"
where
  "seqcomp_tree (Answer v)   k = k v"
| "seqcomp_tree (QueryL u c) k = QueryL u  (\<lambda>d. seqcomp_tree (c d) k)"
| "seqcomp_tree (QueryG g c) k = QueryG g  (\<lambda>d. seqcomp_tree (c d) k)"
| "seqcomp_tree (Side g v t) k = Side g v  (seqcomp_tree t k)"
```

Key lemmas needed (≈50 lines):

```isabelle
(* traverse commutes with bind *)
lemma traverse_seqcomp:
  "traverse_rhs (seqcomp_tree t k) \<sigma> = traverse_rhs (k (traverse_rhs t \<sigma>)) \<sigma>"

(* monotonicity preserved by bind *)
lemma seqcomp_mono:
  "\<lbrakk> \<forall>\<sigma>1 \<sigma>2. \<sigma>1 \<le> \<sigma>2 \<longrightarrow> traverse_rhs t \<sigma>1 \<le> traverse_rhs t \<sigma>2;
     \<forall>v \<sigma>1 \<sigma>2. \<sigma>1 \<le> \<sigma>2 \<longrightarrow> traverse_rhs (k v) \<sigma>1 \<le> traverse_rhs (k v) \<sigma>2;
     \<forall>\<sigma> v1 v2. v1 \<le> v2 \<longrightarrow> traverse_rhs (k v1) \<sigma> \<le> traverse_rhs (k v2) \<sigma> \<rbrakk>
   \<Longrightarrow> \<sigma>1 \<le> \<sigma>2 \<longrightarrow> traverse_rhs (seqcomp_tree t k) \<sigma>1
                   \<le> traverse_rhs (seqcomp_tree t k) \<sigma>2"

(* dep_aux of bind is union of deps of both sides *)
lemma dep_aux_seqcomp:
  "dep_aux \<sigma> (seqcomp_tree t k) = dep_aux \<sigma> t \<union> dep_aux \<sigma> (k (traverse_rhs t \<sigma>))"
```

### Step 2 — Generalize `domain_transfer` to `effectful_domain_transfer`

**Modified: `Constraint_System.thy`**

Replace pure functions `'a abs_state -> 'a abs_state` with tree producers. Each
field returns a strategy tree given the source program point. The tree may
`QueryL`/`QueryG`, issue `Side` for any named global, and ends with `Answer`.

```isabelle
(* A tree for one edge: queries inputs, fires Side contributions, returns local result *)
type_synonym ('g, 'd) edge_tf_tree =
  "pp => (pp, 'g, 'd abs_state) strategy_tree"

record ('g, 'd) effectful_domain_transfer =
  etf_assign     :: "vname => aexp => ('g, 'd) edge_tf_tree"
  etf_assume     :: "bexp  => ('g, 'd) edge_tf_tree"
  etf_assume_not :: "bexp  => ('g, 'd) edge_tf_tree"
  etf_enter      :: "('g, 'd) edge_tf_tree"

fun apply_etf ::
  "('g, 'd) effectful_domain_transfer => edge_action => pp
   => (pp, 'g, 'd abs_state) strategy_tree"
```

**Backward-compat shim** — any existing `domain_transfer` lifts to
`effectful_domain_transfer` via `pure_edge_tree`. This is exactly the tree that
`side_rhs_fold_ip` currently builds by hand:

```isabelle
definition pure_edge_tree ::
  "'a::bounded_semilattice_sup_bot domain_transfer => edge_action => pp
   => (unit, 'a) edge_tf_tree"
where
  "pure_edge_tree tf a u =
     QueryL u (\<lambda>su. QueryG () (\<lambda>g.
       let res = apply_tf tf a (su \<squnion> g) in
       Side () (restrict_global res)
         (Answer (restrict_local res))))"
```

Sign and Interval migrate by wrapping their existing `domain_transfer` records in
`pure_edge_tree`. No existing proof breaks during transition.

### Step 3 — Rebuild `side_rhs_fold_ip` using `seqcomp_tree`

**Modified: `TD_Side_IP_Tree.thy`**

Replace the manual `QueryL`/`QueryG`/`Side` construction with composition of
per-edge trees using `seqcomp_tree`:

```isabelle
fun side_rhs_fold_ip_eff ::
  "('g, 'd::bounded_semilattice_sup_bot) effectful_domain_transfer
   => 'd abs_state
   => (pp \<times> edge_action) list => (pp \<times> pp) list
   => (pp, 'g, 'd abs_state) strategy_tree"
where
  "side_rhs_fold_ip_eff etf acc [] [] = Answer acc"
| "side_rhs_fold_ip_eff etf acc ((u, a) # ps) cs =
     seqcomp_tree (apply_etf etf a u)
       (\<lambda>res. side_rhs_fold_ip_eff etf (acc \<squnion> res) ps cs)"
| "side_rhs_fold_ip_eff etf acc [] ((cc, ex) # cs) = ..."
```

The per-edge TF tree already extracts the local result (returning `Answer (local_result)`
from inside the tree). The fold joins local results via the accumulator.

The denotation lemma `traverse_side_rhs_fold_ip` is restated using
`traverse_seqcomp`:

```isabelle
lemma traverse_side_rhs_fold_ip_eff:
  "traverse_rhs (side_rhs_fold_ip_eff etf acc es cs) \<sigma> =
   side_acc_ip_eff etf acc \<sigma> es cs"
```

where `side_acc_ip_eff` is defined using `traverse_rhs (apply_etf etf a u) \<sigma>` in
place of `restrict_local (apply_tf tf a (side_env \<sigma> u))`.

### Step 4 — Soundness locale

**Modified: `Constraint_System.thy`**

Replace `sound_transfer` with `sound_effectful_transfer`. The obligation is the
same mathematics stated against `traverse_rhs`:

```isabelle
locale sound_effectful_transfer = sound_domain +
  fixes etf :: "('g, 'd) effectful_domain_transfer"
  assumes etf_sound_assign:
    "\<forall>x e u \<sigma>. \<forall>s \<in> gamma_state (side_env (fun_of_st \<circ> \<sigma>) u).
       s(x := aval e s) \<in> gamma_state (traverse_rhs (etf_assign etf x e u) \<sigma>)"
  assumes etf_sound_assume: "..."
  assumes etf_sound_assume_not: "..."
  assumes etf_sound_enter: "..."
```

For `pure_edge_tree`, these reduce to the current `sound_transfer` obligations by
`traverse_seqcomp`. The Sign/Interval `interpretation sound_effectful_transfer`
proofs are mechanical rewrites of the existing ones.

> **Extension (2026-07-01, AD-35).** `etf_sound_enter` is a *lower* (soundness)
> bound only. The keyed context generator (`side_cfg_T_eff_cmp`), which filters
> `EA_Enter` from its intra fold, needs a matching *upper* bound; the sub-locale
> `sound_effectful_transfer_framed` (same file) adds it — a `fresh_frame`
> parameter with `etf_full (etf_enter etf u) σ ≤ fresh_frame ⊔ glob_env σ`. Domains
> riding the keyed context generator discharge this one extra lemma (sign:
> `sign_sound_etf_unit_framed`). See `docs/KEYED_CONTEXT_ENTER_FRAMED_MIGRATION.md`.

### Step 5 — Monotonicity and `mono_deps`

The TD solver requires `mono_deps` — dependency structure must not depend on `σ`.
For `pure_edge_tree` this holds structurally. For general effectful TF trees,
require `static_deps` as a locale assumption:

```isabelle
definition static_deps :: "(pp, 'g, 'd) strategy_tree => bool" where
  "static_deps t \<longleftrightarrow> (\<forall>\<sigma>1 \<sigma>2. dep_aux \<sigma>1 t = dep_aux \<sigma>2 t)"

locale static_effectful_transfer = effectful_domain_transfer +
  assumes etf_static_deps: "\<forall>a u. static_deps (apply_etf etf a u)"
```

`static_deps` is preserved by `seqcomp_tree` when both sides have static deps
(provable from `dep_aux_seqcomp`). Then `side_cfg_T_ip_mono_deps` follows as before.

**Important:** effectful TFs with data-dependent branching (`QueryG g (λv. if v > 0 then ... else ...)`)
that queries *different* further nodes in each branch would violate `static_deps`.
Well-structured TFs avoid this: the query structure (which `QueryL`/`QueryG` calls)
is fixed; only the values at `Side`/`Answer` nodes depend on `σ`.

### Step 6 — Gap 1: generalise `unit` to `'g`

**Modified: `TD_Side_CFG.thy`, `Exec_Bridge.thy`, `TD_Side_IP_*`**

Replace `pp + unit` with `pp + 'g` throughout. `Inr ()` becomes `Inr g` for each
global name `g : 'g`. `side_env` becomes:

```isabelle
definition side_env_g ::
  "(pp + 'g => 'a::bounded_semilattice_sup_bot abs_state) => 'g => pp => 'a abs_state"
where
  "side_env_g \<sigma> g v = \<sigma> (Inl v) \<squnion> \<sigma> (Inr g)"
```

Or, for a TF that reads multiple globals, the TF tree issues separate `QueryG g` calls.
The combine step merges: for each global `g`, `σ(Inr g)` is the accumulated
flow-insensitive value for that named global.

For IMP2 the natural choice is `'g = vname` — one unknown per global variable name.
The shim `pure_edge_tree` uses `'g = unit` (backward compat). New domains use
`'g = vname` or any richer index type.

---

## 4. What stays unchanged

| Component | Status |
|---|---|
| Vendored `TD.TD_side` | **unchanged** — already handles arbitrary trees |
| `TD_Side_IP_Interface`, `TD_Side_IP_Bounds`, `TD_Side_IP_Soundness` | **unchanged** |
| CFG infrastructure, `compile_prog`, collecting semantics | **unchanged** |
| `restrict_local`, `restrict_global` (on `'a abs_state`) | **unchanged** |
| `sound_domain`, `abstract_domain` | **unchanged** |
| `Exec_St`, `lookup_st`, `update_st` | **unchanged** |
| Sign/Interval domain *mathematics* | **unchanged** — only wrapped in `pure_edge_tree` |

---

## 5. File change summary

| File | Change |
|---|---|
| `Strategy_Tree_Monad.thy` | **new** — `seqcomp_tree` + 3 key lemmas |
| `Constraint_System.thy` | replace `domain_transfer` with `effectful_domain_transfer`; add `pure_edge_tree` shim; restate `sound_effectful_transfer` |
| `TD_Side_IP_Tree.thy` | rewrite `side_rhs_fold_ip` using `seqcomp_tree`; restate `side_acc_ip_eff` |
| `TD_Side_IP_Mono.thy` | **deleted** — shim mono re-proved in `TD_Side_IP_Eff_Soundness` via `_gen`; pure mono removed |
| `TD_Side_CFG.thy` | generalise `pp + unit` to `pp + 'g`; update `side_env` |
| `Exec_Bridge.thy` | update to `effectful_domain_transfer`; `pp + 'g` |
| `Sign_Domain.thy` | migrate to `effectful_domain_transfer` via `pure_edge_tree` |
| `Interval_Domain.thy` | same |
| `Sign_Side_IP_Soundness.thy` | restate `interpretation` in `sound_effectful_transfer` |
| `Interval_Side_IP_Soundness.thy` | same |
| Examples | update to new domain interface |

---

## 6. Effort estimate and risks

**Total estimate: 3–5 weeks.**

| Task | Effort | Risk |
|---|---|---|
| `seqcomp_tree` + `traverse_seqcomp` | 3–4 days | Low — structural induction |
| `dep_aux_seqcomp` / `static_deps` | 3–4 days | **Medium** — key interaction with solver preconditions |
| `effectful_domain_transfer` record + `apply_etf` | 1 day | Low |
| Rebuild `side_rhs_fold_ip_eff` | 2–3 days | Low — mirrors current structure |
| `side_acc_ip_eff` denotation | 2 days | Low |
| Re-prove `TD_Side_IP_Mono` | 1 week | **Medium** — monotonicity now depends on domain assumption `etf_mono` |
| Restate `sound_effectful_transfer` | 2 days | Low — direct rewrite |
| Sign/Interval migration (via shim) | 2–3 days | Low |
| Gap 1 (`pp + 'g` generalisation) | 1 week | **Medium** — touches all files that mention `Inr ()` |
| Examples + end-to-end | 3–4 days | Low |

**Main risk:** `dep_aux_seqcomp` — the dependency structure of `seqcomp_tree t k`
includes deps from both `t` and `k (traverse_rhs t σ)`. The latter depends on the
value produced by `t`, which makes `static_deps` of the composition depend on
`static_deps` of both `t` and the image of `k`. If any TF tree has value-dependent
branching that changes which nodes are queried, `mono_deps` breaks. Design all TF
trees to have fixed query structure (query the same nodes regardless of values seen).

**Safe invariant:** every `apply_etf etf a u` tree has the shape
`QueryL u (λ_. QueryG g1 (λ_. ... QueryG gN (λ_. [only Side/Answer nodes] ...)))`.
The `QueryL`/`QueryG` skeleton is fixed; only `Side`/`Answer` values vary. Enforce
this by construction in each domain's `effectful_domain_transfer` instantiation.

---

## 7. Correspondence to Goblint

After this migration, the mapping to Goblint is direct:

| Goblint | Our Isabelle |
|---|---|
| `EqConstrSys.system v get side` | `side_cfg_T_ip_eff g etf bot s0 : pp -> eqsT` |
| `v = \`L node \| \`G gvar` | `pp + 'g` |
| `get (\`L v)` | `QueryL v (λd. ...)` |
| `get (\`G g)` | `QueryG g (λd. ...)` |
| `side (\`G g) v` | `Side g v ...` |
| `Spec.assign man lv e` | `etf_assign etf (EA_Assign lv e) u` |
| `man.global g` | `QueryG g (λd. ...)` inside TF tree |
| `man.sideg g v` | `Side g v ...` inside TF tree |
| `man.local` | `QueryL u (λd. ...)` |

The thesis can then state: "our `effectful_domain_transfer` directly models
Goblint's `Spec` transfer functions; `apply_etf etf a u` is the tree-encoded form
of `Spec.assign` (or `branch`, `enter`, ...) receiving a manager with `global` and
`sideg`."

Context (`C : Printable.S`) remains out of scope — unknowns are bare `pp` with no
call-string tagging. This is the remaining honest gap to state in the thesis.

---

## 8. Implementation status (2026-06-17)

What landed and verified (`isabelle build` green for `Voblint_Analysis` +
`Voblint_Formalization`, no `sorry`):

| Piece | Location | Status |
|---|---|---|
| `seqcomp_tree` + `traverse_seqcomp` + `dep_aux_seqcomp` | `Strategy_Tree_Monad.thy` | **done** |
| `seqcomp_mono` (bind preserves monotonicity) | `Strategy_Tree_Monad.thy` | **done** |
| `static_deps` + `static_deps_seqcomp` (Step 5 dep machinery) | `Strategy_Tree_Monad.thy` | **done** |
| `edge_tf_tree`, `effectful_domain_transfer`, `apply_etf` | `Constraint_System.thy` | **done** |
| `restrict_local` / `restrict_global` moved here, `TD.Basics_side` imported | `Constraint_System.thy` | **done** |
| `pure_edge_tree`, `etf_from_tf`, `traverse_pure_edge_tree`, `apply_etf_from_tf` | `TD_Side_CFG.thy` | **done** |
| `side_env_g` (Gap-1 generic combiner) + `side_env = side_env_g _ ()` | `TD_Side_CFG.thy` | **done** |
| `side_rhs_fold_ip_eff` (Step 3 fold via `seqcomp_tree`) + `side_acc_ip_eff` denotation | `TD_Side_IP_Tree.thy` | **done** |
| Bridge: `side_cfg_T_ip_eff (etf_from_tf tf) = side_cfg_T_ip tf (\<squnion>)` | `TD_Side_IP_Tree.thy` | **done** |
| Shim mono (`side_cfg_T_ip_eff_is_mono_eq` / `_mono_sides` / `_mono_deps`) for `etf_from_tf` | `TD_Side_IP_Eff_Soundness.thy` (re-proved via `_gen`) | **done** |
| `seqcomp_mono`, `static_deps` + `static_deps_seqcomp` (Step 1/5 monad lemmas) | `Strategy_Tree_Monad.thy` | **done** |
| `etf_full` reassembly + `sound_effectful_transfer` locale (Step 4 contract) | `Constraint_System.thy` | **done** |
| `sound_transfer_imp_sound_effectful` (every sound pure domain satisfies the contract via the shim) | `TD_Side_CFG.thy` | **done** |
| Sign instance `sign_etf` + 3 preconditions + `sign_sound_etf : sound_effectful_transfer` | `Sign_Side_IP_Soundness.thy` | **done** |
| `etf_sound_nop` completes the 5-action contract | `Constraint_System.thy` | **done** |
| `edge_collect_etf_sound` + `ip_witness_gamma_eff` + `post_fixpoint_sound_at_ip_eff` (general-effectful IP collecting soundness) | `TD_Side_IP_Eff_Sound.thy` | **done** |
| `etf_combine` field + `etf_sound_combine` obligation (procedure return is now an analysis-customizable effectful TF, like Goblint's `combine`) | `Constraint_System.thy` | **done** |
| `pure_combine_tree` shim + `etf_from_tf` extended + `combine_states_sound` moved up to `Constraint_System` (single source of truth) | `Constraint_System.thy`, `TD_Side_CFG.thy` | **done** |
| Eff fold + denotation + bridge + soundness reworked to route combine through `etf_combine` | `TD_Side_IP_Tree.thy`, `TD_Side_IP_Eff_Sound.thy` | **done** |
| Effectful solver interface `td_cfg_side_ip_solver_eff` + `side_analyse_ip_eff` (TD_side backend on `side_cfg_T_ip_eff`) | `TD_Side_IP_Eff_Interface.thy` | **done** |
| Shim transfer `side_analyse_ip_eff (etf_from_tf tf) = side_analyse_ip tf` + end-to-end shim soundness `side_analyse_ip_eff_collect_sound_exit_pruned` | `TD_Side_IP_Eff_Interface.thy` | **done** |

The **bridge** is the key result: `side_cfg_T_ip_eff (etf_from_tf tf)` is *literally
the same strategy tree* as the pure `side_cfg_T_ip tf (\<squnion>)`. Every existing theorem
about the pure system — including the end-to-end IP soundness theorems in
`TD_Side_IP_Soundness` / `Sign_Side_IP_Soundness` — therefore applies verbatim to the
effectful-shim system. No soundness proof was duplicated.

The **soundness contract** `sound_effectful_transfer` (Step 4) is also in place and
*interpreted*, not orphaned: `sound_transfer_imp_sound_effectful` shows every sound
pure domain satisfies it via the shim, and `sign_sound_etf` is the concrete Sign
witness (`sound_effectful_transfer gamma_sign sign_etf`). The obligation is stated on
`etf_full` — the local Answer rejoined with the global Side contribution — because the
local restriction alone sends globals to `bot` (whose `gamma` is empty), so it can
never over-approximate a post-state touching globals; the contributions must be
reassembled first. This avoids the instantiation-gap audit failure (a locale with no
interpretation) and the definition-drift failure (a soundness statement that is
vacuously false on the restricted local).

The `effectful_domain_transfer` record is polymorphic in the global-name type `'g`,
so the *capability* to route to named globals (Gap 1) and to query/conditionally
side-effect (Gap 2) is present in the interface. The IP fold instantiates `'g = unit`
to interface with the existing unit-global IP soundness pipeline; the per-edge TF
trees may still be genuinely effectful.

The **general-effectful collecting soundness** theorem
`post_fixpoint_sound_at_ip_eff` is now proven (`TD_Side_IP_Eff_Sound.thy`),
mirroring the pure `post_fixpoint_sound_at_ip` in `context sound_effectful_transfer`.
It holds for *any* `etf` satisfying the contract — not just the shim — with concrete
soundness drawn from `edge_collect_etf_sound` (the five-action per-edge lemma) and the
combine soundness drawn from `etf_sound_combine`. The abstract step is
`etf_full (apply_etf etf a u) σ` and the abstract combine is `etf_full (etf_combine etf c ex) σ`,
so a genuinely effectful TF (named globals, conditional sides) — including a custom
procedure-return TF — is covered the moment its post-fixpoint `≤` bounds hold.

**Procedure return is now customizable.** `etf_combine` is a record field with its own
`etf_sound_combine` obligation, the fold routes return through `seqcomp_tree (etf_combine etf c ex)`,
and the soundness theorem's `combine_le` bound is `etf_full (etf_combine etf c ex) σ ≤ side_env σ ret`.
The fixed `combine_abs` is now just the shim default (`pure_combine_tree`), matching
Goblint's developer-implemented `combine`. `combine_states_sound` moved up to
`Constraint_System` as the single source of truth for both pipelines.

The **effectful solver interface** is now in place (`TD_Side_IP_Eff_Interface.thy`):
`td_cfg_side_ip_solver_eff` runs the vendored `TD_side` backend on
`side_cfg_T_ip_eff`, exposing `side_analyse_ip_eff`. For the shim it coincides with
the pure solver (`side_analyse_ip_eff (etf_from_tf tf) = side_analyse_ip tf`), and the
end-to-end soundness `side_analyse_ip_eff_collect_sound_exit_pruned` transports the
pure exit-pruned theorem across the shim — so **the effectful analyser is sound for
every sound pure domain, with examples ready to migrate to `side_analyse_ip_eff`.**

### The standalone effectful path is complete (no bridge)

The effectful pipeline is now **provably self-contained** — a non-shim `etf` obtains
the full solver interface and end-to-end soundness with no reference to
`side_cfg_T_ip`, the pure bounds, or `etf_from_tf`:

- **Mono (Step 1, `TD_Side_IP_Eff_Bounds.thy`).** `side_cfg_T_ip_eff_is_mono_eq_gen` /
  `_mono_sides_gen` / `_mono_deps_gen` discharge the three `TD_side` preconditions from
  a per-tree monotonicity / static-dependency contract — dischargeable for a real
  effectful `etf` via `seqcomp_mono` / `static_deps_seqcomp`. Supporting:
  `sides_of_rhs_seqcomp` / `_at` (the side-contribution bind laws).
- **Bounds (Step 2, `TD_Side_IP_Eff_Bounds.thy`).** `etf_combined_le_ip_eff` /
  `etf_combine_combined_le_ip_eff` discharge the per-edge / per-combine post-fixpoint
  bounds from a `part_post_solution` of `side_cfg_T_ip_eff g etf`. The
  `etf_full = traverse_rhs ⊔ sides_of_rhs` split makes these a clean `sup_mono`,
  cleaner than the pure `restrict_local/global` rejoin.
- **Pipeline (Step 3, `TD_Side_IP_Eff_Pipeline.thy`).**
  `td_cfg_side_ip_solver_eff_gen` builds the interface from the mono/static contract;
  `side_collect_sound_ip_at_eff` (in `sound_effectful_transfer`) gives collecting
  soundness from a post-solution. Together: a non-shim `etf` with the
  per-tree mono/static + `sound_effectful_transfer` contracts has the whole pipeline,
  pure layer untouched.

This settles the feasibility question: **the pure-shim bridge is avoidable; the
effectful path stands alone.**

### Sign/Interval headlines and examples migrated to the standalone path (2026-06-18)

The Sign and Interval headline soundness theorems and both side-effecting
examples now flow through the standalone effectful pipeline, with no reference to
`side_analyse_ip` or any pure IP soundness theorem. `Voblint_Formalization` builds
green, no `sorry`.

| Piece | Location | Status |
|---|---|---|
| Eff dependency cone (`dep_side_rhs_tree_ip_eff_edge` / `_combine`, `ip_reaches_imp_trans_dep_or_eq_side_eff`, `side_ip_cone_in_vars_eff`) | `TD_Side_IP_Eff_Soundness.thy` | **done** |
| Eff exit pruning + entry seeding (`side_collect_sound_ip_exit_pruned_eff`, `s0_le_side_env_entry_ip_eff`) | `TD_Side_IP_Eff_Soundness.thy` | **done** |
| Executable standalone soundness `side_analyse_ip_eff_collect_sound_exit_pruned_gen` (interface from the per-tree mono/static contract, no pure shim) | `TD_Side_IP_Eff_Soundness.thy` | **done** |
| Generic shim discharge of the cone contracts for `etf_from_tf` (`dep_aux_apply_etf_from_tf_src`, `static_deps_*`) | `TD_Side_IP_Eff_Soundness.thy` | **done** |
| `side_ip_sign_analysis_sound` re-proved via `side_analyse_ip_eff` + `sign_sound_etf` | `Sign_Side_IP_Soundness.thy` | **done** |
| `ivl_etf` / `ivl_sound_etf` instance + `side_ip_ivl_analysis_sound` on the eff path | `Interval_Side_IP_Soundness.thy` | **done** |
| Examples point at `side_analyse_ip_eff` / `sign_etf` / `ivl_etf` | `Example_Side_Proc_Global.thy`, `Example_Interval_Side_Proc_Global.thy` | **done** |

The `side_ip_*_analysis_sound` headlines are now stated against `side_analyse_ip_eff`
and proved by instantiating `side_analyse_ip_eff_collect_sound_exit_pruned_gen` at the
domain's `sound_effectful_transfer` witness, discharging the three TD_side
preconditions from `*_tf_mono` and the five cone contracts generically from the
`etf_from_tf` shim structure.

### Pure IP soundness + pure solver interface + pure bounds deleted (2026-06-18)

`Sign_Exec_Sound.thy` was re-based onto the standalone effectful soundness layer:
`Exec_Bridge.part_post_solution_st_to_abs_eff` maps the executable `'a st`
post-solution to a `part_post_solution` of `side_cfg_T_ip_eff (etf_from_tf tf)`,
and `sign_exec_sound_collecting` now draws its collecting soundness from
`sound_effectful_transfer.side_collect_sound_ip_exit_pruned_eff` (the Sign witness
`sign_sound_etf`) — no pure IP soundness theorem.  With that last consumer gone,
three whole pure files were deleted, `Voblint_Formalization` builds green, no `sorry`:

| Deleted | Was |
|---|---|
| `TD_Side_IP_Soundness.thy` | pure IP collecting soundness: `side_collect_sound_ip_at` / `_exit_pruned`, `ip_reaches_imp_trans_dep_or_eq_side`, `side_ip_cone_in_vars`, `side_analyse_ip_collect_sound_exit_pruned` |
| `TD_Side_IP_Interface.thy` | pure solver interface: `td_cfg_side_ip_solver` locale, `side_analyse_ip`, `side_cfg_ip_solve_dom`, `side_nu_at` / `side_stabl_at` / `side_env_at` |
| `TD_Side_IP_Bounds.thy` | pure post-solution bounds (`apply_tf_combined_le_ip`, `combine_combined_le_ip`, the pure dependency-cone membership and entry-seeding lemmas) |

Also removed: the `*_from_tf` shim transport family from `TD_Side_IP_Eff_Interface`.

### Pure monotonicity deleted (2026-06-18)

`TD_Side_IP_Mono.thy` has been deleted. The three shim monotonicity lemmas
(`side_cfg_T_ip_eff_is_mono_eq` / `_mono_sides` / `_mono_deps`) were re-proved in
`TD_Side_IP_Eff_Soundness.thy` using the generic `_gen` versions from
`TD_Side_IP_Eff_Bounds.thy` and structural properties of `pure_edge_tree` /
`pure_combine_tree`. `Exec_Bridge` was decoupled from the pure transport: a direct
`'a st`→eff fold simulation (`side_acc_ip_st_fun_of_st_eff`,
`side_glob_ip_st_fun_of_st_eff`) proves `part_post_solution_st_to_abs_eff` without
going through `side_cfg_T_ip`. `Voblint_Formalization` builds green, no `sorry`.

The pure fold (`side_acc_ip`, `side_rhs_fold_ip`, `side_glob_ip`) remains in
`TD_Side_IP_Tree.thy` as an internal stepping stone for the simulation proof;
it is not referenced from any soundness or interface theory outside `Exec_Bridge`.

### Open (non-blocking)

- **A non-shim effectful instance.** Wire one genuinely effectful `etf` (e.g. the
  flag-routed example in §2) through `side_analyse_ip_eff_collect_sound_exit_pruned_gen`
  to exercise the standalone path for real (precision the pure system cannot express).
- **Gap-1 end-to-end (`pp + 'g`).** The IP fold's combine/return linkage and
  `Exec_Bridge` still hardcode the single `Inr ()` global. Generalising these to
  `pp + 'g` (per §3 Step 6) is the remaining large change; `side_env_g` is the
  prepared entry point.

---

## 9. Gap-1 design decisions (2026-06-19)

### 9.1 The two open items are one item

A **non-shim precision example requires Gap-1** — it is not independent. With
`'g = unit` there is a single global pot `sigma (Inr ())`, and the soundness
contract `etf_sound_assign` forces any global write to contribute to it
(`etf_full` joins `sides_of_rhs t sigma (Inr ())`; suppressing the `Side`
collapses the global slot to `bot`, whose `gamma` is empty, so the obligation
fails). Conflicting writes (`Gdata := 5; Gdata := -5`) therefore force
`sigma (Inr ()) = STop`; no sound `'g = unit` etf beats the shim on global
precision. The doc's own §1.3 says it: "Gap 2 without Gap 1 has limited
practical effect." So the §8 "suppression-only example" idea is **unsound**; the
flag-routed example must use named globals (`'g = vname` / a finite index).

### 9.2 The infinite-join obstacle and its resolution

The vendored `Side y d t` already routes to the named slot `Inr y`
(`Basics_side.sides_of_rhs`), so the solver is `'g`-generic. The obstacle is in
*our* reassembly: a full-store abstract result (the headline's single
`abs_state` at the exit, and `etf_full`'s global coverage) must join **all**
named globals. Over an infinite `'g` that is an infinite `Sup`, which
`bounded_semilattice_sup_bot` (non-complete) lacks.

**Resolution — `'g::finite`.** The generic effectful pipeline carries a
`finite` sort constraint on the global-name type. A named-global analysis
enumerates its global unknowns as a finite type (this mirrors Goblint: a `Spec`
fixes a finite set of global-unknown *kinds*). The shim keeps `'g = unit`
(`unit::finite`), so every existing instance survives unchanged.

### 9.3 New primitives (replace the hardcoded `Inr ()`)

| Primitive | Definition | Role |
|---|---|---|
| `all_sides t sigma` | tree-recursive total of every `Side` contribution (`Side y d t -> d ⊔ all_sides t`) | finite by tree structure; replaces `sides_of_rhs t sigma (Inr ())` in `etf_full` |
| `etf_full t sigma` | `traverse_rhs t sigma ⊔ all_sides t sigma` | full-store post-state; coincides with the current def at `'g = unit` |
| `glob_env sigma` | `Finite_Set.fold (λg a. a ⊔ sigma (Inr g)) bot UNIV` | join of all named-global unknowns (matches the project's locked join convention) |
| `side_env_all sigma v` | `sigma (Inl v) ⊔ glob_env sigma` | full env at a point; `= side_env` at `'g = unit` |

The precision win lives in the **per-unknown** values
(`sigma (Inr ''Gdata_flagpos'') = SPos` distinct from `sigma (Inr ''Gdata_flagneg'') = SNeg`),
not in the merged exit store (which still joins to `STop`). The headline
soundness theorem keeps joining all globals via `glob_env`; the demonstrated
precision is the queryable per-name value the unit pot structurally cannot hold.

### 9.4 Implementation order (build-gated slices)

Status as of 2026-06-20: **Gap-1 is DONE.** All slices below landed, the full
`Voblint_Formalization` session builds green with no `sorry`, and a genuinely
effectful, named-global witness exercises the generalised interface for real.

**Architecture chosen — decouple, don't propagate.** The generalisation lives in
the *abstract* layer: the `sound_effectful_transfer` locale and the abstract
collecting-soundness (`edge_collect_etf_sound`, `ip_witness_gamma_eff`,
`post_fixpoint_sound_at_ip_eff`) are now polymorphic in `'g::finite`. The
*executable* solver construction (`side_cfg_T_ip_eff`, whose entry seeding emits
`Side ()`) stays at `'g = unit`; the three executable theorems were pulled out of
the generic locale and take `sound_effectful_transfer γ etf` as an explicit unit
hypothesis, interpreting the generic abstract soundness at unit. This made slice 4
(Exec_Bridge rework) **unnecessary** — the executable path is untouched. A
named-global analysis demonstrates its precision through the generic
`post_fixpoint_sound_at_ip_eff`, not through the unit solver. Note `'g::finite`
excludes `vname` (infinite); a finite `gname` type is used, matching Goblint's
finite set of global-unknown kinds.

- [x] **1. `all_sides` + coincidence.** `all_sides` primrec +
  `all_sides_eq_sides_Inr_unit` in `Constraint_System`. Commit `d2d0ecb`.
- [x] **2a. `etf_full` to `'g`.** Body is `traverse_rhs t s ⊔ all_sides t s`,
  polymorphic in `'g`; shim lemmas + post-fixpoint bounds carry over via the
  coincidence rewrite. Commit `51785fc`.
- [x] **glob_env infra.** `glob_env` (finite fold over `UNIV::'g::finite`) +
  `glob_env_upper` / `glob_env_unit` / `glob_env_mono` (commit `6727cc5`) and the
  bridge `all_sides_le_glob_env_sides : all_sides t s <= glob_env (sides_of_rhs t s)`
  (commit `f97e618`). These are exactly the primitives the cascade consumes; all
  additive, `Voblint_Analysis` green.
- [x] **2b. Generalised the `sound_effectful_transfer` locale** to
  `('g::finite, 'a)`; obligation source is now `sigma (Inl u) ⊔ glob_env sigma`.
  `side_env` redefined via `glob_env` (coincides at unit by `glob_env_unit`).
  `sound_transfer_imp_sound_effectful`, `sign_sound_etf`, `ivl_sound_etf`
  re-proved. Commit `3474bef`.
- [x] **3. Decoupled the executable soundness chain** rather than propagating
  `'g` into it. `edge_collect_etf_sound` / `ip_witness_gamma_eff` /
  `post_fixpoint_sound_at_ip_eff` are generic in-locale; the unit-bound executable
  theorems (`side_collect_sound_ip_at_eff`, `side_collect_sound_ip_exit_pruned_eff`,
  `side_analyse_ip_eff_collect_sound_exit_pruned_gen`) moved out of the locale with
  an explicit `sound_effectful_transfer γ etf` hypothesis. Sign/Interval headlines +
  `Sign_Exec_Sound` updated to `[OF ..._sound_etf ...]`. `glob_env` gets an
  `enum`-based executable code equation so the unit examples still code-generate.
  Commit `3474bef`.
- [x] **4. Exec_Bridge: no rework needed.** The decoupling keeps the executable
  path (incl. Exec_Bridge) at `'g = unit`; it is unchanged and green.
- [x] **5. Flag-routed named-global witness.** `Sign_Named_Global_Eff.thy`:
  `flag_etf :: (gname, sign) ...` routes the assign contribution to `Gpos` / `Gneg`
  by the queried sign of `''Gflag''`; `flag_etf_sound` proves
  `sound_effectful_transfer gamma_sign flag_etf` (the non-unit instantiation);
  `flag_assign_routes_pos` / `_neg` show the per-slot routing the unit pot cannot
  express. Commit `ef0baab`.

**Remaining honest gap (out of scope here):** the named-global example demonstrates
the capability and soundness at the *abstract* (post-fixpoint) level. A fully
*runnable* `gname`-indexed solver (executable `side_analyse` at `'g ≠ unit`) would
require generalising the entry seeding (`Side ()` → per-name seed) — the one piece
deliberately left unit-bound. The thesis claim (the effectful interface expresses
sound named-global routing the single pot cannot) is established without it.

## 10. Named-global solver construction generalised to `'g::finite` (2026-06-21)

**Level A is done.** The executable-solver-construction chain — previously
`unit`-bound because its entry seeding emitted `Side ()` — is now `'g::finite`
generic with a designated seed-slot parameter `gseed :: 'g`, and a genuinely
named-global analysis runs **through the real solver interface** end-to-end.

- **Seed-slot parameter.** `make_side_rhs_tree_eff` / `side_cfg_T_eff` /
  `side_cfg_solve_dom_eff` / the `td_cfg_side_solver_eff` locale / `nu_at` /
  `side_analyse_eff` all take `gseed :: 'g`; the entry wrap is
  `Side gseed (restrict_global s0)`. Entry coverage generalises from
  `restrict_global s0 ≤ σ (Inr ())` to `restrict_global s0 ≤ σ (Inr gseed) ≤
  glob_env σ` (`glob_env_upper`). Every unit caller (Sign/Interval headlines,
  `Exec_Bridge`, examples) threads `gseed = ()` and is unchanged in behaviour.
- **Global-half bounds restated per-name.** `etf_combined_le_eff` /
  `etf_combine_combined_le_eff` route the per-name side bound
  (`sides_of_rhs (T x) σ (Inr g) ≤ σ (Inr g)`) through
  `all_sides_le_glob_env_sides` + a new `glob_env_mono_Inr`, replacing the
  single-pot `all_sides_eq_sides_Inr_unit` step.
- **Headline (`Sign_Named_Global_Eff.named_ip_analysis_sound`).** The
  two-slot named-global Sign analysis `named_etf :: (gname, sign) ...` (edges →
  `Gpos`, combine → `Gneg`) over-approximates `cfg_collect` at the exit through
  `side_analyse_eff` at `'g = gname` — **not** the unit shim. Its three TD_side
  preconditions discharge for the non-shim etf from the generic `_gen` lemmas
  (`named_traverse_mono` / `named_sides_mono` / `named_edge_static` …), seeded at
  `gseed = Gpos`.

**Finding — conditional routing is not solver-compatible.** The
flag-conditional `flag_etf` is **not** `mono_sides`: as `σ` grows the reassembled
`''Gflag''` value can move `SPos → STop`, so `flag_route` flips the assign
contribution `Gpos → Gneg` and the side map drops its `Gpos` entry, breaking
`σ`-monotonicity of `sides_of_rhs`. So `flag_etf` cannot drive the fixpoint
solver (documented in `Sign_Named_Global_Eff.flag_etf_mono_sides_unprovable`,
deliberately `oops`). `flag_etf` remains the *per-tree precision* witness
(`flag_etf_sound`, `flag_assign_routes_pos` / `_neg`); the *through-solver*
headline uses the monotone constant-routed `named_etf`. This is the §9 risk made
concrete: the genuinely-effectful conditional routing and fixpoint-solver
monotonicity are in tension, and the named-global headline is carried by the
monotone (still non-unit, two-slot) witness.

**Level B (open, separate handoff): code-gen `value`-runnable demo.** `'a abs_state
= vname ⇒ 'a` is not executable; the executable path uses `'a st` (`Exec_St`)
bridged by `Exec_Bridge` (`part_post_solution_st_to_abs_eff`), still at
`'g = unit`. Making *that* run at `'g = gname` (generalising `Exec_St`'s side
fold + `Exec_Bridge`) is the remaining piece — only then can one `value`-observe
`Gpos` and `Gneg` holding distinct values. Not started.
