# Migration — effectful transfer functions and named global unknowns

Status: **PLANNED** (research findings 2026-06-17, not yet started).

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
| `TD_Side_IP_Mono.thy` | re-prove `is_mono_eq`, `mono_sides`, `mono_deps` for new fold |
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
