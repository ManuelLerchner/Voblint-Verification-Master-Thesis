# Audit: Local/Global Lattice Separation and a First-Class Combine Contract

**Status:** Design investigation only. No implementation. Grounds the "missing Goblint-style
analysis specification" work that the CTX cleanup did **not** deliver. **§6 refines Stage 0 into
an implementation-ready `call_spec` call contract** (interface, exact assumptions, CMP instance,
sequence, proof impact, Stage-1 blockers).

**Scope question:** What must change so that (1) locals and globals can carry *independent*
abstract lattices, and (2) call behaviour (enter/combine/return/global routing) is an
analysis-supplied contract with one generic soundness theorem — rather than the current
single-`'a`, `is_global`-partitioned, fixed-calling-convention design?

---

## 0. The one-sentence diagnosis

Everywhere a "state" appears — concrete or abstract, local or global, caller or callee — it is
the **same** `vname => 'a` map, and locals vs. globals are told apart only by the runtime
predicate `is_global :: vname => bool`. `'g` in the generator/tree types is a **routing key**,
not a global value lattice. Separation therefore requires splitting one type parameter into
two *everywhere the state flows*, and re-deriving every soundness obligation stated over the
single combined gamma.

---

## 1. Exact places where local and global are forced to share `'a`

### 1.1 The state type itself
- `src/IMP2/IMP2_Syntax.thy:26` — `type_synonym store = "vname => int"`. One concrete store;
  locals and globals are the same map.
- `src/IMP2/IMP2_Globals.thy:24` — `is_global :: vname => bool`. The *only* discriminator.
- `src/Analysis/Generic/Domain/Abstract_Domain.thy:23` — `type_synonym 'a abs_state = "vname => 'a"`.
  One abstract value type `'a` for every variable, local or global.
- `src/Analysis/Generic/Domain/Abstract_Domain.thy` (`gamma_state`, `\<lbrakk>_\<rbrakk>`) —
  `{s. ∀x. s x ∈ gamma (σ x)}`: a single `gamma` applied uniformly to all `vname`s.

### 1.2 The partition operators (share one `'a abs_state` in and out)
- `src/Analysis/Generic/Solver/Core/TD_Side_CFG.thy:25,29` — `restrict_local`, `restrict_global`
  `:: 'a abs_state => 'a abs_state`, bodies `if is_global x then bot else σ x` / vice versa.
- `src/Analysis/Generic/Equations/Constraint_System.thy:273` — `combine_abs sc se =
  (λx. if is_global x then se x else sc x)`; both arguments and result are `'a abs_state`.
- `src/Analysis/Generic/Domain/Exec_St.thy:521,525,531` — executable mirrors `restrict_local_st`,
  `restrict_global_st`, `combine_abs_st = restrict_local_st sc ⊔ restrict_global_st se`, all on a
  single `'a st`.

### 1.3 The transfer interface
- `src/Analysis/Generic/Equations/Constraint_System.thy:435` — `record ('g,'d) effectful_domain_transfer`.
  `'d` is the single value type; `etf_enter`, `etf_combine`, every `etf_*` produce a
  `'d abs_state`-valued `strategy_tree`. `'g` is the global **key**.
- `src/Analysis/Generic/Equations/Constraint_System.thy` (`combine_tf_tree`) —
  `pp => pp => (pp, 'g, 'd abs_state) strategy_tree`: caller and callee combine inputs share `'d`.

### 1.4 The strategy tree (routing key vs. value)
- `src/Analysis/Generic/Solver/Core/TD_Side_CFG.thy` (datatype `('x,'g,'d) strategy_tree`,
  constructors `Answer 'd | QueryL 'x (…'d) | QueryG 'g (…'d) | Side 'g 'd …`). A **global read**
  `QueryG :: 'g => ('d => tree)` returns the same `'d`, a **global write** `Side :: 'g => 'd => tree`
  writes the same `'d`. There is no separate global value type — only the key `'g`.

### 1.5 The soundness contract
- `src/Analysis/Generic/Equations/Constraint_System.thy:748` — `locale sound_effectful_transfer`
  fixes `etf :: ('g::finite, 'a::sound_domain) effectful_domain_transfer`. Every premise is stated
  over `\<lbrakk>σ (Inl u) ⊔ glob_env σ\<rbrakk>` — one gamma over the merged local+global abstract state.
  `etf_sound_combine` uses the concrete `<s|t>` (is_global merge); `etf_sound_enter` uses
  `enter_state` (reset locals, keep globals). Both bake in the single-domain, is_global convention.

**Consequence.** `'a` is threaded through ~6 layers (store → abs_state → transfer record → tree
value → generator → soundness locale). Separation is not a local edit; it is a type-parameter
split propagated through all of them.

---

## 2. Where combine logic is hard-coded vs. analysis-provided

### 2.1 Hard-coded (fixed by IMP2's calling convention)
- **Concrete combine** `combine_states` / `<s|t>` and its abstract image `combine_abs`
  (`Constraint_System.thy:273`): "globals from callee-exit, locals from caller" — fixed by
  `is_global`, not a parameter.
- **Concrete enter** `enter_state` (used at `sound_effectful_transfer.etf_sound_enter`): reset
  locals to `0`, keep globals — fixed.
- **Executable** `combine_abs_st` (`Exec_St.thy:531`): the same fixed merge.

These *define* what a sound combine must approximate; the analysis cannot change them.

### 2.2 Analysis-provided (but as low-level plumbing, not a contract)
- The generator takes a combine-tree **builder** `cmb :: 'c => pp => pp =>
  (pp × 'c, 'g, 'a abs_state) strategy_tree` as a parameter
  (`TD_Side_Eff_Cmp_Gen.thy:53`, `side_cfg_T_eff_cmp`).
- Instances supply `cmb`: `switching_combine_st` (`Exec_Cmp_Bridge.thy:219`),
  `kgen_combine_rread` (`Exec_Sign_Cmp_RRead_Split.thy:111`),
  `switching_combine_digest_st` (`Digest_Keyed_Writer.thy:83`).
- The **contract** the builder must meet is a post-hoc inequality predicate, not a function
  signature: `switching_combine_sound` (`TD_Side_Eff_Cmp_Gen.thy:890`) says *for any
  post-solution `σ`*, `etf_full (etf_combine etf cc ex) (pull_gk gkey ctx σ) ≤ side_env … ret`.
  Discharged for the certified fixed combine by
  `fixed_combine_satisfies_switching_combine_sound` (`:912`).

**Consequence.** Combine behaviour *is* customizable, but the "contract" is
`generator-solution-relative` and expressed against the fixed semantic `etf_combine`. There is
no clean first-class spec like

```isabelle
enter   :: 'local => 'context × 'local
combine :: 'caller_local => 'callee_global => 'local
```

with combine as a value-level function carrying its own soundness. Combine intent is spread
across: the `cmb` builder, the semantic `etf_combine` field, `restrict_local`/`restrict_global`,
`side_env`/`side_env_cmp` reads, `pull_gk` routing, and the `switching_combine_sound` obligation.

---

## 3. Minimal type/interface changes

Two independent axes. They can be pursued separately; (B) is cheaper and clarifies (A).

### Axis A — independent local/global lattices

Split the single `'a` into `'l` (local value) and `'g` (global value). Introduce a *split state*
rather than `vname => 'a`:

```isabelle
(* replaces 'a abs_state where a state spans both regions *)
record ('l, 'g) split_state =
  loc :: "lname => 'l"      (* local variables *)
  glb :: "gname => 'g"      (* global variables *)
```

with `'l :: abstract_domain`, `'g :: abstract_domain` independently, and two gammas
`gamma_l`, `gamma_g` combined into one `store`-level `gamma_split`. Then:

- `strategy_tree` gains a split value: `QueryL` returns `'l`, `QueryG`/`Side` use `'g`. Either
  a 4-parameter tree `('x, 'gkey, 'l, 'g)` or two Answer variants. This is the invasive change —
  the tree is the spine of the whole solver bridge.
- `effectful_domain_transfer` becomes `('gkey, 'l, 'g)`; `etf_assign` etc. produce `'l`-typed
  local edges, `etf_combine`/`etf_enter` cross the boundary and are typed
  `… => (…, 'l, 'g) strategy_tree`.
- `restrict_local`/`restrict_global`/`combine_abs` become total field projections/injections on
  `split_state` (no `is_global` test, no `bot`-padding).
- `sound_effectful_transfer` premises re-stated over `gamma_split`.

**Note (false economy to avoid):** keeping `vname => 'a` and instantiating `'a` to a sum
`'l + 'g` does **not** achieve separation — a variable would still be typed with both, and
`is_global` would still be the discriminator. Real separation needs the domain split at the
*state* level (two maps), which forces the tree/transfer split.

### Axis B — first-class combine/enter contract

Independently of A, lift the call behaviour into a locale with value-level operations plus one
generic soundness theorem:

```isabelle
locale call_spec =
  fixes enter   :: "'l => 'l"                       (* callee-entry local frame *)
    and combine :: "'l => 'g => 'l"                 (* caller local ⊕ callee global => local *)
    and read_g  :: "'context => 'gkey"              (* global-slot routing (today: gkey) *)
  assumes enter_sound   : "…gamma bound…"
    and   combine_sound : "…gamma bound…"
```

The generator would consume `call_spec` and emit the combine/enter trees from it, so instances
supply *functions*, not hand-built `strategy_tree`s, and the current
`switching_combine_sound`/`fixed_combine_satisfies_*` obligations become the locale's proven
assumptions. Under the present single-`'a`, `combine :: 'a => 'a => 'a` is `combine_abs`; under
Axis A it becomes the cross-domain `combine :: 'l => 'g => 'l`.

**The implementation-ready single-`'a` version of this locale is specified in §6.** The sketch
here is orientation; §6 fixes exact types, ownership, assumptions, and the CMP instance.

---

## 4. Expected proof impact

- **`combine_abs` / `restrict_*` layer** — *moderate.* These are definitional; re-proving
  `restrict_local_global_join`, `combine_states_sound`, `lookup_combine_abs_st` over a split
  state is mechanical but touches every downstream `simp` that unfolds them.
- **`strategy_tree` + `traverse_rhs`/`sides_of_rhs`/`dep_aux`** — *high.* Adding a value axis to
  the tree changes the monad laws (`seqcomp_tree`, `Strategy_Tree_Monad.thy`) and every fold
  lemma (`side_acc_ctx`, `side_rhs_fold_ctx`, the `map_ltree`/`map_gtree` routing). This is the
  spine; expect the largest churn.
- **Generator (`side_cfg_T_eff_cmp`) + routing (`pull_gk`, `traverse_intra_cmp`,
  `side_env`/`side_env_cmp`)** — *high.* Routing lemmas assume the local and global slots carry
  the same `'a`; the `map_sum` pullback splits into `'l`/`'g` halves.
- **CMP soundness (`TD_Side_Eff_Cmp_Sound`, built on `TD_Side_Eff_Ctx_Sound`)** — *high.* Every
  premise over `\<lbrakk>σ (Inl u) ⊔ glob_env σ\<rbrakk>` must be re-stated over two gammas.
  `post_fixpoint_sound_at_ctx_semantic` and its cmp refinement are the load-bearing theorems.
- **Axis B alone** — *low/moderate.* It reorganizes existing obligations behind a locale without
  changing types; `fixed_combine_satisfies_switching_combine_sound` already proves the discharge.
  This is the safe first increment.
- **Executable/`eval` examples** — *moderate but mechanical.* Code generation over a split state
  and the `by eval` witnesses re-run; no new mathematics.

Risk concentrates in the tree + routing + CMP-soundness triad, exactly the retained substrate
the CTX cleanup preserved.

---

## 5. Staged migration plan (design only — do not implement here)

Each stage is independently green-buildable and reviewable.

1. **Stage 0 — Axis B, no type change.** Introduce `call_spec` as a locale over the *current*
   single-`'a` types. Re-express the call-behaviour premises of
   `side_cfg_T_eff_cmp_collect_ctx_sound_semantic` as its assumptions; interpret it with the
   certified fixed combine. Proves the interface shape works with zero soundness risk.
   **Implementation-ready design in §6.**
2. **Stage 1 — split the state type behind an isomorphism.** Define `split_state` and prove it
   isomorphic to `vname => 'a` under `is_global` (`loc`/`glb` ↔ `restrict_local`/`restrict_global`).
   Keep `'l = 'g = 'a`. No behavioural change; establishes the projection/injection calculus.
3. **Stage 2 — thread the split through the tree + transfer, still `'l = 'g = 'a`.** Give
   `strategy_tree`/`effectful_domain_transfer` the split value, ported via the Stage-1 iso. All
   existing theorems recover by transport. This isolates the invasive plumbing change from the
   lattice generalization.
4. **Stage 3 — generalize `'l ≠ 'g`.** Relax the two type variables to independent
   `abstract_domain` instances; re-discharge the two-gamma soundness premises. `call_spec.combine`
   becomes `'l => 'g => 'l`.
5. **Stage 4 — witness.** A demo analysis with genuinely different local and global domains
   (e.g. interval locals, a small finite global lattice) exercised end-to-end via CMP.

**Explicit non-goals for that work:** full Goblint manager/query support, cross-analysis context
queries, and re-proving CTX/CMP equivalence. Stage 0 is the recommended first commit; it delivers
the first-class combine contract with no type surgery and no soundness reproof.

---

## 6. Stage 0, implementation-ready: a first-class `call_spec` call contract

This section refines Stage 0 into a design that can be transcribed to a theory directly. It
stays over the **current single-`'a` state** (`'a abs_state = vname => 'a`) and changes **no**
`abs_state`, `strategy_tree`, equation-system value type, or solver interface. The new artifact
is a small **locale hierarchy** — `call_spec`, `global_routing_spec`,
`trace_context_compatibility`, composed in `goblint_analysis_spec` — plus one soundness
corollary; the existing `Exec_Sign_Cmp_*` spine becomes its first interpretation.

> **Revision note (interface critique incorporated).** An earlier draft used a constant
> `enter :: 'a abs_state`, an under-specified `combine`, an `assign_ret` placeholder, and folded
> `dg`/`gcmp` into one `call_spec`. Auditing the actual generator confirmed: (1) the seeded
> generator uses **context-dependent** `frame_seed :: 'c => 'a abs_state`
> (`Exec_Cmp_Bridge.thy:55,83`), so `enter` must be `enter_seed :: 'c => 'a abs_state`;
> (2) `combines g :: (pp × pp × pp) set` (`IMP2_Proc_to_CFG.thy:131`) carries **no destination
> lval**, so `assign_ret` has no referent and is dropped, not stubbed; (3) `dg :: store list => 'c`
> is a collecting-semantics proof device, not executable call behaviour, so it moves to its own
> `trace_context_compatibility`; (4) `gcmp` drives the keyed read `side_env_cmp`, i.e. global
> routing, so it moves to `global_routing_spec`.

### 6.1 Decomposition and premise ownership

The ten premises of `side_cfg_T_eff_cmp_collect_ctx_sound_semantic`
(`TD_Side_Eff_Cmp_Sound.thy:324`) split cleanly across four concerns. Each locale owns exactly
one concern; the composed soundness theorem consumes all four.

| Premise | Owning locale | Why |
|---|---|---|
| `ENTRY`, `EDGE` | `sound_effectful_transfer` (transfer) | per-edge transfer soundness |
| `PROC_ENTRY` | `call_spec` (`enter_seed`) + framed transfer | context-keyed callee-entry frame bound |
| `LOCAL_POST` | generator post-solution | local slot monotone through combine — structural |
| `CMP_SOUND` | `call_spec` (`combine`) + `global_routing_spec` (`gkey`,`gcmp`) | merge over-approximation read through the keyed slots |
| `ENTER_MONO` | `call_spec` (context selection) + `global_routing_spec` (read) | selected context compatible with `entdg` |
| `DG_INTRA`, `DG_RETURN`, `DG_CALLEE` | **`trace_context_compatibility`** (`dg`) | digest stability — proof infrastructure, not runtime config |

### 6.2 The interface (single-`'a`, implementation-ready)

Four locales. `call_spec` and `global_routing_spec` are **executable analysis configuration**;
`trace_context_compatibility` is **proof-only**. All types are current; nothing mentions `'l`/`'g`.

```isabelle
(* --- executable call configuration: entry frame + caller/callee merge --- *)
locale call_spec = context_domain +
  fixes enter_seed :: "'c => 'a::sound_domain abs_state"     (* context-keyed callee-entry frame *)
    and combine    :: "'a abs_state => 'a abs_state => 'a abs_state"
  assumes
    (* enter: the transfer's enter edge is bounded by the context frame joined with globals
       (= sound_effectful_transfer_framed.etf_enter_framed_le, fresh_frame := enter_seed c) *)
    enter_framed:
      "\<And>etf c u \<sigma>. sound_effectful_transfer etf
         \<Longrightarrow> inr_slot_locals_bot \<sigma> \<Longrightarrow> inl_slot_globals_bot \<sigma>
         \<Longrightarrow> etf_full (etf_enter etf u) \<sigma> \<le> enter_seed c \<squnion> glob_env \<sigma>"
  and (* merge: caller-sound s and callee-sound t recombine soundly (= combine_states_sound) *)
    combine_sound:
      "\<And>\<sigma>c \<sigma>e s t. s \<in> \<lbrakk>\<sigma>c\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>e\<rbrakk> \<Longrightarrow> <s|t> \<in> \<lbrakk>combine \<sigma>c \<sigma>e\<rbrakk>"

(* --- executable global-store routing: which keyed slot a context writes / reads --- *)
locale global_routing_spec =
  fixes gkey :: "'c => 'g::finite"                           (* context -> global write key *)
    and gcmp :: "'c => 'g => bool"                           (* which keyed slots a context reads *)

(* --- proof-only: the trace digest and its stability laws (no runtime role) --- *)
locale trace_context_compatibility =
  fixes dg  :: "store list => 'c"                            (* context of a concrete run *)
    and cmp :: "'c => 'c => bool"
    and entdg :: "store => 'c"
  assumes
    dg_intra:  "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
  and dg_return: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
  and dg_callee: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau)
                     \<Longrightarrow> dg rho = entdg (last tau)"

(* --- the analysis specification: everything an analysis supplies to configure a run --- *)
locale goblint_analysis_spec = abstract_domain + call_spec + global_routing_spec +
  assumes
    (* selected context is entdg-compatible — exactly ENTER_MONO, via route/ctx_sel + the keyed read *)
    enter_mono:
      "\<And>sigma ctx cl s. s \<in> \<lbrakk>side_env_cmp gcmp sigma (cl, ctx)\<rbrakk>
         \<Longrightarrow> cmp (entdg s) (route cl ctx (route_read_cmp sigma (cl, ctx)))"
```

`route = context_domain.route` (`Context_Domain.thy:40`); `<_|_>`, `enter_state`, `glob_env`,
`side_env_cmp`, `route_read_cmp`, `inr_slot_locals_bot`, `inl_slot_globals_bot`, `etf_full` are
existing constants — no new primitives. `enter_mono` sits in `goblint_analysis_spec` (not
`call_spec`) because it couples context selection (`route`/`ctx_sel`) to the keyed read
(`side_env_cmp gcmp`), i.e. it spans call semantics *and* routing.

**Why `combine` stays value-level `'a abs_state => 'a abs_state => 'a abs_state`.** Audit of the
three consumers: the builder `cmb :: 'c => pp => pp => strategy_tree` (`TD_Side_Eff_Cmp_Gen.thy:53`)
takes `(context, caller-pp, callee-exit-pp)` and produces a *routing* tree; `etf_combine :: pp => pp
=> strategy_tree` (`Constraint_System.thy:435`) denotes the **site- and context-free** merge
`<s|t>` (`combine_states`, `IMP2_Globals.thy:28`); `combines g` carries no destination. So the
site/context/routing dependence lives in the *builder* and in `ctx_sel` (which derives the callee
context, `route cc ctx a = ctx_sel cc ctx (prep cc a)`), **not** in the merge. The weakest
sufficient value-level merge is therefore two states in, one out. Its extension arguments —
caller context, callee context (both already handled by `ctx_sel`), and a return lval (once the
CFG has one) — are deliberately **not** added now.

**Honest caveat on `combine`.** In the current spine the merge is *fixed* to `combine_abs`
(locals-from-caller, globals-from-callee); only the routing builder varies per analysis. So
`combine` is a genuine contract field — it is exactly the Goblint-`combine` override point and it
*is* consumed by `combine_sound`/`CMP_SOUND` — but today its only sound instance is `combine_abs`.
It is kept (unlike `assign_ret`) because `combine_abs` is a real, referenced operation, whereas a
return write-back has no referent in this language yet.

### 6.3 Field-by-field mapping

| Field | Locale | Current source | Semantic law | Proof step requiring it | Category |
|---|---|---|---|---|---|
| `start_context`, `ctx_sel`, `cmp`, `prep`, `entdg` | `context_domain` (`Context_Domain.thy:32-37`) | existing | `route` collapse (`route_def`) | interpret step, premises 4/8 | call semantics |
| `enter_seed :: 'c => 'a abs_state` | `call_spec` | `frame_seed` (`Exec_Cmp_Bridge.thy:55,83`); const `fresh_frame_sign` (`Sign_Side_Soundness.thy:103`) is the unit-context case | `enter_framed` | `PROC_ENTRY`; `etf_enter_framed_le` (`Constraint_System.thy:~785`) | call semantics (frame); `etf_enter` edge stays **transfer semantics** |
| `combine :: state => state => state` | `call_spec` | `combine_abs` (`Constraint_System.thy:273`) — merge is *fixed*, only routing varies | `combine_sound` (= `combine_states_sound`) | `CMP_SOUND` via `combine_read_cmp_le`/`combine_case_cmp_sound` (`TD_Side_Eff_Cmp_Sound.thy:63-72`) | call semantics; builder `cmb` is **generator config**; `etf_combine` is **transfer semantics** |
| `gkey :: 'c => 'g` | `global_routing_spec` | per-instance (unit / keyed) | routing commute `traverse_intra_cmp` (`TD_Side_Eff_Cmp_Gen.thy`) | `side_cfg_T_eff_cmp` `map_gtree` routing | generator config / routing |
| `gcmp :: 'c => 'g => bool` | `global_routing_spec` | singleton collapse (`Global_Cmp_Read.thy:50,77`) | `side_env_cmp_singleton` | `CMP_SOUND` keyed read | global-store routing |
| `dg :: store list => 'c` | `trace_context_compatibility` | per-instance `head_digest f` (`TD_Side_Eff_Cmp_Sound.thy:398`) | `dg_intra/return/callee` | `DG_INTRA/RETURN/CALLEE` | **proof infrastructure** (not runtime) |
| *(dropped)* `assign_ret` | — | no destination lval in `combines g` (`IMP2_Proc_to_CFG.thy:131`) | — | none | deferred until the CFG carries return destinations |

### 6.4 Exact soundness assumptions and the composed corollary

`goblint_analysis_spec` (= `abstract_domain` + `call_spec` + `global_routing_spec` + `enter_mono`)
composed with `trace_context_compatibility` and `sound_effectful_transfer etf` (+ the generator
post-solution hypothesis) discharge all ten premises:

- `call_spec.enter_framed`  ⟹ `PROC_ENTRY` (generator frame seed `= enter_seed c`).
- `call_spec.combine_sound` + `global_routing_spec.gcmp` singleton ⟹ `CMP_SOUND` (via `combine_read_cmp_le`).
- `goblint_analysis_spec.enter_mono` ⟹ `ENTER_MONO`.
- `trace_context_compatibility.dg_*` ⟹ `DG_INTRA/RETURN/CALLEE` (for a `head_digest`, already
  proved generically at `TD_Side_Eff_Cmp_Sound.thy:401-409`).
- `ENTRY`, `EDGE`, `LOCAL_POST` come from `sound_effectful_transfer` + the generator structure,
  unchanged.

Delivered corollary (the one new theorem), stated in the composition:

```isabelle
theorem (in goblint_analysis_spec) cmp_generator_sound:
  assumes "sound_effectful_transfer etf"
    and   "trace_context_compatibility dg cmp entdg"
    and   "part_post_solution
             (side_cfg_T_eff_cmp gkey cmb_fixed g etf (enter_seed ctx0) bot0 s0) x sigma vars"
    and   "single-key compat for gcmp"           (* side_env_cmp_singleton hypothesis *)
  shows   "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
```

where `cmb_fixed c cc ex = map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w,c)) (etf_combine etf cc ex))`
is the certified builder whose obligation is already proved by
`fixed_combine_satisfies_switching_combine_sound` (`TD_Side_Eff_Cmp_Gen.thy:912`).
(The seeded generator applies `enter_seed c` per frame-entry context, `Exec_Cmp_Bridge.thy:83`.)

### 6.5 CMP instance mapping (Sign, unit-global)

The current sign spine becomes interpretations of the three configuration/proof locales:

```isabelle
interpretation Sign: goblint_analysis_spec
  (* context_domain *)
  start_context = enter_sign cinit    prep = (\<lambda>_. id)
  ctx_sel = (\<lambda>cc ctx a. ctx)          entdg = sign_of_global   cmp = (=)
  (* call_spec *)
  enter_seed = (\<lambda>_. fresh_frame_sign) (* unit context: constant is the degenerate case *)
  combine    = combine_abs
  (* global_routing_spec *)
  gkey = (\<lambda>_. ())                      gcmp = (\<lambda>_ _. True)   (* keyed sign: non-trivial *)
  <proof: enter_framed = sign_etf_unit_framed; combine_sound = combine_states_sound;
          enter_mono = the existing sign enter-mono obligation>

interpretation SignDg: trace_context_compatibility
  dg = head_digest sign_of_global   cmp = (=)   entdg = sign_of_global
  <proof: dg_intra/return/callee = generic head_digest_DG_* lemmas>
```

`enter_framed` is `sign_etf_unit_framed` (`Sign_Side_Soundness.thy:119`); `combine_sound` is
`combine_states_sound`; `dg_*` are the generic `head_digest_DG_*` lemmas; `enter_mono` is the sole
per-instance value-dependent obligation the sign proof already discharges. The keyed sign instance
(`Exec_Sign_Cmp_Keyed_*`) is the same with non-trivial `gkey`/`gcmp` and a genuinely
context-dependent `enter_seed`.

### 6.6 What stays hard-coded vs. what becomes a wrapper

- **Stays hard-coded (Stage 0):** `combine_abs`, `combine_states` (`<_|_>`), `enter_state`,
  `restrict_local`, `restrict_global`, `glob_env`, `side_env_cmp`, and the generator
  `side_cfg_T_eff_cmp`. These are the *semantic reference* and *state-partition plumbing*; the
  locales reference them in laws but do not replace them. They are the Stage-1 casualties, so
  leaving them untouched isolates Stage 0 from the type surgery. Note the merge `combine_abs` stays
  the *only* sound `combine` instance — the merge is not yet analysis-varied (only routing is).
- **Becomes a locale-derived wrapper:** the generator's frame-seed argument
  (`frame_seed` ↦ `call_spec.enter_seed`), the combine builder (`cmb` ↦ `cmb_fixed` from
  `combine` + `gkey` + `etf_combine`), and the digest (`head_digest …` ↦
  `trace_context_compatibility.dg`). Instances stop passing these positionally and instead
  interpret the locales.

### 6.7 Stage-0 implementation sequence (do not implement yet)

1. Add `Call_Spec.thy` importing `TD_Side_Eff_Cmp_Sound` + `Context_Domain`; define the three
   configuration/proof locales and `goblint_analysis_spec` of §6.2. No proofs beyond the
   declarations.
2. Prove `cmp_generator_sound` (§6.4) in `goblint_analysis_spec` by feeding the four locales'
   assumptions into `side_cfg_T_eff_cmp_collect_ctx_sound_semantic`. All premises already have
   named discharges; this is assembly, not new mathematics.
3. Add the `head_digest` convenience lemma so a `trace_context_compatibility` instance follows from
   supplying only `entdg` (reuse `TD_Side_Eff_Cmp_Sound.thy:401-409`).
4. Interpret the locales for the unit-global sign spine (§6.5); re-derive the existing sign
   soundness endpoint as `Sign.cmp_generator_sound`. Keep the old theorem as a one-line alias so
   nothing downstream breaks.
5. Interpret for the keyed sign and the interval spine; retire the positional generator calls in
   favour of the interpretations.

Each step is independently green-buildable. Steps 1–3 touch only new files; steps 4–5 add
interpretations without editing the generator or solver.

### 6.8 Expected proof impact (Stage 0)

- **New theory `Call_Spec.thy`:** three small locales (`call_spec`, `global_routing_spec`,
  `trace_context_compatibility`) + `goblint_analysis_spec` + 1 assembled theorem + 1 head-digest
  lemma. Low risk — the theorem is a re-packaging of an existing proof.
- **`sound_effectful_transfer` / `..._framed`:** unchanged; `call_spec.enter_framed` is stated to
  match `etf_enter_framed_le` (with `fresh_frame := enter_seed c`) so existing interpretations feed
  it directly.
- **Instance files (`Sign_Side_Soundness`, `Exec_Sign_Cmp_*`, interval):** add locale
  `interpretation`s and an alias per endpoint. No proof reopened; risk is name-plumbing only.
- **No change** to `abs_state`, `strategy_tree`, `effectful_domain_transfer`, `side_cfg_T_eff_cmp`,
  `side_env_cmp`, or any solver theory. This is the defining constraint of Stage 0 and is
  satisfied because `call_spec` only *consumes* those types.

### 6.9 Blockers before Stage 1 (local/global separation)

1. **`combine`'s type conflates the two regions.** `combine :: 'a abs_state => 'a abs_state => 'a abs_state`
   takes caller and callee as the *same* type. Stage 1 needs `combine :: 'a abs_state => 'g_state => 'a abs_state`
   (callee contributes only globals). The Stage-0 field is deliberately single-`'a`; the signature
   change is the first Stage-1 edit and cannot be hidden behind the locale.
2. **`enter_seed :: 'c => 'a abs_state` returns a whole-state frame.** Its `is_global`-partitioned
   meaning (`fresh_frame_sign` sets locals to `STop`, globals to `⊥`) is baked into `restrict_*`.
   Stage 1 must re-type its codomain to a local frame `'a abs_state_local`; the `'c =>` shape is
   Stage-1-stable, only the codomain splits.
3. **`combine_sound` references `<s|t>` and `⟦_⟧`.** Both are single-store / single-gamma. Stage 1
   replaces them with a split combine and two gammas; the `call_spec` law must be re-stated, so
   `call_spec` is *not* Stage-1-stable — it is the seam where the split lands. `global_routing_spec`
   and `trace_context_compatibility` are comparatively stable (routing keys and digests are already
   region-agnostic).
4. **`gcmp`/`side_env_cmp` read a single-`'a` slot.** The singleton collapse
   (`Global_Cmp_Read.thy:50`) assumes global values live in the same `'a`; a distinct global
   lattice changes the read type in `global_routing_spec`.

Net: Stage 0 gives a genuine analysis-provided call contract and a single composed soundness
corollary without touching the value types; Stage 1 begins precisely by re-typing
`call_spec.combine` and `call_spec.enter_seed`'s codomain — which is why the decomposition (call
semantics vs. routing vs. proof-only) matters: it localises the Stage-1 churn to `call_spec`.

### 6.10 Stage-0 implementation deviations (2026-07-12)

Implementing §6 surfaced four points where code evidence overrides the design sketch. These are
authoritative for `Call_Spec.thy`.

1. **The composed corollary already exists — Stage 0 wraps it, not the base theorem.**
   `context_domain.collect_ctx_sound_route` (`TD_Side_Eff_Cmp_Sound.thy`) already restates
   `side_cfg_T_eff_cmp_collect_ctx_sound_semantic` with `rt = route` and the locale's `entdg`/`cmp`,
   taking `ENTRY/PROC_ENTRY/EDGE/LOCAL_POST/CMP_SOUND/DG_*/ENTER_MONO` as premises. Stage 0's
   `cmp_generator_sound` is a thin wrapper that supplies `DG_*` from `trace_context_compatibility`.

2. **`ENTER_MONO`/`enter_mono` is candidate-solution-specific → theorem-level premise, not a locale
   assumption.** It mentions the candidate solution `sigma` (`s \<in> \<lbrakk>side_env_cmp gcmp sigma …\<rbrakk>`)
   and is *provably not always dischargeable* — `Example_Finite_Sign_Context_Analysis` shows the
   shared-context sign case where it (there called `n`) is unprovable, becoming provable only with
   keyed globals. Per the Stage-0 rule "keep candidate-solution premises out of reusable locales",
   it is a hypothesis of the soundness corollary, **not** an assumption of `goblint_analysis_spec`.
   (§6.2's placement of `enter_mono` in `goblint_analysis_spec` is superseded by this.)

3. **`enter_framed` is not a `call_spec` assumption.** `etf` is deliberately not a spec-locale
   parameter, and the enter bound is transfer-specific (`sound_effectful_transfer_framed`, e.g.
   `sign_etf_unit_framed`). `call_spec` carries only the sigma-/etf-free `combine_sound`; the enter
   bound is discharged at the transfer layer when a run discharges `PROC_ENTRY`. `enter_seed`
   remains a config field with no locale law (like `start_context`).

4. **`abstract_domain` is a type class, not a locale.** `goblint_analysis_spec` cannot
   `abstract_domain +`; the constraint rides the type variable (`'a::sound_domain`, the class the
   soundness theorem actually needs). Composition is `goblint_analysis_spec = call_spec +
   global_routing_spec`.

Resulting shapes (as built):

```isabelle
locale call_spec = context_domain +
  fixes enter_seed :: "'c => 'a::sound_domain abs_state"
    and combine    :: "'a abs_state => 'a abs_state => 'a abs_state"
  assumes combine_sound:
    "\<And>sc se s t. s \<in> \<lbrakk>sc\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>se\<rbrakk> \<Longrightarrow> <s|t> \<in> \<lbrakk>combine sc se\<rbrakk>"

locale global_routing_spec =
  fixes gkey :: "'c => 'g::finite" and gcmp :: "'c => 'g => bool"

locale trace_context_compatibility =
  fixes dg :: "store list => 'c" and cmp :: "'c => 'c => bool" and entdg :: "store => 'c"
  assumes dg_intra … and dg_return … and dg_callee …

locale goblint_analysis_spec = call_spec + global_routing_spec

(* soundness assembly *)
locale cmp_generator_soundness = goblint_analysis_spec + trace_context_compatibility
begin
theorem cmp_generator_sound:
  assumes ENTRY … PROC_ENTRY … EDGE … LOCAL_POST … CMP_SOUND … ENTER_MONO …   (* all sigma-dependent *)
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
  by (rule collect_ctx_sound_route[OF ENTRY PROC_ENTRY EDGE LOCAL_POST CMP_SOUND
                                       dg_intra dg_return dg_callee ENTER_MONO])
end
```

---

## Appendix — audited symbols and locations

| Symbol | Location |
|---|---|
| `store`, `is_global` | `IMP2_Syntax.thy:26`, `IMP2_Globals.thy:24` |
| `'a abs_state`, `gamma_state` | `Abstract_Domain.thy:23`, `Abstract_Domain.thy` |
| `sound_domain`, `abstract_domain` | `Abstract_Domain.thy:46`, `:148` |
| `effectful_domain_transfer`, `apply_etf` | `Constraint_System.thy:435`, `:443` |
| `combine_abs`, `combine_states_sound` | `Constraint_System.thy:273` |
| `sound_effectful_transfer` (+ `_framed`, `_framed_le`) | `Constraint_System.thy:748` |
| `restrict_local` / `restrict_global`, `side_env` | `TD_Side_CFG.thy:25,29,93` |
| `strategy_tree`, `seqcomp_tree` | `TD_Side_CFG.thy`, `Strategy_Tree_Monad.thy` |
| `side_cfg_T_eff_cmp`, `side_acc_ctx`, `pull_gk` | `TD_Side_Eff_Cmp_Gen.thy:53`, `TD_Side_Tree.thy:372` |
| `switching_combine_sound` (+ `_le`, fixed-combine discharge) | `TD_Side_Eff_Cmp_Gen.thy:890,912,926` |
| `restrict_local_st` / `restrict_global_st` / `combine_abs_st` | `Exec_St.thy:521,525,531` |
| `switching_combine_st`, `kgen_combine_rread`, `side_env_cmp` | `Exec_Cmp_Bridge.thy:219`, `Exec_Sign_Cmp_RRead_Split.thy:111`, `Global_Cmp_Read.thy:70` |
