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
`abs_state`, `strategy_tree`, equation-system value type, or solver interface. The only new
artifact is one locale plus one soundness corollary; the existing `Exec_Sign_Cmp_*` spine
becomes its first interpretation.

### 6.1 What `call_spec` owns — and what it deliberately does not

`call_spec` packages exactly the **call-behaviour contract**: the pieces that decide how an
activation enters, how caller and callee recombine, how a context is selected, and how globals
are keyed. It does *not* absorb the per-edge transfer (`effectful_domain_transfer`), the
generator `side_cfg_T_eff_cmp`, or the solver — those remain separate and unchanged. The
generic soundness theorem `side_cfg_T_eff_cmp_collect_ctx_sound_semantic`
(`TD_Side_Eff_Cmp_Sound.thy:324`) already has ten premises; `call_spec`'s job is to own the
subset that is call behaviour and prove them once, leaving the transfer/generator subset with
`sound_effectful_transfer` where it already lives.

Premise ownership (from the theorem head at `TD_Side_Eff_Cmp_Sound.thy:324`):

| Premise | Owner | Why |
|---|---|---|
| `ENTRY`, `EDGE` | `sound_effectful_transfer` + generator | per-edge transfer soundness, not call behaviour |
| `PROC_ENTRY` | `call_spec` (enter) + framed transfer | callee-entry frame bound |
| `LOCAL_POST` | generator post-solution | local slot monotone through combine — structural |
| `CMP_SOUND` | **`call_spec` (combine)** | the global-half combine over-approximation |
| `DG_INTRA`, `DG_RETURN`, `DG_CALLEE` | **`call_spec` (context/digest)** | digest stability laws |
| `ENTER_MONO` | **`call_spec` (context selection)** | selected context compatible with `entdg` |

### 6.2 The interface (single-`'a`, implementation-ready)

`call_spec` extends the existing `context_domain` (`Context_Domain.thy:32`) — reusing
`start_context`, `ctx_sel`, `entdg`, `cmp`, `prep` verbatim — and adds the routing keys and the
abstract call operations. All types are current; nothing below mentions `'l`/`'g` split.

```isabelle
locale call_spec = context_domain +
  (* --- global-slot routing (generator configuration) --- *)
  fixes gkey :: "'c => 'g::finite"                         (* context -> global key *)
    and gcmp :: "'c => 'g => bool"                         (* context/key compatibility *)
  (* --- abstract call operations, over the current single-'a state --- *)
    and enter      :: "'a::sound_domain abs_state"          (* callee-entry frame seed *)
    and combine    :: "'a abs_state => 'a abs_state => 'a abs_state"
    and assign_ret :: "'a abs_state => 'a abs_state"        (* return write-back; today id *)
    and dg         :: "store list => 'c"                    (* trace digest = context of a run *)
  assumes
    (* enter: the transfer's enter edge is bounded by the frame joined with globals
       (= sound_effectful_transfer_framed.etf_enter_framed_le, with fresh_frame := enter) *)
    enter_framed:
      "\<And>etf u \<sigma>. sound_effectful_transfer etf
         \<Longrightarrow> inr_slot_locals_bot \<sigma> \<Longrightarrow> inl_slot_globals_bot \<sigma>
         \<Longrightarrow> etf_full (etf_enter etf u) \<sigma> \<le> enter \<squnion> glob_env \<sigma>"
  and (* combine: caller-sound s and callee-sound t recombine soundly
         (= combine_states_sound, specialised to combine) *)
    combine_sound:
      "\<And>\<sigma>c \<sigma>e s t. s \<in> \<lbrakk>\<sigma>c\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>e\<rbrakk> \<Longrightarrow> <s|t> \<in> \<lbrakk>combine \<sigma>c \<sigma>e\<rbrakk>"
  and (* return write-back is sound (today assign_ret = id, trivially) *)
    assign_ret_sound: "\<And>\<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>assign_ret \<sigma>\<rbrakk>"
  and (* digest laws — exactly DG_INTRA / DG_RETURN / DG_CALLEE *)
    dg_intra:  "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
  and dg_return: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
  and dg_callee: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau)
                     \<Longrightarrow> dg rho = entdg (last tau)"
  and (* selected context is entdg-compatible — exactly ENTER_MONO, via route/ctx_sel *)
    enter_mono:
      "\<And>sigma ctx cl s. s \<in> \<lbrakk>side_env_cmp gcmp sigma (cl, ctx)\<rbrakk>
         \<Longrightarrow> cmp (entdg s) (route cl ctx (route_read_cmp sigma (cl, ctx)))"
```

`route` is the existing `context_domain.route` (`Context_Domain.thy:40`); `<_|_>`,
`enter_state`, `glob_env`, `side_env_cmp`, `route_read_cmp`, `inr_slot_locals_bot`,
`inl_slot_globals_bot`, `etf_full` are all existing constants — no new primitives.

### 6.3 Field-by-field mapping

| `call_spec` field | Current source | Semantic law | Theorem / proof step requiring it | Category |
|---|---|---|---|---|
| `start_context`, `ctx_sel`, `cmp`, `prep` | `context_domain` (`Context_Domain.thy:32-37`) | `route` collapse (`route_def`) | interpret step for premise 4/8 in `…sound_semantic` proof | call semantics |
| `entdg` | `context_domain` (`:36`) | `dg_callee`, `enter_mono` | `DG_CALLEE`, `ENTER_MONO` | call semantics |
| `dg` | per-instance `head_digest f` (`TD_Side_Eff_Cmp_Sound.thy:398`) | `dg_intra/return/callee` | `DG_INTRA/RETURN/CALLEE` | call semantics |
| `enter` | `fresh_frame_sign` (`Sign_Side_Soundness.thy:103`) | `enter_framed` | `PROC_ENTRY`; `sound_effectful_transfer_framed.etf_enter_framed_le` (`Constraint_System.thy:~785`) | call semantics (frame); the `etf_enter` edge stays **transfer semantics** |
| `combine` | `combine_abs` (`Constraint_System.thy:273`) | `combine_sound` (= `combine_states_sound`) | `CMP_SOUND` via `combine_read_cmp_le`/`combine_case_cmp_sound` (`TD_Side_Eff_Cmp_Sound.thy:63-72`) | call semantics; builder `cmb` is **generator config**; `etf_combine` is **transfer semantics** |
| `assign_ret` | `id` (implicit — no return value in IMP2) | `assign_ret_sound` (trivial) | none today; extension point for a real return value | call semantics |
| `gkey` | per-instance `'c => 'g` (unit / keyed) | routing commute `traverse_intra_cmp` (`TD_Side_Eff_Cmp_Gen.thy`) | `side_cfg_T_eff_cmp` `map_gtree` routing | generator config |
| `gcmp` | single-key compat (`Global_Cmp_Read.thy:50,77` singleton collapse) | `side_env_cmp_singleton` | `CMP_SOUND` read collapse | generator config ↔ call semantics bridge |

### 6.4 Exact soundness assumptions and the delivered corollary

`call_spec` + `sound_effectful_transfer etf` (+ the generator post-solution hypothesis) discharge
all ten premises of `side_cfg_T_eff_cmp_collect_ctx_sound_semantic`:

- `enter_framed`  ⟹ `PROC_ENTRY` (with the generator's frame seed `= enter`).
- `combine_sound` + `gcmp` singleton ⟹ `CMP_SOUND` (through `combine_read_cmp_le`).
- `dg_intra/return/callee` ⟹ `DG_INTRA/RETURN/CALLEE` (for a `head_digest`, already proved
  generically at `TD_Side_Eff_Cmp_Sound.thy:401-409`).
- `enter_mono` ⟹ `ENTER_MONO`.
- `ENTRY`, `EDGE`, `LOCAL_POST` come from `sound_effectful_transfer` + the generator structure,
  unchanged.

Delivered corollary (the one new theorem):

```isabelle
theorem (in call_spec) cmp_generator_sound:
  assumes "sound_effectful_transfer etf"
    and   "part_post_solution (side_cfg_T_eff_cmp gkey cmb_fixed g etf enter bot0 s0) x sigma vars"
    and   "single-key compat for gcmp"           (* side_env_cmp_singleton hypothesis *)
  shows   "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
```

where `cmb_fixed c cc ex = map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w,c)) (etf_combine etf cc ex))`
is the certified builder whose obligation is already proved by
`fixed_combine_satisfies_switching_combine_sound` (`TD_Side_Eff_Cmp_Gen.thy:912`).

### 6.5 CMP instance mapping (Sign, unit-global)

The current sign spine (`Sign_Side_Soundness.thy`) becomes one interpretation:

```isabelle
interpretation Sign: call_spec
  start_context = enter_sign cinit          (* existing context policy *)
  prep          = (\<lambda>_. id)
  ctx_sel       = (\<lambda>cc ctx a. ctx)          (* unit-global: single context *)
  entdg         = (\<lambda>s. head_digest (sign o (\<lambda>x. s (SOME g. is_global g))) ...)  (* the sign-of-global digest, A7.3 *)
  cmp           = (=)                         (* or the existing sign cmp *)
  gkey          = (\<lambda>_. ())                    (* unit global slot *)
  gcmp          = (\<lambda>_ _. True)                (* join-all read; or singleton for keyed *)
  enter         = fresh_frame_sign            (* Sign_Side_Soundness.thy:103 *)
  combine       = combine_abs
  assign_ret    = id
  dg            = head_digest (...)           (* the existing head digest *)
```

Every assumption is already proved for these values: `enter_framed` is
`sign_etf_unit_framed` (`Sign_Side_Soundness.thy:119`); `combine_sound` is `combine_states_sound`;
`dg_*` are the generic `head_digest_DG_*` lemmas; `enter_mono` is the sole per-instance
value-dependent obligation the sign proof already discharges. The keyed sign instance
(`Exec_Sign_Cmp_Keyed_*`) is the same interpretation with `gkey`/`gcmp` non-trivial.

### 6.6 What stays hard-coded vs. what becomes a wrapper

- **Stays hard-coded (Stage 0):** `combine_abs`, `combine_states` (`<_|_>`), `enter_state`,
  `restrict_local`, `restrict_global`, `glob_env`, `side_env_cmp`, and the generator
  `side_cfg_T_eff_cmp`. These are the *semantic reference* and the *state-partition plumbing*;
  `call_spec` references them in its laws but does not replace them. They are exactly the
  Stage-1 casualties, so leaving them untouched isolates Stage 0 from the type surgery.
- **Becomes a `call_spec`-derived wrapper:** the generator's frame seed argument (`fresh_frame`
  ↦ `call_spec.enter`), the combine builder (`cmb` ↦ `cmb_fixed` built from `call_spec` +
  `etf_combine`), and the digest (`head_digest …` ↦ `call_spec.dg`). Instances stop passing
  these positionally and instead interpret `call_spec`.

### 6.7 Stage-0 implementation sequence (do not implement yet)

1. Add `Call_Spec.thy` importing `TD_Side_Eff_Cmp_Sound` + `Context_Domain`; define the locale of
   §6.2. No proofs beyond the locale declaration.
2. Prove `cmp_generator_sound` (§6.4) inside the locale by feeding the assumptions into
   `side_cfg_T_eff_cmp_collect_ctx_sound_semantic`. All premises already have named discharges;
   this is assembly, not new mathematics.
3. Add the `head_digest` convenience sublocale/lemma so instances supply only `entdg` and get
   `dg_intra/return/callee` for free (reuse `TD_Side_Eff_Cmp_Sound.thy:401-409`).
4. Interpret `call_spec` for the unit-global sign spine (§6.5); re-derive the existing sign
   soundness endpoint as `Sign.cmp_generator_sound`. Keep the old theorem as a one-line alias so
   nothing downstream breaks.
5. Interpret for the keyed sign and the interval spine; retire the positional generator calls in
   favour of the interpretations.

Each step is independently green-buildable. Steps 1–3 touch only new files; steps 4–5 add
interpretations without editing the generator or solver.

### 6.8 Expected proof impact (Stage 0)

- **New theory `Call_Spec.thy`:** ~1 locale + 1 assembled theorem + 1 head-digest sublocale.
  Low risk — the theorem is a re-packaging of an existing proof.
- **`sound_effectful_transfer` / `..._framed`:** unchanged; `call_spec.enter_framed` is stated to
  match `etf_enter_framed_le` so the existing interpretations feed it directly.
- **Instance files (`Sign_Side_Soundness`, `Exec_Sign_Cmp_*`, interval):** add an `interpretation`
  and an alias per endpoint. No proof reopened; risk is name-plumbing only.
- **No change** to `abs_state`, `strategy_tree`, `effectful_domain_transfer`, `side_cfg_T_eff_cmp`,
  `side_env_cmp`, or any solver theory. This is the defining constraint of Stage 0 and is
  satisfied because `call_spec` only *consumes* those types.

### 6.9 Blockers before Stage 1 (local/global separation)

1. **`combine`'s type conflates the two regions.** `combine :: 'a abs_state => 'a abs_state => 'a abs_state`
   takes caller and callee as the *same* type. Stage 1 needs `combine :: 'a abs_state => 'g_state => 'a abs_state`
   (callee contributes only globals). The Stage-0 field is deliberately single-`'a`; the signature
   change is the first Stage-1 edit and cannot be hidden behind the locale.
2. **`enter :: 'a abs_state` is a whole-state frame.** Its `is_global`-partitioned meaning
   (`fresh_frame_sign` sets locals to `STop`, globals to `⊥`) is baked into `restrict_*`. Stage 1
   must re-type it as a local frame `'a abs_state_local`.
3. **`combine_sound` references `<s|t>` and `⟦_⟧`.** Both are single-store / single-gamma. Stage 1
   replaces them with a split combine and two gammas; the `call_spec` law must be re-stated, so
   `call_spec` itself is *not* Stage-1-stable — it is the seam where the split lands.
4. **`gcmp`/`side_env_cmp` read a single-`'a` slot.** The singleton collapse
   (`Global_Cmp_Read.thy:50`) assumes global values live in the same `'a`; a distinct global
   lattice changes the read type.

Net: Stage 0 gives a genuine analysis-provided call contract and a single soundness corollary
without touching the value types; Stage 1 begins precisely by re-typing `call_spec.combine` and
`call_spec.enter`, which is why building `call_spec` first is the right forcing function.

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
