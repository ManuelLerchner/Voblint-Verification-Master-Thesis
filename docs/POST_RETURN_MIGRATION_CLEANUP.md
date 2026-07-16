# Post-return-migration cleanup backlog

Written after the parameter-passing / return-value migration (`EA_Enter xs es`,
4-tuple `combines`, `combine_collect dst s t = combine_assign dst (t ret_var)
(combine_states s t)`) landed and both `Voblint_Analysis` and
`Voblint_Formalization` compiled green. The migration exposed structural
duplication that predates it but was multiplied by it. Nothing here is a
correctness gap — every item is a length / complexity / maintainability
reduction.

A future agent should treat each item as an independent refactor: verify the
claim against the cited `file:line`, make the change behind a green
`isabelle build`, and delete the corresponding entry here.

---

## Landed

Items 1, 4, 5, 6, 7, 8 landed, each behind a green
`isabelle build ... Voblint_Formalization`:

* **1 — combine bridge lemmas.** `combine_collect_None`
  (`CFG_Collect.thy`) and `combine_collect_abs_None` (`Constraint_System.thy`)
  name the definitional equality `<s|t> = combine_collect None s t`; the three
  inline re-derivations in `Example_Trace_Digest_Combine` route through it.
  `combine_states` / `combine_abs` stay — they are the env-combine primitive
  under the operational semantics and the base of `combine_collect`, not a
  redundant second operator. (The original "retire `combine_states`" framing
  over-scoped this.)
* **4 — `combine_abs_bound_sound` centralized.** Moved to its natural home next
  to `combine_collect_sound` in `Constraint_System`; the dead duplicate
  `seeded_activation_comb` deleted; the two live COMB discharges in
  `seeded_activation_collecting_sound` routed through it. (Independent of item 1:
  the inlines already used the unified `combine_collect_sound`; the `OF`
  ambiguity came from `gamma_state_mono`, not a dual combine. The DG
  unit/indep cases use base `combine_collect_sound` for *exact* membership — no
  bound weakening — so they are not instances of `combine_abs_bound_sound`.)
* **5 — `bind_formals` API.** Deleted the duplicate `bind_formals_notin`
  (= `bind_formals_nonformal` in `IMP2_Proc`); added the concrete
  `bind_formals_global` next to its abstract sibling `bind_formals_abs_global`
  in `Constraint_System`; routed the cover-seed global branch through it.
* **6 — shared `sound_effectful_transfer` skeleton.** `route_family_etf_sound`
  factors the identical six-obligation proof; `flag_etf_sound` and
  `named_etf_sound` are single `rule` applications (file: -75 / +64 lines).
* **7 — `dg_combine_trees`.** An abbreviation for the repeated
  `map (\<lambda>(cc, ex, dst). dg_cmb_of S () dst cc ex) (combine_predecessor_list g v)`
  across the eq / sides / dep commutation goals in `Exec_DG_Bridge`. Being an
  abbreviation, the underlying terms — and the commute proofs — are unchanged.
* **8 — named `sound_dg_spec` combine corollaries.** `gamma_dg_combine_sound` /
  `gamma_unit_combine_sound` replace the positional
  `subgoal premises prems for s dc g t de dst` binders in `DG_Soundness`.

---

## Deferred: 2 + 3 (trace-backbone unification) — verified not a sound cleanup

On inspection these two items, as written, are **not** length/complexity
reductions; they would either regress the architecture or require a large,
high-risk re-architecture of heavily-used inductive predicates. Recorded here so
the finding is not re-litigated.

### 2. Make `activation_trace_sound` an instance of `trace_ctx_sound_meaning`

**Verified against the source, the claim does not hold.** The backbone
`trace_ctx_sound_meaning` (`Ctx_Collect_Backbone.thy`) inducts over **plain
`trace_witness`** and carries context *externally* through a whole-trace digest
(`dg` / `cmp`) plus routing (`rt`), which is exactly why it needs the three
digest obligations `DG_INTRA` / `DG_RETURN` / `DG_CALLEE`.

`activation_trace_sound` (`Seeded_Activation_Sound.thy:41`) inducts over
`trace_witness_act`, which threads the call context **structurally** in the
trace. Its own docstring states the point: *"the soundness backbone needs no
digest-propagation machinery … the context is structural, not a whole-trace
filter. This is strictly simpler than the digest-filtered kernel."* It is a
clean ~20-line, five-obligation induction.

Folding it onto the backbone would force it to *supply* `DG_INTRA` /
`DG_RETURN` / `DG_CALLEE` (recovering the structural context as a digest filter)
and couple a deliberately digest-free proof to the heavier machinery — a net
complexity **increase**. The two are a specialization and a generalization that
legitimately coexist, not duplicates.

### 3. Unify `trace_witness` / `trace_witness_act` (and `_d` / `_ctx`)

The four inductive predicates (`trace_witness`, `trace_witness_d`,
`trace_witness_ctx`, `trace_witness_act`) are structurally parallel but carry
**different information**: `_act` threads a call context `'c` and forgets to
`trace_witness` (`trace_witness_act_imp_trace_witness`); `_d` / `_ctx` carry the
digest / context refinements. None is dead code (≈120 / 73 / 15 / 51 references;
259 total across CFG + Analysis + Examples). One sub-claim is inaccurate:
`trace_witness_act` has **no** `_nonempty` lemma to be "copy-pasted".

Collapsing them onto one context-algebra-parameterized predicate would require
re-deriving every `.induct` / `.intros` / `_imp` / `_edges` / `_combineI` /
`_last_in_cfg_collect` / soundness lemma and every consumer — and the backbone
depends on `trace_witness.induct`, so that rule would have to be re-derived
through the general predicate. This is a research-grade re-architecture, not an
incremental cleanup, and its payoff is uncertain because the predicates are not
naive clones. Deferred pending a dedicated, separately-reviewed effort.
