# Roadmap

**This file does not list issues, lemmas, or sorries.** Those drift. It points to the live sources of truth and records *stable* architectural directions.

---

## Source-of-truth pointers

| What you want | Where to look |
| --- | --- |
| Open work items, dependencies, status | **[GitHub Project 8](https://github.com/users/ManuelLerchner/projects/8)** |
| Active issues, labels, milestones | `gh issue list --state open` |
| Live sorry inventory | `rg -n '^\s*sorry' src/ \| rg -v '\.thy~'` |
| **Next session / week plan** | `docs/NEXT_STEPS.md` |
| All declared lemmas/theorems | `rg -n '^(lemma\|theorem) ' src/` |
| Soundness chain narrative | `docs/PROOF_OVERVIEW.md` |
| Proposed local-trace semantic refoundation | `docs/LTR_COLLECT_REFOUNDATION_PLAN.md` |
| Keyed context architecture | `docs/KEYED_CONTEXT_CONSOLIDATION.md` |
| Per-stage workflow | `docs/PROOF_OVERVIEW.md` (lemma spine) + `src/*/README.md` (per-layer) |
| Catalogued repo problems (P1–P10) by file:line | `docs/OPEN_PROBLEMS.md` |
| CFG representation decision | `docs/cfg-representation.md` |
| HOL-IMP differences | `docs/HOL_IMP_COMPARISON.md` |
| Comparison to Blazy/Pichardie/Verasco | KB: `~/git/goblint-formalization-kb/wiki/concepts/blazy-2013-value-analysis.md` and `wiki/concepts/verasco.md` |

---

## Label scheme (GitHub)

| Group | Labels | Meaning |
| --- | --- | --- |
| Phase | `phase:core` / `phase:stretch` / `phase:thesis` | Where the work lives in the proof-architecture phasing |
| Type | `type:proof` / `type:refactor` / `type:docs` / `type:code-gen` | Kind of work |
| Source | `source:blazy-2013` | Inspired by Blazy et al. SAS 2013 (arXiv:1304.3596) |

Filter examples:

```bash
gh issue list --state open --label phase:core
gh issue list --state open --label source:blazy-2013
gh issue list --state open --label phase:stretch --label type:proof
```

Dependency arrows live on the issues themselves (GitHub's native `blockedBy`/`blocking`). The Project 8 Roadmap view shows them when the *Dependencies* layer is on.

---

## Stable architectural directions

Issue numbers are deliberately omitted — they go stale. The directions remain even as individual issues open, close, or get renamed.

### Core soundness chain (done in code)

Collecting spec + post-fixpoint + TD side bridge (B3–B4 in `docs/OPEN_PROBLEMS.md`) are proved.
Sign pipeline is closed end-to-end (`proc_global_side_sign_analysis` / `side_sign_analysis_sound`)
modulo one named TD hypothesis (P1: `side_cfg_solve_dom_eff`).

### Semantics and pipeline (current)

- **Spec:** `cfg_collect` (IP state) and `cfg_collect_trace` (IP trace) at every program point; `cfg_runs_to` is exit-projected sugar.
- **Canonical soundness:** `trace_analysis_sound` (no termination premise); `reaching_global_read_sound` (per-variable read).
- **Mixed-flow theorem:** `mixed_flow_analysis_sound` / `mixed_flow_analysis_optimal` for effectful TD_side equation systems.
- **Exit corollary:** `side_sign_analysis_sound` (sign domain).
- **Operational:** `pstep` in `IMP2_Proc.thy`; `cfg_runs_to` in `CFG_Collect_Runs.thy`.
- **Showcase:** `Example_Trace_Digest_Precision.thy` — digest vs. flat precision comparison.
- **Keyed-global context precision:** `Example_Global_Ctx_Read_Precision.thy` (sound read-layer
  witness: global-derived contexts, filtered read `SZero`/`SPos` vs. join-all `SNonNeg`,
  contrasted with the unsound caller-local seeded split) and `Exec_Sign_Cmp_Keyed_DG_Run.thy`
  (current keyed DG witness: per-context global slots, `combine_sound`, `dg_gamma_c`, and
  `by eval` separation). Executable filtered read: `glob_env_cmp_code` in
  `Global_Cmp_Read.thy`. The former executable `_st` keyed generator has been retired; the
  remaining seeded-clean and keyed examples are direct DG witnesses. Full per-call-site
  `SZero`/`SPos` separation is carried by `Example_Finite_Sign_Context_Analysis.thy`, a
  first-class example with a finite context/key type `GZero | GPos | GNonNeg | GOther` computed
  from the sign value of global `G`: it proves the separated slots `by eval`
  (`fctx_slot_zero_precise` = `SZero`, `fctx_slot_pos_precise` = `SPos`, `fctx_join_all` =
  `SNonNeg`), plus the finite-key soundness-facing theorem `fctx_keyed_sound_if_post_fixpoint`.
  The precision hinges on filtering `EA_Enter` from the intra fold and seeding a framed fresh
  frame (see the framed-enter redesign below, `docs/KEYED_CONTEXT_ENTER_FRAMED_MIGRATION.md`).
  The remaining proof obligation is the value-dependent finite-context soundness theorem
  (concrete run → abstract post-fixpoint) / eventual `context_domain` locale. Batch-green, no
  sorry.
- **Generic keyed soundness core:** `TD_Side_Eff_Cmp_Pull.thy` — the reusable heart of a
  keyed generator. The masking pullback `pull_cmp` collapses the `cmp`-filtered slots into a
  monovariant view (`side_env_cmp_pull`), so `post_fixpoint_sound_at_cmp_pull` reduces keyed
  collecting soundness to the monovariant `post_fixpoint_sound_at_eff` for any program/domain;
  `cmp_edge_sound` / `cmp_entry_sound` discharge the `EDGE` / `ENTRY` premises of
  `post_fixpoint_sound_at_ctx_semantic_cmp_final` from the pullback bounds.
- **Keyed generator (sound):** `TD_Side_Eff_Cmp_Gen.thy` — `map_gtree` (the global-key
  relabel absent from the context spine, which only relabels locals via `map_ltree`), the
  keyed generator `side_cfg_T_eff_cmp` (routes each context's global writes to slot `gkey c`).
  Call-enter edges are filtered out of the intra predecessor fold
  (`non_enter_predecessor_list`) and each frame-entry node seeds a context-independent fresh
  local frame; callee-entry globals flow only through the combine edge — this kills the enter
  duplication that merged distinct call-site activations. Its denotation
  `eq_side_cfg_T_eff_cmp` and the routing chain follow. The `pull_gk` pullback reads each
  context's single keyed slot; `side_cfg_T_eff_cmp_edge_le` (non-enter) / `_combine_le` are the
  routing-correctness bounds (global side-aggregation: `sides_intra_pull_gk` →
  `sides_le_side_rhs_fold_ctx` → `sides_fold_le_side_cfg_T_eff_cmp` →
  `side_post_solution_le_global_cmp`, landing the keyed slot), and `side_cfg_T_eff_cmp_enter_le`
  discharges the filtered enter edge from the new `sound_effectful_transfer_framed` contract
  (`Constraint_System.thy`: the enter upper bound `etf_full (etf_enter etf u) σ ≤ fresh_frame ⊔
  glob_env σ`, the companion to the old lower-bound-only `etf_sound_enter`) plus the
  frame-entry seed. The end-to-end theorem `side_cfg_T_eff_cmp_collect_sound` case-splits
  enter/non-enter, discharges `post_fixpoint_sound_at_eff` at `pull_gk`, and collapses
  (`{k. gcmp ctx k} = {gkey ctx}`) into the `cmp`-filtered read: a post-fixpoint of the keyed
  generator over-approximates IP collecting semantics at `side_env_cmp`. Sign discharges the
  framed contract via `fresh_frame_sign` / `sign_sound_etf_unit_framed`. Batch-green. Design
  note: `docs/KEYED_CONTEXT_ENTER_FRAMED_MIGRATION.md`.

### Retain keyed context (status)

- **Retain migration: complete.** The context-fixed keyed generator path routes through the
  retain discipline end-to-end: `retain_edge_tree`, the retain-compatible enter bound
  (`side_cfg_T_eff_cmp_enter_le_le`), the generalized invariant `inl_glob_le_keyed_ctx`
  (local globals ≤ keyed global slot — old publish `inl_slot_globals_bot_ctx` still implies
  it), the Sign retain spine (`sign_etf_retain` / `sign_etf_retain_st`), the exact concrete
  retain run (`kgen_retain_part_solution`), and the keyed soundness endpoint
  (`kgen_retain_keyed_generator_sound_if_post_fixpoint` / `_if_exact_fixpoint`). The
  `route_read_cmp` (routing) / `side_env_cmp` (observation) split is confirmed, and
  `Exec_Sign_Cmp_Keyed_DG_Run.thy` keeps the current keyed witness; the retain
  story still lives in `Exec_Sign_Cmp_Keyed_Retain_Run.thy`, which proves the
  routing read sees `G = SZero`/`SPos` under retain vs `SBot` under publish
  (`route_read_retain_G` / `route_read_publish_G` / `route_ctx_publish_collapses`). Retain has
  delivered its part — do not keep extending it.
- **Switching fctx: blocked by caller-context exactness / ENTER_MONO.** In
  `Example_Finite_Sign_Context_Analysis.thy` both call sites share caller context `GOther`, so
  the observation read `side_env_cmp σ (4/7, GOther) ''G'' = SNonNeg`
  (`fctx_caller_read_G_imprecise`). `ENTER_MONO` quantifies over the observation
  concretization, which retain does **not** sharpen (retain fixes only the routing read). Fix
  is a context-scheme change — a finite caller context exact on `G` at each call site — not a
  retain change. See `docs/OPEN_PROBLEMS.md`.

### Heterogeneous D/G framework (complete)

- **Stages 1 and 2: complete.** The framework transports two independent
  analysis-chosen domains — per-point answers `D`, side-published facts `G` —
  through `dg_spec` / `dg_edge_tree` / `side_cfg_T_eff_cmp_seed_dg`
  (`DG_Framework.thy`). Native `sound_dg_spec` soundness is canonical;
  homogeneous analyses are `D = G` interpretations. Migration-only split,
  packing, and post-solution transport cones have been deleted.
  `Instances/Mixed/Mixed_Sign_Interval.thy` (Sign `D`, Interval `G`) is the
  first genuinely mixed analysis: sound (`mixed_si_post_solution_collect_sound`)
  and executable (`Example_Mixed_Sign_Interval_GraphViz.thy`).
  **Scope of "complete" (2026-07 audit):** what is generic is the D/G *carrier*
  transport (`('l × 'g) dg_state`, `indep_dg_spec`, `gamma_dg_combine_sound`).
  `Mixed_Sign_Interval` is a **hand-written instance** — `mixed_si_step` /
  `mixed_si_combine` / `mixed_si_spec` are defined by hand and interpreted directly;
  it is the **independent (direct) product** (`mixed_si_spec_indep`, γ-intersection)
  with **no reduction operator**. There is **no** generic `domain × domain ⇒ domain`
  constructor and **no** reduced product. Those are tracked as **P1–P3** in
  "Research-gap reconciliation" below; do not read "complete" as "generic composition".
- **Next boundary:** consolidate the remaining paper-alignment work on top of
  the now-delivered DG spine. Caller-state-dependent `enter` is already
  realized by `DG_Context_Soundness.thy` / `Sign_DG.thy`; keyed global access is
  already exhibited by `Global_Cmp_Read.thy`, `Digest_Global_Read.thy`, and
  `Sign_Named_Global_Eff.thy`. The remaining work is to unify these witnesses
  into a single D/G/C/V story where it pays off, not to invent new semantics.
  N5 is the concrete consolidation slice; see `docs/DGCV_LAYER_MIGRATION.md`
  for the file order and first shared-lemma targets.
  Audit record: `docs/DGCV_LAYER_MIGRATION.md`; limitation tables:
  `docs/SPLIT_STATE_MIGRATION.md`.

### Trace-context analysis (planned — umbrella)

History-sensitive analysis: trace semantics → `cfg_collect_ctx` → context-indexed
solver. Two tracks (digest/k-CFA vs semantic entry-state), shared B0–B2 foundation.
**Agent plan:** `docs/TRACE_CONTEXT_ANALYSIS_MIGRATION.md`. Track detail:
`TRACE_BASED_FORK_MIGRATION.md` (A), `SEMANTIC_CONTEXT_MIGRATION.md` (B),
`TRACE_CONTEXT_BRIDGE_MIGRATION.md` (shared semantics).

### Ghost instrumentation and checks (future — Track C)

Executable validation: ghost variables encode Level-A observables; `__goblint_check`
assertions; Phase 2 proves flat analyzer fails where computed context analyzer
passes (D5). **Depends on** trace-context B3. Plan:
`docs/GHOST_INSTRUMENTATION_MIGRATION.md`. Thesis stretch — declarative soundness
chain remains primary (`docs/THESIS_SCOPE_MEMO.md`).

### Trace-based analyzer fork (planned — Track A detail)

Full digest-partitioned analyzer (one abstract state per `(pp, digest)`), still executable on `TD_side`. The trace contract (`digest_env_sound` / `digest_read_sound`) already exists and is proved realizable by the flat collapse (`flat_env_is_digest_sound`); the fork produces a *tighter* `envd`. Approach A (digest-indexed unknowns), first instance k-call-string. Plan + slices + exit criteria: `docs/TRACE_BASED_FORK_MIGRATION.md`. Single-threaded precursor to thread-modular work.

### Domain stretch

Interval is the next instance. Octagon is the relational stretch. Both fit the existing `sound_domain` / `abstract_domain` locale chain. **Interval pipeline is the architectural template**: once instantiated, octagon and any further domains follow the same scaffold provided the `vname ⇒ 'a abs_state` pointwise lifting is adequate. For domains where it is not (e.g. octagons over DBMs), see "Two-layer split" below.

### Blazy 2013 (arXiv:1304.3596) — adopted directions

The repo's `sound_domain` locale and HOL `fun`-instance lifting already match Blazy 2013's minimalist `adom` interface and `NonRelDom.make` functor, free of charge. Four paper patterns are queued as additive extensions on the issue tracker (search label `source:blazy-2013`):

1. **Backward transformers + iterative `assume` refinement** (§5.2). Forward-only `tf_assume` cannot infer dual bounds from chained comparisons (`if (0 ≤ x ∧ x < y ∧ y < z ∧ ... ∧ v < 10)`). Adding `tf_backward_*` and a bounded forward+backward fixpoint iteration recovers tight bounds. Precision win on interval.
2. **Direct product → reduced product locales** (§3.3 + §5.3). Direct product is γ-intersection; reduced product adds a `reduction` operator. Useful once a second numerical domain is around (interval + octagon).
3. **`range` query interface** (§5.1). Separates "what is the abstract value of this expression?" from "how does this transition update the state?". Used internally by `assume`; thesis-narrative win.
4. **Decidable post-fixpoint checker** (§4 translation-validation pattern). Not needed for soundness — AFP TD is verified — but cheap to add and pedagogically valuable as a contrast point to the verified-solver approach.

Two larger refactors are queued but not committed to:

- **Two-layer split** of `num_value_domain` (scalar) from `env_domain` (environment-level). Currently collapsed via the HOL `fun`-instance. Needed if and only if relational domains require their own `env_domain` instance (octagons do; intervals do not).
- **Sparse environment representation** (`vname ⇀ 'a` with implicit-⊤ default, à la `AbTree.make`). Executability + dead-code-elimination win. Subsumes part of P9.

Out of scope: memory layer (`mem_dom`, §6) — IMP2 has no pointer/memory model; signed/unsigned reduced product — IMP2 uses ℤ; translation-validated Bourdoncle — repo's AFP TD is strictly stronger.

### Octagon / relational domains — flagship stretch

**Value.** Relational numerical abstraction (octagons à la Miné: `x − y ≤ c`, `x + y ≤ c`) is the next major precision step beyond intervals. There is **no existing Isabelle/HOL formalization of octagons in AFP**, so a clean implementation here is a publishable artifact on its own (separate AFP entry: `Octagon_Domain`) in addition to being a thesis stretch goal. The reduced product Octagon × Interval is the canonical demonstration that the repo's pipeline scaffold handles relational and non-relational domains uniformly.

> ⚠️ **This is the hardest open work item.** Realistic estimate: **4–6 weeks of focused effort**, of which roughly 2 weeks is architectural plumbing in this repo before any octagon theory is touched. Do **not** estimate this as "another domain like interval".

#### Why it is difficult

1. **Architectural mismatch with the pointwise lifting.** The repo's `'a abs_state = vname ⇒ 'a` is per-variable: every abstract state is a pointwise function from variable names to a single-variable abstract value. Sign, interval, parity, congruence — all of these fit. **Octagons do not.** A DBM (difference-bound matrix) tracks bounds on `xᵢ − xⱼ` and `xᵢ + xⱼ` for every variable pair; the natural type is **whole-state**, not per-variable. The HOL `fun :: sup` / `fun :: bot` instances that give us `sound_domain` "for free" do not apply. Either the `env_domain` interface is split into a relational variant (the principled fix; see "Two-layer split" above), or octagon ships with a bespoke `abs_state` type and a parallel pipeline plumbing path (the bypass).

2. **DBM canonical closure.** Octagon soundness depends on operating on **strongly closed** DBMs (Floyd-Warshall closure adapted for the doubled variable set used by octagons). Closure has subtle invariants — strong closure differs from regular shortest-path closure because of the `x + y` constraints — and many algorithmic shortcuts in the literature trade precision for speed in ways that need explicit soundness proofs. Closure must be re-established after every transfer function. Getting this right in Isabelle is a real proof, not a paste from a textbook.

3. **Join is non-trivial.** Unlike intervals where join is bounds-min/bounds-max, the DBM join is **pointwise max on closed forms** but the result is **not automatically closed**. So either join re-closes (cost: closure pass per join, plus the soundness of "join-then-close = sound join") or the soundness statement carries closure as an invariant on inputs (cost: every transfer fn must promise to return closed DBMs). The trade-off touches every lemma.

4. **Widening on DBMs is heuristic.** The standard widening (interval-style widening on each bound, plus a closure pass — or not, depending on whether you want stability) has several variants in the literature. Picking one and proving it sound for the chosen closure invariant adds another layer.

5. **Transfer functions are richer.** Assignment `x := y + c` updates an entire row/column of the DBM, not a single cell. Constraint-based `assume` (`x − y ≤ k`) directly refines one DBM entry but then needs closure to propagate. Backward transformers (cf. Blazy 2013 §5.2) are significantly harder than for intervals because every DBM entry potentially constrains every other — there is no "operand-local" reasoning.

6. **Reduced product with interval is mandatory.** Octagon alone misses single-variable bounds that interval catches trivially (octagon expresses `x ≤ c` only as `x − 0 ≤ c` if `0` is a tracked variable, which it usually is not). The reduced product is what makes octagon useful in practice. So the soundness story is **not** just `octagon_pipeline_sound`; it is `(octagon × interval)_pipeline_sound` with a reduction operator proved sound.

7. **No reusable Isabelle prior art.** Verasco has convex polyhedra (different structure, uses an untrusted VPL library validated a-posteriori by Farkas certificates — a different design point). HOL-IMP has none. The closest references are Miné's PhD and the pen-and-paper SAS / VMCAI literature; mechanization is from scratch.

#### Phasing

The recommended path (encoded in the GitHub DAG):

```
Interval partial-corr  →  Interval pipeline  →  Two-layer split (refactor)
                                            →  Backward transformers
                                            →  Direct product  →  Reduced product
                                                                         ↓
                                                                      Octagon
```

Skipping the two-layer split is possible (route (a) bypass), but it sets a precedent for every future relational domain (zones, polyhedra) to repeat the bespoke-plumbing pattern. The split is upfront cost amortised across all future relational work.

#### Scope decision the supervisors should make

The thesis is defensible at **two scope levels**:

- **Scope A: interval pipeline closed + Blazy-2013 precision extensions** (backward transformers, iterative `assume`, reduced product with interval × sign). Polished, finished, ~3–4 months. Octagon is acknowledged as future work with the difficulty notes above.
- **Scope B: full octagon end-to-end with reduced product**. Significantly more ambitious; ~6–8 months minimum. Strong defensibility if it lands; high risk of running over.

Both are legitimate. The choice should be explicit before the two-layer split lands, because the refactor is only worth its cost if octagon (or another relational domain) actually follows.

### Total correctness

Gated on P5. Verified against the vendor (2026-07 audit): **every** vendored termination
corollary — `TD_plain_term.terminating`, `TD_term.terminating`, `TD_widen_term.terminating`,
`TD_wn_phases_term.solve_termination`, `TD_warrow_mono_term.TD_warrow_terminating` — requires
**both** `acc` (`wf {(y,x::'d). less x y}`, i.e. the value order is well-founded / finite
ascending chains) **and** `finite_vars` (`finite (UNIV :: 'x set)`, a finite unknown *type*);
see `vendor/td-verification/Basics.thy:754`, `TD_warrow.thy:3240,3260`. Two consequences the
roadmap must not paper over:

1. **Finite domain height is necessary but not sufficient.** `acc` alone does not discharge
   `solve_dom`; `finite_vars` is a separate requirement. The repo's unknowns are `(pp × 'c) + 'g`
   with `pp = nat` — an infinite type — so `finite_vars` is currently unmet. Closing it is the
   P5 finite-unknown-type refactor (routes (a)/(b) in `docs/P1_TOTAL_CORRECTNESS_ROUTE.md`),
   multi-week spine work, not "polish".
2. **The side solver has no termination corollary.** The current spine rides `TD_side`
   (`TD_side_mono` / `TD_side_upd_rule`), which the vendor gives monotonicity but **no**
   `TD_side_term`. Termination would have to come from a `TD_side ↔ TD_warrow` equivalence
   (then still gated on `finite_vars`) or a bespoke well-founded argument for the side algorithm.

Partial correctness with the named `solve_dom` hypothesis (P1) is a defensible thesis stance.
The finite-height milestone is tracked as **T1** in "Research-gap reconciliation" below, with these
blockers stated up front. Interval never satisfies `acc` (infinite height) — its convergence is
warrowing + per-run `eval`, never a finite-height argument.

### Thesis writeup

`docs/PROOF_OVERVIEW.md` is the prose-level pipeline-narrative source. The thesis chapter lifts from it; cross-references to `.thy` files are by file path, not by lemma name (those drift; `rg` finds them).

---

## Research-gap reconciliation (2026-07 audit)

Source: the *Second-Pass Research-Gap Audit* (theorem-level, read-only). Every confirmed gap is
reconciled here into one of `DONE / ACTIVE / PLANNED / STRETCH / NON-GOAL / UNDECIDED`, with a
theorem-level completion criterion. This subsection is the current view; where it conflicts with
older narrative above or in migration docs, it wins, and the conflict is listed under
"Contradictions resolved".

### Verified termination reality (read from the vendor, not assumed)

The audit checked the vendor before proposing any termination milestone (see the expanded "Total
correctness" section above). Bottom line: **no total termination result exists in-repo**
(`rg generated_solver_terminates|solver_terminates src/ vendor/` → none), every executable example
discharges `solve_dom` individually `by eval` on `solve_c`, and `threefold_mono`
(`= is_mono_eq ∧ mono_sides ∧ mono_deps`, `TD_Side_Eff_Pipeline.thy:38`) is a **soundness /
least-solution** precondition consumed independently of the `solve_dom` hypothesis
(`LTR_TD_Side_Eff_Exit.thy:211-214`) — it does **not** prove termination.

### Final research-work table

| ID | Item | Status | Priority | Depends on | Theorem-level completion criterion | Scope |
|----|------|--------|----------|-----------|-------------------------------------|-------|
| T1 | Sign finite-height ⇒ `solve_dom` (unconditional Sign soundness) | PLANNED | Framework research | P5 (finite unknown type) **and** a `TD_side` termination corollary or `TD_side↔TD_warrow` bridge | A `solve_dom`-shaped theorem for `side_cfg_T_eff … sign_etf …` with **no** `solve_dom` hypothesis, discharged from `acc`(sign) + `finite_vars`(reachable pp) + `threefold_mono`; then `side_sign_analysis_sound` restated with the `side_solve_dom` premise removed | thesis-if-P5-lands / else long-term |
| A1 | Bundled `run_analysis_source_sound` (hide the 4–5-step manual chain) | **DONE** (committed, batch-green) | Near-term | none (bundles existing partial-correctness chain) | ✔ `dg_exec_run_source_sound` (global) + `dg_run_source_sound_abs` / `dg_gen_of_eq` (in `sound_dg_spec`) in `src/Formalization/Pipeline/Run_Analysis_Sound.thy`; query-parametric; the flagship's `flagship_source_run_sound` is now a single `rule dg_exec_run_source_sound` with the `solve_dom`/`partial_post_solution`/transport/collect/source chain removed | thesis |
| A2 | Domain-registration API (essential obligations in, plumbing derived) | **DONE** (committed, batch-green) | Framework validation | A1 (shares the export shape) | ✔ `unit_dg_exec_analysis` locale (`src/Formalization/Pipeline/Run_Analysis_Sound.thy`): inputs are exactly `{domain_transfer + sound_transfer, tf_st + per-action commute, solver solve/solve_c + part_post_solution}`; outputs the generic transport lemmas `unit_dg_Hstep`/`unit_dg_Hcomb`, a semantic accessor `gamma`, and the end-to-end `run_source_sound` — no `strategy_tree`/`ltree`/`gtree`/`Inl-Inr`/`Hstep`/`Hcomb` in the derived theorem. Registered for both domains in `DG_Domain_Registration.thy` (`ivl_reg`, `sign_reg`) by `unfold_locales`. `Example_Interval_DG_Flagship` migrated: `flagship_source_run_sound` is a single `rule ivl_reg.run_source_sound`. Sign validated by `sign_reg` interpretation succeeding with no interval-specific input. Residual tree/`Inl-Inr`/`fun_of_dg_st` mentions remain only in the equation-system definition and slot-reading inspection/non-vacuity lemmas, not in the source-soundness theorem | publication |
| E1 | Parity — second finite-height analysis (validation instance) | PLANNED | Framework validation | A2 (must register through it) | `parity` domain + `gamma` + `sound_transfer` + `tf_mono`; a registered `side_parity_analysis_sound`; an executable example with a non-trivial parity result; if T1 has landed, termination inherited without a fresh `by eval`. **Failure signal:** any copy of Sign-specific tree plumbing ⇒ A2 incomplete | publication |
| E2 | Non-exit query witness (demand-driven usability) | PLANNED | Near-term | none | An executable example instantiating `side_collect_sound_in_eff_cone` (`LTR_TD_Side_Eff_Exit.thy:148`) at a `v ≠ cfg_exit`, with `solve_c … = Some σ`, a non-trivial abstract value at `v`, an anti-vacuity statement, and the cone-soundness link | thesis |
| P1 | Generic direct-product constructor (`domain × domain ⇒ domain`) | PLANNED | Medium-term | none (parallel track) | A generic construction giving lattice/`gamma`/transfer of a pair from two `sound_domain`s, with a generic direct-product soundness lemma that `Mixed_Sign_Interval` instantiates (replacing its hand-written `mixed_si_*`) | publication |
| P2 | Reduced-product locale (reduction operator) | STRETCH | Medium-term | P1 | A `reduction` operator interface + soundness of reduced transfer (`γ(reduce d) = γ(d)`, reduce monotone/reductive), end-to-end on one instantiated product | publication |
| P3 | Relational / product flagship | STRETCH | Medium-term | P2 (and, for octagon, the two-layer split) | An end-to-end instantiated product analysis with a computed non-trivial result and source-level soundness | publication / long-term |
| G1 | Framework-effort evaluation | UNDECIDED → publication task | Publication | A2, E1 | Not a theorem: a measured comparison (essential-lemma count, solver-glue count, shared-vs-copied across Sign/Interval/Parity, tree-concept leakage before/after A2, termination theorems reused). Classified as a publication/evaluation task, not implementation | publication |
| — | Constant propagation / Taint | NON-GOAL (current scope) | — | — | Faithfulness breadth only; taint needs the inter-analysis query gap (`GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`). Not on the critical path | long-term |
| — | Broad generic solver-totality (any finite-height + monotone ⇒ terminates) | STRETCH | — | P5 + `TD_side` termination theory | Would need a generic `TD_side_term`-style result; the vendor proves this only for plain/warrow/wn solvers, not the side solver. Do not promise the general theorem | long-term |
| — | Octagon end-to-end | STRETCH | — | P1, P2, two-layer split | See "Octagon / relational domains" above; 4–6 weeks, no Isabelle prior art | long-term |

### Dependency order (corrected — supported by the theories, not the candidate order)

The audit's candidate order led with T1; that is wrong. T1 is the heaviest item and is *blocked*
(P5 + missing `TD_side` termination), while A1 and E2 are cheap, independent, and unblocked. Parity
(E1) should follow the registration API (A2), so it *validates* rather than *copies* it. Product
work is an independent parallel track.

```
NEAR-TERM (unblocked, cheap):
   A1  bundled run-analysis soundness  ─┐
   E2  non-exit query witness  ─────────┘   (independent of everything)

FRAMEWORK VALIDATION:
   A1 ──▶ A2  domain-registration API ──▶ E1  Parity  (Parity witnesses A2; and T1 if T1 has landed)

TERMINATION (heavy, blocked — parallel, not a prerequisite for the above):
   P5 finite unknown type  +  TD_side termination corollary ──▶ T1  Sign finite-height ⇒ solve_dom

PRODUCTS (independent parallel track):
   P1 direct product ──▶ P2 reduced product ──▶ P3 relational/product flagship
```

Rationale for the four ordering questions the task poses: **the bundle precedes termination** (A1
needs only the existing partial-correctness chain, not `solve_dom` totality); **the registration
API precedes Parity** (E1's value is as an A2 validator — copying Sign plumbing is the failure
signal); **Parity is not required to prove T1** (T1's blocker is domain-independent P5 /
`TD_side_term`, though Parity is a good second witness once T1 lands); **product work is
independent** and can run in parallel with everything.

### Scope placement

- **Current thesis:** A1, E2, and T1 *iff* the P5 refactor is undertaken (otherwise T1 stays a
  named hypothesis — the defensible partial-correctness stance).
- **Follow-up publication:** A2, E1, P1, G1 — the "framework is genuinely reusable" claim.
- **Long-term framework development:** P2, P3, octagon, constant-propagation/taint, broad
  solver-totality.

### Contradictions resolved (2026-07)

- **"solver termination is established"** — never asserted here, but the "Total correctness"
  section now states the two unmet vendor requirements (`finite_vars`, no `TD_side_term`) instead
  of implying `finite (UNIV::'pp set)` is the only blocker.
- **"product composition is generic"** — the "Heterogeneous D/G framework (complete)" bullet now
  distinguishes the generic D/G *carrier* transport from the **hand-written** `Mixed_Sign_Interval`
  instance, and records that no reduced product / generic domain-product exists (P1–P3).
- **"the API is already minimal and fully packaged"** — the obligation set is near-minimal
  (`DOMAIN_INTERFACE_MINIMIZATION.md`). Packaging closed by A2 (**DONE**): the `unit_dg_exec_analysis`
  registration locale exports `run_source_sound` with `strategy_tree` / `ltree` / `gtree` / `Inl-Inr` /
  `Hstep` / `Hcomb` absent from the derived theorem; residual mentions survive only in equation-system
  definitions and slot-reading inspection lemmas.
- **"examples demonstrate arbitrary query points"** — every executable example queries `cfg_exit`;
  the query-parametric theorem exists but has no non-exit witness. Tracked as E2.
- **"source-level soundness through one direct theorem"** — the shapes exist
  (`source_activation_sound`, `source_reaches_ltr_collect`, `side_analyse_eff_collect_sound_exit_ltr`)
  but are not bundled; examples chain 4–5 theorems by hand. Tracked as A1.
- **M3 T1 "safe, cheap win"** — corrected in `docs/M3_CONTEXT_BOUNDING_TERMINATION_MIGRATION.md`:
  T1 is gated on P5 and a missing `TD_side` termination corollary, exactly as that doc's own T2 row
  cautioned.

### Remaining uncertainties (feasibility not established from the solver theories)

- Whether a `TD_side` termination corollary is derivable at all — via a `TD_side ↔ TD_warrow`
  equivalence, or a bespoke well-founded argument for the side algorithm. The vendor provides
  termination only for the plain / warrow / wn solvers (`TD_*_term` locales), **not** `TD_side`.
  Until this is checked, **do not claim finite height implies `solve_dom` for the side solver.**
- Whether the P5 finite-unknown-type refactor is compatible with the `pp = nat` linear-order /
  `predecessor_list` machinery without a multi-week spine retype (route (a) in
  `P1_TOTAL_CORRECTNESS_ROUTE.md`).

## How to keep this file current

Edit when:

- A *stable* decision changes (e.g., "we are dropping IMP2 in favour of HOL-IMP `Abs_Int2`").
- A new architectural direction enters or leaves the queue.
- A pointer above breaks.

Do **not** edit for:

- Individual issue progress (use GitHub).
- Lemma renames or sorry counts (use `rg`).
- New issues that fit an existing direction.
