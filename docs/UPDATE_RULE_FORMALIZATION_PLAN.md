# Plan: verify the update rules and expose them as analyser features

**Goal.** Turn the vendored side-solver *update rules* (per-origin joins, Apinis
warrowing = widening/narrowing, and their combination) from eval-only experiments into
**soundness-backed features** of the analyser: the analysis can be run under any of them
with a machine-checked over-approximation theorem, so `run_menu`'s columns are certified,
and the analyser can **terminate on unbounded loops with a proof** (widening).

## Status (2026-07-07): Phases A-D done, E open

- **A (audit) --- done, and it collapsed the plan.** Both unknowns resolved favorably:
  `part_post_solution` (`Basics_side.thy:337`) is *update-rule-independent* (just "sigma is
  a join-order post-solution"), and the vendor proves it for *every* rule
  (`partial_post_solution` on the `TD_side_upd_rule` locale). The whole transport below it is
  rule-agnostic. **No bridge lemmas needed** --- per-origin/warrowing soundness is pure
  instantiation.
- **B (warrowing sound) --- done.** `mode_digest_abstracts_wa` in
  `Exec_Sign_Mode_Compiled_Run`.
- **C (per-origin sound) --- done.** `mode_digest_abstracts_po` (keeps the digest sharp).
- **D (parametric) --- done for the digest example.** `mode_digest_sound_all_update_rules`
  bundles the three abstract post-solutions --- the exact precondition `Analysis_Sound` /
  `Constraint_System_Sound` consume. A fully generic top-level analyser selector (one entry
  parametric in the rule) remains optional future work; the per-run instantiation is a
  4-lemma copy with the interpretation swapped.
- **E (close P11) --- open, diagnosed.** `solve_dom` is `iterate_dom` (established per run,
  here by `eval` on `solve_c \<noteq> None`), *not* a free termination theorem. For
  `warrowing_per_origin`, `by eval` raises `Interrupt_Breakdown` inside the vendor's
  `update_global_warrowing_per_origin` iteration (`Update_rules.thy:143`), so neither the
  executable result nor `solve_dom` is obtainable on our systems --- and there is no
  soundness path without one. Fixing it is vendor-internal code-gen work; left to P11.

Result: the digest analysis is certified sound under `join`, `per_origin`, and `warrow`;
widening is now a *proven-sound* feature (soundness holds while it terminates on unbounded
loops). The remaining gap is the one ideal-but-unexecutable combination (per-origin widening).

---

Status when written: soundness was proved and instantiated only for `always_join`. The other
rules ran under `by eval` (see `Exec_Ivl_Mode_Compiled_Run`, `Exec_Ivl_Run`) with no soundness
corollary.

---

## The leverage (why this is mostly instantiation, not new proof)

Two facts make this tractable:

1. **The vendor already proves the hard part, generically.**
   `vendor/td-verification/TD_side_upd_rule.thy:1787`,
   `theorem partial_post_solution`, is proved for the abstract `TD_side_upd_rule`
   (= `update_rule`) locale. Every update rule is an interpretation of that locale
   (`TD_side_upd_rule.thy:2409-2441`: `always_join`, `per_origin`, `warrowing_apinis`,
   `warrowing_per_origin`, `bounded_narrowing`). So **each of the five solvers already
   produces a `part_post_solution`.**

2. **Our soundness spine consumes exactly `part_post_solution`.**
   `Analysis_Sound.thy` / `Constraint_System_Sound.thy` take `post_fp: "n g tf (\<squnion>) bot s0 env"`,
   and the examples reach it through the `part_post_solution -> n` transport
   (`mode_digest_part_post_solution_st`, `part_post_solution_digest_st_to_abs_eff`).

So the collecting-soundness is *already* update-rule-agnostic in its hypothesis. The gap is
the **instantiation gap** (Kappelmann audit item 2): we have only surfaced the `always_join`
corollary. Closing it is wiring plus two bridge lemmas.

---

## Two unknowns to resolve first (they set the difficulty)

- **U1 — warrowing shape.** Our hypothesis is a *join* post-fixpoint (`n \<dots> (\<squnion>) \<dots>`). A
  warrowing solution is a *widen* post-fixpoint. Widening over-approximates join
  (`x \<nabla> y \<sqsupseteq> x \<squnion> y`), so a widen-post-fixpoint should also satisfy the join-post-fixpoint
  hypothesis. Confirm whether this is literally true of `part_post_solution` or needs a one-line
  `widen \<sqsupseteq> join` lemma.
- **U2 — per-origin global shape.** Per-origin keeps each write origin's contribution in a
  separate cell and collapses them on *read* (`rho_lookup`). Confirm whether
  `part_post_solution` for `per_origin` is already stated over the collapsed (read) globals
  --- if so per-origin is direct; if not, add a collapse lemma (per-origin globals `\<sqsupseteq>`
  merged join).

Both are answered by reading the vendor's `part_post_solution` definition and the
`per_origin` / `warrowing_apinis` `update_global` definitions --- a half-day audit, no proof.

---

## Phases

### Phase A --- Audit the coupling (0.5 day)
Read `Constraint_System_Sound.thy`, `Analysis_Sound.thy`, `TD_Side_Eff_Interface.thy` and the
vendor `part_post_solution` / `update_global` definitions. Deliverable: a precise statement of
(a) exactly which lemmas mention `always_join` vs the generic predicate, and (b) resolutions to
U1 and U2. This decides B and C scope before any proof.

### Phase B --- Warrowing as a sound feature (1-2 days, highest value)
- Bridge a warrowing `part_post_solution` to the `n \<dots> (\<squnion>) \<dots>` hypothesis (U1 lemma).
- Surface `side_sign_analysis_sound_warrow` and the interval analogue.
- **Payoff:** a proven-sound analysis that *terminates* on unbounded loops. The interval
  `while (x < 1000000)` result (`wide_loop_widened_then_narrowed`) upgrades from eval-only to
  soundness-backed. This is the single most useful gap-closer toward real programs.

### Phase C --- Per-origin as a sound feature (2-3 days)
- Resolve U2: either the vendor predicate already collapses on read (direct), or add the
  per-origin -> merged-join reduction lemma.
- Surface per-origin sound corollaries. Certifies `iv_digest_per_origin_precise` and
  `iv_digest_across_update_rules`.

### Phase D --- Make the analyser update-rule-parametric (1 day)
- Add an update-rule selector at the top-level analysis entry (a locale parameter or a small
  sum type `Join | PerOrigin | Warrow`), each with a sound-analysis corollary.
- Back each `solver_menu` entry with its soundness theorem, so `run_menu` is certified, not
  just executable.
- Update `Analysis_Sound` README, `docs/NON_GOALS.md`, and this plan's status.

### Phase E --- Close P11 (stretch)
Chase the `warrowing_per_origin` code-gen `Interrupt_Breakdown` (likely a missing code equation
or a non-terminating narrowing over the per-origin map). Then one executable solve delivers
*both* loop termination and a precise digest --- the currently-open combination.

---

## Risks

- **U2 is the swing factor.** If `part_post_solution` is stated over per-origin (uncollapsed)
  globals, Phase C needs a genuine reduction proof, not just instantiation.
- **`bounded_narrowing` untested** --- may have its own code-gen issue; out of the initial scope.
- **Precision is not soundness.** These theorems certify over-approximation only. That
  warrowing is *more precise* than join on a given loop (as `run_menu` shows) is a separate,
  non-theorem observation --- do not conflate.

## First concrete step
Phase A: read `Constraint_System_Sound.thy` + the vendor `part_post_solution` /
`update_global_warrowing` / `update_global_per_origin` definitions, and write the U1/U2
resolutions here. Everything downstream keys off that.

## See also
- `docs/OPEN_PROBLEMS.md` P11 (per-origin widening code-gen).
- `src/Analysis/Generic/Solver/Exec/Solver_Menu.thy` (the executable menu this plan certifies).
- `Exec_Ivl_Mode_Compiled_Run.thy`, `Exec_Ivl_Run.thy` (the eval-only witnesses to upgrade).
