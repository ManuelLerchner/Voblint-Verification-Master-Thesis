# Proof Phases

Concrete execution plan for closing the remaining `sorry`s. Companion to
`docs/PROOF_OVERVIEW.md` (big-picture chain) and `AGENTS.md` (workflow).

HTML walkthroughs: `docs/html/PIPELINE_WALKTHROUGH.html`,
`docs/html/IMP_CFG_WALKTHROUGH.html`.

---

## Thesis target (final theorem)

For any IMP program `c`, terminating run `(c, s) ⇒ t` implies
`t ∈ γ_state(σ_exit)`, where `σ` is the TD solver result and
`σ_exit = σ (cfg_exit (to_cfg c))`.

Strong form (Option 2, supervisor-preferred): for every program point `v`,
`cfg_reach (to_cfg c) {s} v ⊆ γ_state(σ v)`. Exit-soundness is the
`v = cfg_exit` special case.

---

## Pipeline chain

```
big_step (c, s) t                                       -- IMP2_Semantics
  ⊆ collect c {s}                                       -- IMP2_Collecting
  = cfg_collect (to_cfg c) {s} (cfg_exit ...)           -- CFG_Collecting   [bridge #1 DONE]
  ⊆ γ_state (env (cfg_exit ...))                        -- Constraint_System_Sound [bridge #2]
                                                        -- via post-fixpoint
  env = td_analyse c tf join bot init                   -- TD_Interface (AFP TD_plain)
```

Bridge #1 is closed (no `sorry` in `src/IMP2/` or `src/CFG/`). Bridge #2 and
pipeline composition remain open.

---

## Sorry inventory (live)

Run: `rg -n '^\s*sorry' src/` (source of truth).

| File                                    | n  | Status                          |
|-----------------------------------------|----|---------------------------------|
| `IMP2/IMP2_Collecting.thy`              | 0  | **done** (optional `collect_While` removed) |
| `CFG/CFG_Path.thy`                      | 0  | **done** (exit-reachability stubs removed) |
| `CFG/CFG_Collecting.thy`                | 0  | **done** — `cfg_collect_exit_eq_collect` |
| `Equations/Constraint_System_Sound.thy` | 3  | Phase 1 ★ — blocks downstream   |
| `Solver/TD_Soundness.thy`               | 2  | Phase 2                         |
| `Pipeline/Pipeline.thy`                 | 4  | Phase 2                         |
| `Domains/Interval_Domain.thy`           | 7  | Phase 3 (stretch)               |
| `Solver/TD_Total.thy`                   | 8  | optional (totality / widening)  |
| `Equations/Direct_Equations.thy`        | 7  | skip (alternate path)           |
| `Scratch_Explore.thy`                   | 1  | scratch only                    |

★ = blocks everything downstream.

---

## Phase 1 — Hard bridges

### 1.1 CFG collecting ≡ IMP collecting at exit — **DONE**

File: `src/CFG/CFG_Collecting.thy`

Closed lemmas:

- `cfg_path_collect_exit_le_collect` / `cfg_collect_exit_le_collect`
- `collect_le_cfg_collect_exit`
- `cfg_collect_exit_eq_collect` (main theorem)
- `cfg_reach_entry`
- Supporting: `compile_path_big_step`, `big_step_cfg_path`, `path_sound_cfg_collect`, …

Exit criterion for 1.1: satisfied.

**Removed (not sorry’d):** `collect_While` in `IMP2_Collecting.thy` (explicit
`lfp` characterisation — bridge uses `big_step` induction instead);
`cfg_exit_reachable_from_entry` / `to_cfg_exit_reachable` in `CFG_Path.thy`
(not needed; false for arbitrary `cfg_wf` CFGs).

### 1.2 Post-fixpoint over-approximates collecting — **OPEN**

File: `src/Equations/Constraint_System_Sound.thy`

- `collect_pp_abstract_sound`
  Strategy: case split on `edge_action`. Use the three `tf_sound_*`
  hypotheses + `is_post_fixpoint` join upper bound to lift each
  edge into `γ_state(env v)`.
- `post_fixpoint_sound`
  Strategy: `lfp_lowerbound`. Show `λρ v. γ_state(env v)` dominates
  the CFG collecting functional. Uses 1.2.1 at every step.
- `exit_sound` (corollary)
  Compose `post_fixpoint_sound` with **proved**
  `cfg_collect_exit_eq_collect` + `cfg_reach_entry`.

Exit criterion: `Constraint_System_Sound.exit_sound` has no `sorry`.

---

## Phase 2 — Pipeline composition

Mechanical once Phase 1.2 is closed.

File: `src/Pipeline/Pipeline.thy`, `src/Solver/TD_Soundness.thy`.

- `pipeline_sound`
  From `exit_sound` + `td_analyse_post_fixpoint` + unfold
  `domain_transfer_sound`.
- `pipeline_invariant_sound` (Option 2)
  Direct from `post_fixpoint_sound` + `td_analyse_post_fixpoint`;
  no termination assumption needed.
- `sign_pipeline_sound`, `sign_pipeline_invariant_sound`
  Discharge γ_state coercion `sign_domain.gamma_state` ↔
  `sound_domain.gamma_state gamma_sign`.
- `td_solver_sound`, `sign_analysis_sound` (TD_Soundness):
  composition only.

Exit criterion: `pipeline_invariant_sound` and `sign_pipeline_sound`
closed without `sorry`.

---

## Phase 3 — Interval stretch (optional)

File: `src/Domains/Interval_Domain.thy`.

- Interval lattice laws (`join_ivl` comm/assoc; `ivl_le` partial order).
- TF soundness: `assign_ivl_sound`, `assume_ivl_sound`,
  `assume_not_ivl_sound`.
- `ivl_pipeline_sound`, `interval_analysis_sound` via Phase 2 template.
- Skip widening termination (`TD_Total`) unless total correctness
  required by supervisors. Partial correctness suffices for soundness.

---

## Phase 4 — Examples + thesis polish

- `Examples/Example_Sign_Analysis.thy`: no `sorry` in current tree (verify on change).
- Decide on `Result_Mapping.thy`: drop (Option 2 already headline) or
  repair per `PROOF_OVERVIEW.md` §1 Option 3.
- Final batch build green:
  `isabelle build -d ~/afp/thys -d vendor/td-verification -D . Goblint_Formalization`
  with `quick_and_dirty` removed from `ROOT`.

---

## Working order

1. ~~`cfg_collect_exit_eq_collect` (Phase 1.1)~~ **done**
2. `collect_pp_abstract_sound` (Phase 1.2)
3. `post_fixpoint_sound` + `exit_sound` (Phase 1.2)
4. `pipeline_sound` + `pipeline_invariant_sound` (Phase 2)
5. Sign corollaries (Phase 2)
6. Interval (Phase 3, optional)
7. Examples + polish (Phase 4)

Commit after each step closes — never mid-bridge.
