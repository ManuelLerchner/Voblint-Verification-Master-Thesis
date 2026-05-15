# Proof Phases

Concrete execution plan for closing the remaining `sorry`s. Companion to
`docs/PROOF_OVERVIEW.md` (big-picture chain) and `AGENTS.md` (workflow).

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
big_step (c, s) t                                       -- IMP2_Big_Step
  ⊆ collect c {s}                                       -- IMP2_Collecting
  ⊆ cfg_collect (to_cfg c) {s} (cfg_exit ...)           -- CFG_Collecting   [bridge #1]
  ⊆ γ_state (env (cfg_exit ...))                        -- Constraint_System_Sound [bridge #2]
                                                        -- via post-fixpoint
  env = td_analyse c tf join bot init                   -- TD_Interface (AFP TD_plain)
```

Bridges #1 and #2 are the two hard pieces. Everything else is composition.

---

## Sorry inventory (snapshot)

| File                                       | n | Status      |
|--------------------------------------------|---|-------------|
| `IMP2/IMP2_Collecting.thy`                 | 1 | Phase 1     |
| `CFG/CFG_Path.thy`                         | 2 | Phase 1     |
| `CFG/CFG_Collecting.thy`                   | 3 | Phase 1 ★   |
| `Equations/Constraint_System_Sound.thy`    | 3 | Phase 1 ★   |
| `Solver/TD_Soundness.thy`                  | 2 | Phase 2     |
| `Pipeline/Pipeline.thy`                    | 6 | Phase 2     |
| `Pipeline/Result_Mapping.thy`              | 1 | skip / drop |
| `Examples/Example_Sign_Analysis.thy`       | 3 | Phase 4     |
| `Domains/Interval_Domain.thy`              |15 | Phase 3     |
| `Solver/TD_Total.thy`                      | 8 | optional    |
| `Equations/Direct_Equations.thy`           | 7 | skip (alt)  |

★ = blocks everything downstream.

---

## Phase 1 — Hard bridges

Goal: close the two semantic bridges. Everything downstream is mechanical.

### 1.1 CFG collecting ≡ IMP collecting at exit
File: `src/CFG/CFG_Collecting.thy`

- `cfg_collect_exit_le_collect`
  Strategy: `lfp_least`. Show `(λv. collect c S restricted to v)` is a
  post-fixpoint of the CFG transformer `F`. Per-`com` case analysis
  (SKIP / Assign / Seq / If / While); each CFG edge must match a
  `big_step` step.
- `collect_le_cfg_collect_exit`
  Strategy: induction on `big_step`. Unfold `lfp` once per step
  (`lfp_unfold` with `mono`). While case: IH on body + IH on
  recursive `WhileTrue`.
- `cfg_reach_entry`
  Direct unfold of `cfg_collect` at entry; `S ⊆ S ∪ collect_pp ...`.

### 1.2 Post-fixpoint over-approximates collecting
File: `src/Equations/Constraint_System_Sound.thy`

- `collect_pp_abstract_sound`
  Strategy: case split on `edge_action`. Use the three `tf_sound_*`
  hypotheses + `is_post_fixpoint` join upper bound to lift each
  edge into `γ_state(env v)`.
- `post_fixpoint_sound`
  Strategy: `lfp_lowerbound`. Show `λρ v. γ_state(env v)` dominates
  the CFG collecting functional. Uses 1.2.1 at every step.
- `exit_sound` (corollary)
  Compose `post_fixpoint_sound` with
  `cfg_collect_exit_eq_collect` + `cfg_reach_entry`.

### 1.3 Local clean-up

- `IMP2_Collecting`: remaining `While` case.
- `CFG_Path`: `cfg_exit_reachable_from_entry`, `to_cfg_exit_reachable`
  (intentionally weak — discharge for `to_cfg` only).

Exit criterion: `Constraint_System_Sound.exit_sound` and
`CFG_Collecting.cfg_collect_exit_eq_collect` have no `sorry`.

---

## Phase 2 — Pipeline composition

Mechanical once Phase 1 is closed.

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

- `Examples/Example_Sign_Analysis.thy`: close executable demo sorrys.
- Decide on `Result_Mapping.thy`: drop (Option 2 already headline) or
  repair per `PROOF_OVERVIEW.md` §1 Option 3.
- Final batch build green:
  `isabelle build -d ~/afp/thys -d vendor/td-verification -D . Goblint_Formalization`
  with `quick_and_dirty` removed from `ROOT`.

---

## Working order

1. `cfg_collect_exit_le_collect` (Phase 1.1)
2. `collect_le_cfg_collect_exit` (Phase 1.1)
3. `cfg_reach_entry` (Phase 1.1)
4. `collect_pp_abstract_sound` (Phase 1.2)
5. `post_fixpoint_sound` + `exit_sound` (Phase 1.2)
6. `pipeline_sound` + `pipeline_invariant_sound` (Phase 2)
7. Sign corollaries (Phase 2)
8. Interval (Phase 3, optional)
9. Examples + polish (Phase 4)

Commit after each step closes — never mid-bridge.
