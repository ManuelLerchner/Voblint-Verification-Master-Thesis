# TD solver bridge (side-effecting, interprocedural)

Connect the vendored **TD side** solver (`vendor/td-verification`, session `TD`, theory `TD_side`)
to the interprocedural CFG and effectful `rhs` format.
`side_analyse_eff pi ps c etf bot s0 v` is proved sound against `cfg_collect` at `v`
(`side_analyse_eff_collect_sound_exit_pruned_gen`).

**Theories**

| File | Role |
| --- | --- |
| `Strategy_Tree_Monad.thy` | `seqcomp_tree` (bind), `traverse_seqcomp`, `dep_aux_seqcomp`, `sides_of_rhs_seqcomp`; `static_deps`, `seqcomp_mono` |
| `TD_Side_CFG.thy` | `restrict_local`, `restrict_global`, `side_env`; unit-global tree constructors (`unit_edge_tree`, `unit_combine_tree`); `trans_dep\<^sub>L` step/trans lemmas |
| `TD_Side_Tree.thy` | `side_cfg_T_eff` effectful IP strategy trees; folds `side_acc_eff` |
| `TD_Side_Eff_Bounds.thy` | Monotonicity + dependency stability; `side_cfg_T_eff_is_mono_eq_gen`, `_mono_sides_gen`, `_mono_deps_gen` |
| `TD_Side_Eff_Interface.thy` | `td_cfg_side_solver_eff` locale, `side_cfg_solve_dom_eff`, `side_analyse_eff` |
| `TD_Side_Eff_Pipeline.thy` | Ties mono/static contract + collecting soundness for an arbitrary `etf` |
| `TD_Side_Eff_Sound.thy` | `post_fixpoint_sound_at_eff` — effectful post-fixpoint over-approximates `cfg_collect` |
| `TD_Side_Eff_Soundness.thy` | Effectful collecting soundness with pruning: `side_collect_sound_exit_pruned_eff`, `side_analyse_eff_collect_sound_exit_pruned_gen` |
| `TD_Side_RHS_Generator.thy` | `unit_rhs_generator` / `mixed_rhs_generator` locale stacks; `threefold_mono` discharge |
| `Exec_Bridge.thy` | `'a st` fold mirror + `fun_of_st` simulation; `part_post_solution_st_to_abs_eff` lifts an `'a st` post-solution to a `part_post_solution` of `side_cfg_T_eff` |
| `Solver_Side_RG.thy` | Reach-global lemmas: reachability under side-effecting queries |

**External:** Algorithm correctness is in `TD.TD_side` (`partial_correctness`, `TD_side_mono`).
This folder wires `part_post_solution` to `is_post_fixpoint` via `Generic/Equations/Constraint_System_Sound`.

**Downstream:** `Instances/Sign/Sign_Side_Soundness.thy` — `side_sign_analysis_sound`;
`Instances/Interval/Interval_Side_Soundness.thy`; `Formalization/Pipeline/Trace_Analysis_Sound.thy`.
