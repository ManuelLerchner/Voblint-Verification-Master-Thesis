# TD solver bridge (side-effecting, interprocedural)

**Main contribution:** Connect the vendored **TD side** solver (`vendor/td-verification`,
session `TD`, theory `TD_side`) to our interprocedural CFG and effectful `rhs`
format. `side_analyse_eff pi ps c etf bot s0 v` is proved sound against
`cfg_collect` at `v` (`side_analyse_eff_collect_sound_exit_pruned_gen`).

The solver rides on the **effectful** equation system `side_cfg_T_eff`
(transfer functions are strategy trees that may query and side-effect named
globals). Domain-facing theories provide native `effectful_domain_transfer`
records. Unit-global pure-transfer records support executable transport and
legacy-style pure domains without a separate adapter. Their IP-soundness and
solver-interface layers were retired (see `docs/EFFECTFUL_TF_MIGRATION.md`).

**Theories**

| File | Role |
| --- | --- |
| `Strategy_Tree_Monad.thy` | `seqcomp_tree` (bind) + `traverse_seqcomp` / `dep_aux_seqcomp` / `sides_of_rhs_seqcomp`; `static_deps` and `seqcomp_mono` |
| `TD_Side_CFG.thy` | `restrict_local`, `restrict_global`, `side_env`; unit-global pure-transfer tree shape (`pure_edge_tree`, `pure_combine_tree`, `pure_effectful_transfer`); `trans_dep\<^sub>L` step/trans lemmas |
| `TD_Side_Tree.thy` | `side_cfg_T_eff` effectful interprocedural strategy trees; folds `side_acc_eff` |
| `TD_Side_Eff_Bounds.thy` + `TD_Side_Eff_Soundness.thy` | monotonicity + dependency stability; TD_side preconditions `side_cfg_T_eff_is_mono_eq` / `_mono_sides` / `_mono_deps`, plus pure-transfer compatibility discharges |
| `Exec_Bridge.thy` | executable `'a st` fold mirror + `fun_of_st` simulation; `part_post_solution_st_to_abs_eff` maps the `'a st` post-solution to a `part_post_solution` of `side_cfg_T_eff` for a matching unit-global effectful record |
| `TD_Side_Eff_Sound.thy` | `post_fixpoint_sound_at_eff` — a post-fixpoint of the effectful system over-approximates `cfg_collect` (in `sound_effectful_transfer`) |
| `TD_Side_Eff_Bounds.thy` | per-edge / per-combine post-solution bounds (`etf_combined_le_eff`) and the generic TD_side preconditions (`side_cfg_T_eff_is_mono_eq_gen` …) |
| `TD_Side_Eff_Interface.thy` | `td_cfg_side_solver_eff` locale, `side_cfg_solve_dom_eff`, `side_analyse_eff` (TD_side backend on `side_cfg_T_eff`) |
| `TD_Side_Eff_Pipeline.thy` | ties the three strands for an arbitrary `etf`: solver interface from the per-tree mono/static contract + collecting soundness from a post-solution |
| `TD_Side_Eff_Soundness.thy` | standalone effectful collecting soundness with pruning: eff dependency cone (`reaches_imp_trans_dep_or_eq_side_eff`, `side_cone_in_vars_eff`), `side_collect_sound_exit_pruned_eff`, executable `side_analyse_eff_collect_sound_exit_pruned_gen` |

**External:** Algorithm correctness is in the TD session (`TD_side.partial_correctness`
/ `TD_side_mono`). This folder wires `part_post_solution` to `is_post_fixpoint`
via `Constraint_System_Sound`.

**Operational hypothesis (P1):** `side_cfg_solve_dom_eff g etf bot s0 v` at each
queried program point. This is `TD_side.solve_dom destab_opt True (side_cfg_T_eff …) v`.
Monotonicity of `side_cfg_T_eff` is proved; termination gated on finite `pp` (P5).

**Soundness mechanism:** `side_analyse_eff_collect_sound_exit_pruned_gen` proves
soundness at `cfg_exit` by showing every backward-reachable node from `v₀` is in the
solver's `trans_dep` cone (eff reach-cone lemma), so `part_post_solution` covers all
relevant unknowns. CFG pruning (`CFG_Prune`) restricts to the backward-reachable
subgraph.

**Downstream:** `Analysis/Domains/Sign_Side_Soundness.thy` — `side_sign_analysis_sound`;
`Formalization/Pipeline/Trace_Analysis_Sound.thy` — `trace_analysis_sound`.
