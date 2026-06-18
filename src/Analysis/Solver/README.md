# TD solver bridge (side-effecting, interprocedural)

**Main contribution:** Connect the vendored **TD side** solver (`vendor/td-verification`,
session `TD`, theory `TD_side`) to our interprocedural CFG and effectful `rhs_ip`
format. `side_analyse_ip_eff pi ps c etf bot s0 v` is proved sound against
`cfg_collect_ip` at `v` (`side_analyse_ip_eff_collect_sound_exit_pruned_gen`).

The solver rides on the **effectful** equation system `side_cfg_T_ip_eff`
(transfer functions are strategy trees that may query and side-effect named
globals). The pure single-pot equation system `side_cfg_T_ip` survives only as the
denotational substrate the `'a st` executable bridge and the shim monotonicity
lemmas are still defined against; its IP-soundness and solver-interface layers were
retired (see `docs/EFFECTFUL_TF_MIGRATION.md`).

**Theories**

| File | Role |
| --- | --- |
| `Strategy_Tree_Monad.thy` | `seqcomp_tree` (bind) + `traverse_seqcomp` / `dep_aux_seqcomp` / `sides_of_rhs_seqcomp`; `static_deps` and `seqcomp_mono` |
| `TD_Side_CFG.thy` | `restrict_local`, `restrict_global`, `side_env`; `pure_edge_tree` / `pure_combine_tree` / `etf_from_tf` shim; `trans_dep\<^sub>L` step/trans lemmas |
| `TD_Side_IP_Tree.thy` | `side_cfg_T_ip` (pure) and `side_cfg_T_ip_eff` (effectful) interprocedural strategy trees; folds `side_acc_ip` / `side_acc_ip_eff`; the `etf_from_tf` bridges |
| `TD_Side_IP_Eff_Bounds.thy` (generic `_gen`) + `TD_Side_IP_Eff_Soundness.thy` (shim for `etf_from_tf`) | monotonicity + dependency stability; TD_side preconditions `side_cfg_T_ip_eff_is_mono_eq` / `_mono_sides` / `_mono_deps` |
| `Exec_Bridge.thy` | executable `'a st` fold mirror + `fun_of_st` simulation; `part_post_solution_st_to_abs_eff` maps the `'a st` post-solution to a `part_post_solution` of `side_cfg_T_ip_eff (etf_from_tf tf)` |
| `TD_Side_IP_Eff_Sound.thy` | `post_fixpoint_sound_at_ip_eff` — a post-fixpoint of the effectful system over-approximates `cfg_collect_ip` (in `sound_effectful_transfer`) |
| `TD_Side_IP_Eff_Bounds.thy` | per-edge / per-combine post-solution bounds (`etf_combined_le_ip_eff`) and the generic TD_side preconditions (`side_cfg_T_ip_eff_is_mono_eq_gen` …) |
| `TD_Side_IP_Eff_Interface.thy` | `td_cfg_side_ip_solver_eff` locale, `side_cfg_ip_solve_dom_eff`, `side_analyse_ip_eff` (TD_side backend on `side_cfg_T_ip_eff`) |
| `TD_Side_IP_Eff_Pipeline.thy` | ties the three strands for an arbitrary `etf`: solver interface from the per-tree mono/static contract + collecting soundness from a post-solution |
| `TD_Side_IP_Eff_Soundness.thy` | standalone effectful collecting soundness with pruning: eff dependency cone (`ip_reaches_imp_trans_dep_or_eq_side_eff`, `side_ip_cone_in_vars_eff`), `side_collect_sound_ip_exit_pruned_eff`, executable `side_analyse_ip_eff_collect_sound_exit_pruned_gen` |

**External:** Algorithm correctness is in the TD session (`TD_side.partial_correctness`
/ `TD_side_mono`). This folder wires `part_post_solution` to `is_post_fixpoint_ip`
via `Constraint_System_IP_Sound`.

**Operational hypothesis (P1):** `side_cfg_ip_solve_dom_eff g etf bot s0 v` at each
queried program point. This is `TD_side.solve_dom destab_opt True (side_cfg_T_ip_eff …) v`.
Monotonicity of `side_cfg_T_ip_eff` is proved; termination gated on finite `pp` (P5).

**Soundness mechanism:** `side_analyse_ip_eff_collect_sound_exit_pruned_gen` proves
soundness at `cfg_exit` by showing every backward-reachable node from `v₀` is in the
solver's `trans_dep` cone (eff reach-cone lemma), so `part_post_solution` covers all
relevant unknowns. CFG pruning (`CFG_Prune`) restricts to the backward-reachable
subgraph.

**Downstream:** `Analysis/Domains/Sign_Side_IP_Soundness.thy` — `side_ip_sign_analysis_sound`;
`Formalization/Pipeline/Trace_IP_Analysis_Sound.thy` — `trace_ip_analysis_sound`.
