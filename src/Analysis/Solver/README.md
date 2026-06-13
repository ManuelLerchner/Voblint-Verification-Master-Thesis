# TD solver bridge (side-effecting, interprocedural)

**Main contribution:** Connect the vendored **TD side** solver (`vendor/td-verification`,
session `TD`, theory `TD_side`) to our interprocedural CFG and `rhs_ip` format.
`side_analyse_ip pi ps c tf bot s0 v` is proved sound against `cfg_collect_ip` at `v`
(`side_analyse_ip_collect_sound_exit_pruned`).

**Theories**

| File | Role |
| --- | --- |
| `TD_Side_CFG.thy` | `restrict_local`, `restrict_global`, `side_env`; base locals/globals split on abstract states; `side_cfg_T` construction template |
| `TD_Side_IP_CFG.thy` | `side_cfg_T_ip` — interprocedural strategy tree; `side_rhs_ip`; `ip_reaches`, `ip_succ`; monotonicity (`side_cfg_T_ip_is_mono_eq`, `_mono_sides`, `_mono_deps`) |
| `TD_Side_IP_Interface.thy` | `side_cfg_ip_solve_dom`, `td_cfg_side_ip_solver` locale; `side_stabl_at`, `side_sigma_at`, `side_env_at`, `side_env_entry`; `side_analyse_ip`; imports `TD.TD_side` |
| `TD_Side_IP_Soundness.thy` | `ip_reaches_imp_trans_dep_or_eq_side`, `side_ip_cone_in_vars`, `side_analyse_ip_collect_sound_exit_pruned`; reach cone + pruning |

**External:** Algorithm correctness is in the TD session (`TD_side.partial_correctness`
/ `TD_side_mono`). This folder wires `part_post_solution` to `is_post_fixpoint_ip`
via `Constraint_System_IP_Sound`.

**Operational hypothesis (P1):** `side_cfg_ip_solve_dom g tf bot s0 v` at each queried
program point. This is `TD_side.solve_dom destab_opt True (side_cfg_T_ip …) v`.
Monotonicity of `side_cfg_T_ip` is proved; termination gated on finite `pp` (P5).

**Soundness mechanism:** `side_analyse_ip_collect_sound_exit_pruned` proves soundness
at `cfg_exit` by showing every backward-reachable node from `v₀` is in the solver's
`trans_dep` cone (reach cone lemma), so `part_post_solution` covers all relevant
unknowns. CFG pruning (`CFG_Prune`) restricts to the backward-reachable subgraph.

**Downstream:** `Analysis/Domains/Sign_Side_IP_Soundness.thy` — `side_ip_sign_analysis_sound`;
`Formalization/Pipeline/Trace_IP_Analysis_Sound.thy` — `trace_ip_analysis_sound`.
