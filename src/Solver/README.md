# TD solver bridge

**Main contribution:** Connect the vendored **TD** top-down solver (`vendor/td-verification`,
session `TD`, theory `TD_plain`) to our `rhs` format. Per-program-point
`td_analyse c … v` is proved sound against `cfg_collect` at `v`
(`td_analyse_collect_sound_at` / `td_analyse_collect_sound`), then lifted to exit
soundness per domain (`td_solver_sound`, `sign_analysis_sound`,
`interval_analysis_sound`).

**Theories**

| File | Role |
| --- | --- |
| `TD_CFG_Core.thy` | `make_rhs_tree`, `make_rhs`, CFG↔TD correspondence, `cfg_path_node_in_reach` |
| `TD_Interface.thy` | Per-pp `td_analyse`, `td_env_at`, `td_analyse_eq_env_at`; imports `TD.TD_plain` |
| `TD_Soundness.thy` | `td_analyse_collect_sound_at`, `td_analyse_collect_sound`, `td_solver_sound`, domain exit soundness |
| `TD_Side_CFG.thy` | `side_cfg_T` construction, denotation, `side_collect_sound_*` (M3) |
| `TD_Side_Interface.thy` | `td_cfg_side_solver`, `side_analyse`, `side_part_post_solution_at` via `TD_side_mono` |
| `TD_Widen_Interface.thy` | Widening variant of the TD bridge (stretch) |
| `TD_WN_Interface.thy` | Widening + narrowing interface (stretch) |

**External:** Algorithm correctness is in the TD session (`TD_plain.partial_correctness`).
This folder wires partial solutions to `post_fixpoint_sound_at` in
`Constraint_System_Sound`.

**Operational hypothesis (P1):** `⋀v. TD_plain.solve_dom (make_rhs_tree …) v` at each
queried program point. Former reach hypothesis `td_cfg_in_reach` (P2) was removed with
per-pp solve (Fix B; issue #8 closed).

**Analysis configs** (`sign_analysis_config`, `ivl_analysis_config`) are in
`Pipeline/Pipeline.thy`, not here.

**Downstream:** `Pipeline/Pipeline.thy` — end-to-end invariant, path, and exit theorems.
