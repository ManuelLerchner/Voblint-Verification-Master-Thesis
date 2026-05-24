# TD solver bridge

**Main contribution:** Connect the vendored **TD** top-down solver (`vendor/td-verification`,
session `TD`, theory `TD_plain`) to our `rhs` format, prove solver output is a
post-fixpoint (`td_analyse_post_fixpoint`), and lift to exit-point soundness per
domain (`sign_analysis_sound`, `interval_analysis_sound`).

**Theories**

| File | Role |
| --- | --- |
| `TD_CFG_Core.thy` | `make_rhs_tree`, `make_rhs`, CFG↔TD correspondence, `cfg_env_post_fixpoint` |
| `TD_Interface.thy` | `td_analyse`, `td_analyse_post_fixpoint`; imports `TD.TD_plain` |
| `TD_Soundness.thy` | `td_solver_sound`, `sign_analysis_sound`, `interval_analysis_sound` |
| `TD_Widen_Interface.thy` | Widening variant of the TD bridge (stretch) |
| `TD_WN_Interface.thy` | Widening + narrowing interface (stretch) |

**External:** Algorithm correctness is in the TD session. This folder states interface
assumptions (`TD_plain.solve_dom`, TD `reach` side conditions) and connects to
`Constraint_System_Sound`.

**Analysis configs** (`sign_analysis_config`, `ivl_analysis_config`) are in
`Pipeline/Pipeline.thy`, not here.

**Downstream:** `Pipeline/Pipeline.thy` — end-to-end invariant, path, and exit theorems.
