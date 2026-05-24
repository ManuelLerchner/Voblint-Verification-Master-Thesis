# TD solver bridge

**Main contribution:** Connect the vendored **TD** top-down solver (`vendor/td-verification`,
session `TD`, theory `TD_plain`) to our `rhs` format, prove solver output is a
post-fixpoint (`td_analyse_post_fixpoint`), and lift to `cfg_collect` soundness per domain.

**Theories**

| File | Role |
| --- | --- |
| `TD_Interface.thy` | `make_rhs_tree`, `td_analyse`, `td_analyse_post_fixpoint`; imports `TD.TD_plain` |
| `TD_Soundness.thy` | `td_solver_sound`, `sign_analysis_sound`, `interval_analysis_sound` |

**External:** Algorithm correctness is in the TD session. This folder states interface
assumptions (`TD_plain.solve_dom`, TD `reach` side conditions) and connects to
`Constraint_System_Sound`.

**Analysis configs** (`sign_analysis_config`, `ivl_analysis_config`) are in
`Pipeline/Pipeline.thy`, not here.

**Downstream:** `Pipeline/Pipeline.thy` — end-to-end invariant, path, and exit theorems.
