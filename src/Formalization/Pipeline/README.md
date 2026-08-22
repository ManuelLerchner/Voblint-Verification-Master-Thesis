# End-to-end pipeline

**Main contribution:** the registered analysis endpoints that turn a computed
D/G post-solution into a source-level soundness statement, and the
context-sensitive routed instances built on them.

**Theories**

| Theory | Concern |
| --- | --- |
| `Run_Analysis_Sound.thy` | `base_dg_exec_analysis`/`unit_dg_exec_analysis`: `run_source_sound` and `collect_sound` from one executable solve |
| `Source_Activation_Sound.thy` | source adequacy: a reachable VIMP configuration yields a `valid_ltr` trace, bounded at its activation context and monovariantly |
| `Sign_Exec_Ctx_Sound` siblings | per-domain routed instances at the entry-state and call-string contexts |

**Context:** every endpoint concludes over `ltr_collect` (monovariant) or
`activation_collect` (context-sensitive); both come from `sound_dg_spec` via
`dg_post_solution_collect_sound_ltr` and `activation_collect_sound`.

**Downstream:** `Voblint_CLI` packages these as the per-domain
`analyse_*_result_node_sound_for` and `analyse_*_report_sound_proved/_refuted`
wrappers the exported `analyse` API is proved against.
