# Examples

**Main contribution:** Concrete demonstrations — procedural soundness witnesses,
CFG visualisation, coverage tests, and precision comparisons. Not imported by
pipeline theories.

**Theories**

| File | Role |
| --- | --- |
| `Example_Side_Proc_Global.thy` | `proc_global_side_sign_analysis` — sign soundness witness for a single global-increment call (`inc_pi`); uses `side_analyse_ip` + `pruns_to_ip` |
| `Example_IMP2_Coverage.thy` | Coverage test: non-terminating loop; `nloop_head_x_pos` via `reaching_global_read_sound`; exercises IP collecting on a concrete CFG |
| `Example_Proc_GraphViz.thy` | Graphviz output for the procedural CFG (`compile_prog inc_pi …`) |
| `Example_Trace_Digest_Precision.thy` | Precision comparison: `cfg_collect_trace_ip` vs flat `cfg_collect_ip` on a two-path program; shows `digest_beats_flat` — digest strictly more precise than flat sign env |

**Session entry points** (see `ROOT`): `Example_Side_Proc_Global`,
`Example_IMP2_Coverage`, `Example_Proc_GraphViz`, `Example_Trace_Digest_Precision`,
plus main target `Voblint_Formalization`.
