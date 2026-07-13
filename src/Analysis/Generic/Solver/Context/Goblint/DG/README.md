# DG

D/G framework and retain analysis.

| File | Role |
| --- | --- |
| `DG_Framework.thy` | heterogeneous DG framework core |
| `DG_Soundness.thy` | heterogeneous DG soundness (unit context) |
| `DG_Context_Soundness.thy` | context-keyed accessors + per-context collecting soundness (`collect_sound_reader`, `dg_postfix_c_collect_sound`) |
| `DG_Route_Soundness.thy` | carrier-agnostic context-sliced backbone (`collect_ctx_sound_meaning`) + DG endpoint over digest-sliced `cfg_collect_ctx` (`dg_collect_ctx_sound`) — the DG replacement for the homogeneous `side_cfg_T_eff_cmp_collect_ctx_sound_semantic` |
| `Retain_Analysis.thy` | retain analysis on the DG interface |
