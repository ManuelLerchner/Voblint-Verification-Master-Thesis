# DG

D/G framework, context-sensitive soundness, and retain analysis.

| File | Role |
| --- | --- |
| `DG_Framework.thy` | heterogeneous DG framework core + seeded keyed generator |
| `DG_Soundness.thy` | heterogeneous DG soundness (unit context) |
| `DG_Context_Soundness.thy` | context-keyed accessors + per-context collecting soundness (`collect_sound_reader`, `dg_postfix_c_collect_sound`) |
| `DG_Ctx_Activation.thy` | DG-native discharge of the activation obligations (`activation_collect_sound`) |
| `Retain_Analysis.thy` | retain analysis on the DG interface |
