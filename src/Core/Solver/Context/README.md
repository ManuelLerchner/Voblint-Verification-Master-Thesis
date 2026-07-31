# Context

Context-sensitive spine of the side-effecting solver, split by concern:

| Subfolder / File | Concern |
| --- | --- |
| `Activation/` | activation-local trace collecting (`activation_collect_sound`) and its generic backbone |
| `DG/` | D/G framework, per-key context soundness, and native analysis interpretations |
| `TD_Side_Eff_Keyed_Gen.thy` | functional keyed-global generator scaffolding (context-routed global writes), used by `DG/DG_Framework.thy` and by `Analysis/Instances/Mixed/Exec_DG_Bridge.thy` |

The generic D/G framework (`DG/`) is the public modular-analysis interface. New
analyses should use it unless they specifically require the functional keyed
generator.
