# Context

Context-sensitive spine of the side-effecting solver, split by concern:

| Subfolder / File | Concern |
| --- | --- |
| `Activation/` | activation-local trace collecting (`activation_collect_sound`) and its generic backbone |
| `DG/` | D/G framework, per-key context soundness, and native analysis interpretations |

The generic D/G framework (`DG/`) is the public modular-analysis interface. New
analyses should use it unless they specifically require the functional keyed
generator.
