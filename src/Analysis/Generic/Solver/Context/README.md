# Context

Context-sensitive spine of the side-effecting solver, split by concern:

| Subfolder | Concern |
| --- | --- |
| `Activation/` | activation-local trace collecting (`activation_collect_sound`) and its generic backbone |
| `DG/` | D/G framework, per-key context soundness, and the retained analysis interpretation |
| `Read/` | functional keyed-global generator scaffolding (context-routed global writes) |
