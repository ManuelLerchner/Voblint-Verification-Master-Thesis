# Dispatch — semantic analysis configuration

Cross-domain analysis selection, no soundness obligation. Distinct from
`Instances/Tooling/`, which renders an already-computed result; this
directory decides which computation runs.

| File | Role |
| --- | --- |
| `Analysis_Config.thy` | `analysis_config` (domain/solver/context selection), the canonical `resolve_analysis_config` legality-and-defaults resolver, and `valid_analysis_config` derived from it |
