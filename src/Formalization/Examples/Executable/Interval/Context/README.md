# Examples / Executable / Interval / Context

Interval **entry-state context** runs. The `Gen` run carries the proved semantic
endpoint; the bare run is an `eval`-only precision witness.

| File | Role | What |
| --- | --- | --- |
| `Exec_Ivl_Ctx_Gen_Run.thy` | required support | generator-driven context analysis on a compiled CFG; instantiates the entry-context soundness endpoint |
| `Exec_Ivl_Ctx_Run.thy` | precision comparison | `eval`-only witness that entry-state contexts are strictly more precise than flat analysis |

Proved entry-context endpoint: `TD_Side_Eff_Ctx_Sound.semantic_entry_store_ctx_analysis_sound`.
Role vocabulary: repository `README.md` § Architecture.
