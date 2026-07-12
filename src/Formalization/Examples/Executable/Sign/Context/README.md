# Examples / Executable / Sign / Context

Sign **entry-state context** runs. The `Gen` run carries the proved semantic
endpoint; the others are `eval`-only precision witnesses.

| File | Role | What |
| --- | --- | --- |
| `Exec_Sign_Ctx_Gen_Run.thy` | required support | generator-driven context analysis on a compiled CFG; `gctx_executable_post_fixpoint_sound_at_ctx_semantic` (executable + semantic endpoint) |
| `Exec_Sign_Ctx_Run.thy` | precision comparison | `eval`-only witness that entry-state contexts are strictly more precise than flat analysis |
| `Exec_Sign_Ctx_Seeded_Run.thy` | precision comparison | frame-entry context seeding; `eval`-only sharper-than witness |

Proved entry-context endpoint: `TD_Side_Eff_Ctx_Sound.semantic_entry_store_ctx_analysis_sound`.
Role vocabulary: repository `README.md` § Architecture.
