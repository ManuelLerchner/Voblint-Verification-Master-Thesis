# Examples / Executable / Common

Shared **support scaffolds** for the executable witnesses. No soundness endpoint
of their own; imported by the seeded/context runs below them.

| File | Role | What |
| --- | --- | --- |
| `Twfr_Reach_Read.thy` | required support | the `twfr_reach_read` combinator (the shipped per-coordinate soundness shape) + the domain-agnostic single-global concrete store family `gk` + `edge_step` lemmas |
| `Exec_Context_Run_Common.thy` | required support | shared two-context executable run scaffold for the entry-state context demos |

See `../../../README.md` (Examples index) and the repository `README.md`
§ Architecture for the role vocabulary and the `twf`/`twfr` witness calculus.
