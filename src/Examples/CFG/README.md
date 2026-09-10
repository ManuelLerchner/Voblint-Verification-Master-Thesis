# Examples / CFG

Domain-agnostic witnesses and regressions for the VIMP-to-CFG compiler and the
activation-local collecting semantics. Nothing here depends on an abstract
domain; compare with `../Sign/`, `../Interval/`, `../Parity/`, `../Int/` for
domain-specific procedure-call spines.

| File | Role | What |
| --- | --- | --- |
| `Example_Compile_Call_Free.thy` | required support | `no_proc_call`, the syntactic condition for a call-free source, and `compile_prog_calls_empty`, the theorem that such a source compiles to a graph with no call edges; each importer states its own program and reuses the theorem |
| `Example_Inc_Proc.thy` | required support | shared global-increment program (`inc_program`) with its source-run and compiled-run witnesses; imported by the `Voblint` capstone |
| `Example_Compile_Regression.thy` | regression | procedure layout, compiler invariants, and the rejection of runtime-only `Restore`/`Unwind` bodies |
| `Example_Control_Simulation_Regression.thy` | regression | located execution and source/CFG control simulation |
| `Example_LTR_Collect_Regression.thy` | regression | nested calls, multiple returns, recursion, and local-trace collecting semantics |
| `Example_VIMP_Proc_Regression.thy` | regression | source call, return, global propagation, and bounded recursion |

The dispatcher, result-table and min/max regressions import
`Voblint_CLI.Analyse_Dispatch`, so they live in `../CLI/`.

Role vocabulary: repository `README.md`.
