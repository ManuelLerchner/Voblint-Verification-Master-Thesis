# Examples / CFG

Domain-agnostic witnesses and regressions for the VIMP-to-CFG compiler and the
activation-local collecting semantics. Nothing here depends on an abstract
domain; compare with `../Sign/`, `../Interval/`, `../Parity/`, `../Int/` for
domain-specific procedure-call spines.

| File | Role | What |
| --- | --- | --- |
| `Example_Compile_Call_Free.thy` | required support | the shared call-free program every domain's flagship run is stated over |
| `Example_Inc_Proc.thy` | required support | shared global-increment procedure (`inc_program`) + its run-to-collecting witness lemmas; reused wherever an example needs a small interprocedural program with a concrete run-to-collecting witness |
| `Example_Compile_Regression.thy` | regression | procedure layout, compiler invariants, and the rejection of runtime-only `Restore`/`Unwind` bodies |
| `Example_Control_Simulation_Regression.thy` | regression | located execution and source/CFG control simulation |
| `Example_LTR_Collect_Regression.thy` | regression | nested calls, multiple returns, recursion, and local-trace collecting semantics |
| `Example_VIMP_Proc_Regression.thy` | regression | source call, return, global propagation, and bounded recursion |

The dispatcher, result-table and min/max regressions import
`Voblint_CLI.Analyse_Dispatch`, so they live in `../CLI/`.

Role vocabulary: repository `README.md`.
