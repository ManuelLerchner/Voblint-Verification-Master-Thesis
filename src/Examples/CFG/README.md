# Examples / CFG

Domain-agnostic witnesses and regressions for the VIMP-to-CFG compiler and the
activation-local collecting semantics. Nothing here depends on an abstract
domain; compare with `../Sign/`, `../Interval/`, `../Parity/`, `../Mixed/` for
domain-specific procedure-call spines.

| File | Role | What |
| --- | --- | --- |
| `Example_Inc_Proc.thy` | required support | shared global-increment procedure (`inc_program`) + its run-to-collecting witness lemmas; reused wherever an example needs a small interprocedural program with a concrete run-to-collecting witness |
| `Example_Compile_Baseline.thy` | required support | executable structural-successor diagnostics (`succ_list`) for the compiled CFG, recorded as a baseline ahead of compiler changes |
| `Example_Compile_Regression.thy` | regression | procedure layout and compiler invariants |
| `Example_Control_Simulation_Regression.thy` | regression | located execution and source/CFG control simulation |
| `Example_LTR_Collect_Regression.thy` | regression | nested calls, multiple returns, recursion, and local-trace collecting semantics |
| `Example_Proc_Recursion_CFG.thy` | regression | direct and mutual recursive CFG layout (`proc_layout_regression_blocks`) |
| `Example_VIMP_Proc_Regression.thy` | regression | source call, return, global propagation, and bounded recursion |

Role vocabulary: repository `README.md`.
