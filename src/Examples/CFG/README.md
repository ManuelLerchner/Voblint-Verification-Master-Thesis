# Examples / CFG

Domain-agnostic witnesses and regressions for the VIMP-to-CFG compiler and the
activation-local collecting semantics. Nothing here depends on an abstract
domain; compare with `../Sign/`, `../Interval/`, `../Parity/`, `../Mixed/` for
domain-specific procedure-call spines.

| File | Role | What |
| --- | --- | --- |
| `Example_Inc_Proc.thy` | required support | shared global-increment procedure (`inc_program`) + its run-to-collecting witness lemmas; reused wherever an example needs a small interprocedural program with a concrete run-to-collecting witness |
| `Example_Compile_Regression.thy` | regression | procedure layout, compiler invariants, and the rejection of runtime-only `Restore`/`Unwind` bodies |
| `Example_Control_Simulation_Regression.thy` | regression | located execution and source/CFG control simulation |
| `Example_LTR_Collect_Regression.thy` | regression | nested calls, multiple returns, recursion, and local-trace collecting semantics |
| `Example_VIMP_Proc_Regression.thy` | regression | source call, return, global propagation, and bounded recursion |
| `Example_Analysis_Dispatch_Regression.thy` | regression | `analyse_interval_proved_sound` fully discharged for one concrete `Check_Proved` |
| `Example_Analysis_Result_Regression.thy` | regression | `Analysis_Result`/`lookup_context`/`lookup_joined_state`/`canonicalize_lift` internals |
| `Example_Min_Max_Regression.thy` | regression | parity-preservation and wrong-arity-call rejection for min/max (the Sign/Interval verdict checks moved to `tests/regression/14-min-max/`) |

Role vocabulary: repository `README.md`.
