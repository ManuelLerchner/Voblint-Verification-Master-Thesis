# Voblint examples

`Voblint_Examples` is the leaf session. It contains executable runs, concrete
regressions, visualizations, and the narrative capstone. No soundness session
depends on it.

## Executable analyses

| Area | Role |
| --- | --- |
| `Executable/Sign/` | Sign-domain solver runs and D/G execution |
| `Executable/Interval/` | Interval solver runs, source certification, and activation-sensitive D/G examples |

`Example_Interval_Source_Ctx` uses the `twice` program to demonstrate two calls
to one procedure under distinct contexts. It is interprocedural,
repeated-call, and context-sensitive; it is not recursive.

## Interprocedural regressions

| File | Role |
| --- | --- |
| `Example_VIMP_Proc_Regression.thy` | Source call, return, global propagation, and bounded recursion |
| `Example_Compile_Regression.thy` | Procedure layout and compiler invariants |
| `Example_Control_Simulation_Regression.thy` | Located execution and source/CFG control simulation |
| `Example_LTR_Collect_Regression.thy` | Nested calls, multiple returns, recursion, and local-trace collecting semantics |
| `Example_Proc_Recursion_CFG.thy` | Direct and mutual recursive CFG layout |
| `Example_Inc_Proc.thy` | Source-to-CFG execution witness for a global increment |
| `Example_Side_Proc_Global.thy` | Sign analysis over a procedure call |
| `Example_Interval_Side_Proc_Global.thy` | Interval analysis over a procedure call |
| `Example_Mixed_Flow_Sign.thy` | Mixed-flow Sign theorem instantiation |
| `Example_Proc_Call.thy` | Structural CFG example with calls |
| `Example_Side_Branch_Calls.thy` | Repeated calls from separate branches |
| `Example_Side_Execute.thy` | Minimal executable side-solver example |

## Numeric and tooling examples

`Numeric/` demonstrates guard refinement and interval loop coverage.
`Tooling/` renders procedure CFGs and mixed Sign/Interval results as GraphViz
DOT.

`Voblint.thy` imports the curated examples and presents the complete certified
pipeline.
