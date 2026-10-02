# Examples / Tooling

Solver- and generator-layer witnesses that are not about any one domain. They
are stated over whichever domain makes the effect visible -- usually Interval,
which is why `Voblint_Examples_Tooling` is parented on
`Voblint_Analysis_Interval` rather than on the solver.

| File | Role | What |
| --- | --- | --- |
| `Example_Keyed_Solver_Update_Rule_Regression.thy` | regression | Side buffering at `routed_node_rhs`'s interface: the buffered RHS generator terminates where issuing two Side writes per evaluation livelocks the solver |
| `Example_Per_Origin_Widening_Precision.thy` | regression | two producers, one global: warrowing after the join loses the upper bound that warrowing per origin keeps |
| `Example_Update_Rule_Steps.thy` | witness | one global fed the same contributions under each update rule, outside any solver run: the values each rule computes step by step |

Rendering has no witness here. Isabelle stops at `run_voblint`'s structured
result; DOT and HTML are produced from it by `cli/render/render_dot.ml` and `cli/render/report_dir.ml`,
outside any theory. A rendering asserts nothing a build-time render could
check, so coverage lives in the executable corpus instead:
`tests/regression/08-tooling/` for `--dot`, `13-full-state-dot/` for per-node
state labels, and `11-graph-snapshot/` for golden cluster/node/edge snapshots
including a recursive procedure. Those compare output; a render into the build
log only proves it did not crash.

Role vocabulary: repository `README.md` § Architecture.
