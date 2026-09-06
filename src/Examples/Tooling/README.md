# Examples / Tooling

Solver- and generator-layer witnesses that are not about any one domain. They
are stated over whichever domain makes the effect visible -- usually Interval,
which is why `Voblint_Examples_Tooling` is parented on
`Voblint_Analysis_Interval` rather than on the solver.

| File | Role | What |
| --- | --- | --- |
| `Example_Keyed_Solver_Update_Rule_Regression.thy` | regression | the keyed-generator instance of the same, at `routed_node_rhs`'s interface |
| `Example_Buffered_Encoding_Flush_Order.thy` | regression | the direct and buffered routed generators solved side by side under three update rules, on one program publishing a global and an activation seed from the same evaluation |
| `Example_Per_Origin_Widening_Precision.thy` | regression | two producers, one global: warrowing after the join loses the upper bound that warrowing per origin keeps |
| `Example_Strategy_Tree.thy` | demo | `strategy_tree` as a small dependency/effect language with no abstract domain, CFG, or context in play |
| `Example_TD_Side_Program.thy` | demo | Tilscher's TDside lock-set running example, through the typed `strategy_program` frontend |
| `Example_TD_Plain_Program.thy` | demo | the TD must-be-initialized running example, through the same frontend with no side effects |

The context-expanded GraphViz regression needs
`Voblint_CLI.State_Report_GraphViz`, so it lives in `CLI/`.

Plain DOT rendering has no witness here. `raw_cfg_dot_lit` and
`state_report_dot` (`Voblint_CLI.State_Report_GraphViz`) assert nothing a
build-time render could check, so their coverage lives in the executable
corpus instead: `tests/regression/08-tooling/` for `--dot`,
`13-full-state-dot/` for per-node state labels, and `11-graph-snapshot/` for
golden cluster/node/edge snapshots including a recursive procedure. Those
compare output; a render into the build log only proves it did not crash.

Role vocabulary: repository `README.md` § Architecture.
