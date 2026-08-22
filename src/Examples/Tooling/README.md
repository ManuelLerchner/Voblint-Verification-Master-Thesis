# Examples / Tooling

Domain-independent witnesses that do not belong to any one domain folder:
the contextual GraphViz surface, the solver's generator-layer buffering
regressions, and the strategy-tree language on its own.

| File | Role | What |
| --- | --- | --- |
| `Example_EntryState_GraphViz_Regression.thy` | regression | the two entry-state rendering paths — full-state via `point_state_node_annotation`, and the check-report surface — read back off the solved result table |
| `Example_Keyed_Solver_Update_Rule_Regression.thy` | regression | the keyed-generator instance of the same, at `side_cfg_T_eff_keyed_seed_dg`'s interface |
| `Example_Strategy_Tree_Demo.thy` | demo | `strategy_tree` as a small dependency/effect language with no abstract domain, CFG, or context in play |

Plain DOT rendering has no witness here. `raw_cfg_dot_lit` and
`state_report_dot` (`Voblint_CLI.State_Report_GraphViz`) assert nothing a
build-time render could check, so their coverage lives in the executable
corpus instead: `tests/regression/08-tooling/` for `--dot`,
`13-full-state-dot/` for per-node state labels, and `11-graph-snapshot/` for
golden cluster/node/edge snapshots including a recursive procedure. Those
compare output; a render into the build log only proves it did not crash.

Role vocabulary: repository `README.md` § Architecture.
