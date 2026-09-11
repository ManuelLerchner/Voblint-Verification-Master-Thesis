# Examples / CLI

The witnesses that reach the CLI layer: the `AnalysisConfig` dispatcher, the
GraphViz render surface, or more than one domain's entry point at once.

This folder is its own session, `Voblint_Examples_CLI`, and it is the parent of
`Voblint_Examples` — the capstone imports from here, so an ancestor relationship
means those theories are built once rather than re-elaborated.

They sit together in one folder because `Voblint_CLI` is parented on
`Voblint_Analysis_Int`, so anything importing it sees every domain. Left in
their domain folders, each of those folders' sessions would inherit that
closure and the per-domain split would buy nothing. The domain folders
therefore hold what a domain can prove on its own; this folder holds what only
the assembled analyzer can.

| File | Role | What |
| --- | --- | --- |
| `Config_Matrix.thy` | regression | The generated configuration resolver's public support matrix, pinned cell by cell |
| `Dispatch_Matrix.thy` | regression | Config-driven dispatch agrees with every typed production entry point |
| `Example_Checks_Store_Only.thy` | acceptance | `__voblint_check(...)` discharged node-locally against a computed Sign post-solution: one proved, one refuted, one unknown |
| `Example_Interval_Checks_Store_Only.thy` | acceptance | the Interval member of the same trio, inside a two-sided bound guard |
| `Example_Parity_Checks_Store_Only.thy` | acceptance | the Parity member: `y := x * 2` is even and `z := y + 1` odd whatever `x` is, a fact neither Sign nor Interval expresses |
| `Example_Int_Refinement_Mode_Regression.thy` | regression | raw `int_dom` refinement interactions, their non-CLI solver-run counterparts, and production solver choices through the dispatcher |
| `Example_Analysis_Dispatch_Regression.thy` | regression | `analyse_config` over the selectable domains and context policies |
| `Example_Analysis_Result_Regression.thy` | regression | the published result table: per-point reachability and the per-context lookup surface |
| `Example_Min_Max_Regression.thy` | acceptance | `Min`/`Max` special calls end to end through the dispatcher |
| `Example_EntryState_Graph_Regression.thy` | regression | internal well-formedness (`analysis_graph_wf`) and result-table coverage for the context-expanded graph; the rendering itself is covered CLI-observably under `tests/regression/11-graph-snapshot/` |

The final fully discharged certificate lives in `../Capstone/`. Domain-only
executable witnesses live with their domains.

Role vocabulary: repository `README.md`.
