# Examples / CLI

The witnesses that reach the CLI layer: a domain's codegen entry point
(`Voblint_CLI.Sign_Entry` and its siblings), the `AnalysisConfig` dispatcher,
or the GraphViz render surface.

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
| `Example_Side_Execute.thy` | canonical spine | the smallest certified sign IP run, on `x := 1` (`x1_certified_sound`, `x1_explicit_completed_run_covered`) |
| `Example_Checks_Store_Only.thy` | acceptance | `__voblint_check(...)` discharged node-locally against a computed Sign post-solution: one proved, one refuted, one unknown |
| `Example_Interval_Checks_Store_Only.thy` | acceptance | the Interval member of the same trio, inside a two-sided bound guard |
| `Example_Parity_Checks_Store_Only.thy` | acceptance | the Parity member: `y := x * 2` is even and `z := y + 1` odd whatever `x` is, a fact neither Sign nor Interval expresses |
| `Exec_Interval_Run.thy` | precision comparison | `Example_Interval_Loop_Coverage`'s `loop_prog` under three fixpoint engines — bounded Kleene, warrowing TD, and every update rule at once (`join` / `per_origin` / `warrow`); interval narrowing plus the backward guard filter recover `[0,20]` under all of them. Imports the coverage theory rather than restating the program |
| `Example_Int_Refinement_Mode_Regression.thy` | regression | the `int_dom` refinement modes reached through `analyse_config`, not through the domain's own primitives |
| `Example_Analysis_Dispatch_Regression.thy` | regression | `analyse_config` over the selectable domains and context policies |
| `Example_Analysis_Result_Regression.thy` | regression | the published result table: per-point reachability and the per-context lookup surface |
| `Example_Min_Max_Regression.thy` | acceptance | `Min`/`Max` special calls end to end through the dispatcher |
| `Example_EntryState_GraphViz_Regression.thy` | regression | internal well-formedness (`analysis_graph_wf`) and result-table coverage for the context-expanded graph; the rendering itself is covered CLI-observably under `tests/regression/11-graph-snapshot/` |

Role vocabulary: repository `README.md`.
