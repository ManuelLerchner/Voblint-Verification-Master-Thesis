# Examples / CLI

The witnesses that reach the CLI layer: the public `run_voblint` operation, or
more than one domain's entry point at once.

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
| `Example_Checks_Store_Only.thy` | acceptance | `__voblint_check(...)` discharged node-locally against a computed Sign post-solution: one proved, one refuted, one unknown |
| `Example_Interval_Checks_Store_Only.thy` | acceptance | the Interval member of the same trio, inside a two-sided bound guard |
| `Example_Parity_Checks_Store_Only.thy` | acceptance | the Parity member: `y := x * 2` is even and `z := y + 1` odd whatever `x` is, a fact neither Sign nor Interval expresses |
| `Example_Int_Refinement_Mode_Regression.thy` | regression | raw `int_dom` refinement interactions and their non-CLI solver-run counterparts |
| `Example_Analysis_Dispatch_Regression.thy` | regression | `run_voblint` on one program across global update rules and context policies |
| `Example_Analysis_Result_Regression.thy` | regression | the published result table: per-point reachability and the per-context lookup surface |
| [Example_Arithmetic_Diagnostics_Regression.thy](Example_Arithmetic_Diagnostics_Regression.thy) | regression | Public CLI arithmetic findings: guard deduplication, dead branches, context aggregation, and eager Boolean operands |
| `Example_Min_Max_Regression.thy` | acceptance | `Min`/`Max` special calls through Parity's routed result table, and wrong-arity rejection |

The final fully discharged certificate lives in `../Capstone/`. Domain-only
executable witnesses live with their domains.

Role vocabulary: repository `README.md`.
