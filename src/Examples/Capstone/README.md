# Examples / Capstone

The final integration session, `Voblint_Examples`. It is parented on
`Voblint_Examples_CLI` and lists every other example session, so the narrative
index can cite the complete verified development without putting examples on
the production or code-generation path.

| File | Role | What |
| --- | --- | --- |
| `Example_End_To_End_Certificate.thy` | acceptance certificate | Discharges every premise of `run_voblint_certified_source_sound` for one product-domain, call-string configuration |
| `Example_Non_Vacuity.thy` | non-vacuity and falsification | Satisfies the premises of `run_voblint_certified_source_sound` and `run_voblint_dead_check_unreached` for concrete programs, and shows which obligations are load-bearing by counterexample |
| `Voblint.thy` | narrative capstone | Imports the curated examples and presents the complete certified pipeline |

The certificate lives here because its subject is the assembled analyzer's
final source-level theorem. Dispatcher, result-table, and rendering regressions
remain in `../CLI/`.

Role vocabulary: repository `README.md`.
