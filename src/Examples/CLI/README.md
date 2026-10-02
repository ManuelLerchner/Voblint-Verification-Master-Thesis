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
| `Example_Analysis_Dispatch_Regression.thy` | regression | `run_voblint` on one program across global update rules and context policies |

The final fully discharged certificate lives in `../Capstone/`. Domain-only
executable witnesses live with their domains.

Role vocabulary: repository `README.md`.
