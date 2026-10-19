# Examples / CLI

The witnesses that reach the public `run_voblint` operation. This folder is its own
session, `Voblint_Examples_CLI`, and the parent of `Voblint_Examples`.

| File | Role | What |
| --- | --- | --- |
| `Example_Run_Voblint_Regression.thy` | regression | `run_voblint` on the programs the generated OCaml module's regression driver runs, pinned by evaluation |
| `Example_Run_Voblint_Precision.thy` | regression | the precision a configuration buys: refinement, context, overflow semantics |
| `Example_Sign_Mixed_Flow.thy` | witness | program globals on the shared channel, through `run_voblint`, sound end to end for one program |
| `Cooperation_Regression.thy` | regression | two analyses that answer each other's queries through the combined state |

Role vocabulary: repository `README.md`.
