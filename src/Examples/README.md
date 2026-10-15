# Voblint examples

The examples are the leaf of the proof-session chain: executable runs, concrete
regressions, and the capstone. Nothing depends on them -- `Voblint_Codegen`'s parent
is `Voblint_CLI`, not an example session -- so every minute they cost buys
verification and exposition only.

| Session | Folder | Parent |
| --- | --- | --- |
| `Voblint_Examples_CFG` | `CFG/` | `Voblint_Compile` |
| `Voblint_Examples_CLI` | `CLI/` | `Voblint_CLI` |
| `Voblint_Examples` | `Capstone/` | `Voblint_Examples_CLI` |

Making `Voblint_Examples_CLI` the capstone's parent rather than a listed session
matters: theories imported from an ancestor come from that session's heap, while
theories from a merely listed session are re-elaborated in the importer.

| Folder | Contents |
| --- | --- |
| `CFG/` | domain-agnostic compiler witnesses, and regressions on VIMP syntax and semantics, compiled edges, elaboration and the elaborated graph |
| `CLI/` | witnesses through `run_voblint`: regressions shared with the generated OCaml driver, precision per analysis and option, program globals on the shared channel, and cooperating analyses |
| `Capstone/` | the published theorems are not vacuous, and their premises are load-bearing |

Per-domain regressions that run one analysis inside Isabelle sit in the domain's own
session (`Interval_Regression`, `Congruence_Regression`, `Int_Regression`,
`Order_Regression`).

## What does not live here

A `value` or `ML_val ... writeln` runs the analyzer at build time and asserts
nothing, so a green build proves only that the code generator produced something
that ran. These sessions contain none. Anything worth pinning is a `by eval` lemma;
anything only observable as output -- rendered DOT, a report's text -- is pinned by
the executable corpus under `tests/regression/`, which runs the same analysis through
the code-generated CLI and compares the result.
