# Codegen

One theory, one command: `export_code` over the CLI surface, into OCaml.

`Voblint_Codegen` is the only session that runs the code generator, and it is the last
one built. That has a consequence worth knowing: **a change that lands a new theory
without regenerating `codegen/generated/` leaves the breakage for whoever next runs a
full build**, because nothing earlier in the graph exercises the export.

## What is exported

Six modules. Four because the handwritten OCaml under `cli/` names them, two because
they are HOL's own serializer preludes:

| Module | Contents |
| --- | --- |
| `Core` | everything else, folded together by the `code_identifier` block in `Voblint_CLI.Analyse_Dispatch` |
| `Analysis_Config` | `mk_analysis_config`, `valid_analysis_config` |
| `Analyse_Dispatch` | `analyse_config`, `analyse_config_ctx`, `analyse_config_with_state`, `abstract_value` |
| `State_Report_GraphViz` | the `*_graph_snapshot_auto` / `*_export_auto` / `*_payload_auto` renderer entry points |
| `Bit_Shifts`, `Str_Literal` | HOL runtime support, not project theories |

`scripts/check_codegen_modules.py` holds the same six names; keep the two in step.

## What the proof attaches to

`export_code` translates the executable equations of `analyse` and everything it
transitively calls, down to the solver. It is not proving one function and shipping a
different hand-written one: the generated `analyse` *is* a translation of the equations
the soundness theorems are proved about. The proof term is erased, as in any
`export_code` use; what survives is the identity of the constant.

## Checks

| Command | What it catches |
| --- | --- |
| `pixi run codegen` | regenerates `codegen/generated/` |
| `pixi run codegen-check` | fails if the checked-in export has drifted from the theories |
| `pixi run codegen-modules` | fails, naming the theory, if a new theory is missing from the `code_identifier` map — no Isabelle needed |
| `pixi run codegen-regression` | compiles the generated OCaml with `ocamlfind ocamlopt` and runs a driver that builds a program purely through the exported constructors, checking results against values Isabelle already proves |

The generated source is tracked. Regenerating it is part of any change that adds or
moves a theory reachable from the export root — a moved definition changes serialization
order even when the emitted code is behaviourally identical.
