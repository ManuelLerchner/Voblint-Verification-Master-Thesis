# Codegen

One theory, one command: `export_code` over the CLI surface, into OCaml.

`Voblint_Codegen` is the only session that runs the code generator, and it is the last
one built. That has a consequence worth knowing: **a change that lands a new theory
without regenerating `codegen/generated/` leaves the breakage for whoever next runs a
full build**, because nothing earlier in the graph exercises the export.

## What is exported

Three modules. One holds the whole generated program, because the export declares
`module_name Generated`; the other two are HOL's own serializer preludes:

| Module | Contents |
| --- | --- |
| `Generated` | the entire reachable program: entry points, domains, solver, CFG, VIMP AST |
| `Bit_Shifts`, `Str_Literal` | HOL runtime support, injected as literal target code |

`scripts/check_codegen_modules.py` holds the same three names; keep the two in step.

The generated internals are monolithic, and the export says so. Letting the serializer
split by theory does not work here: OCaml's single-file output emits modules in
dependency order and cannot express a cycle, while the executable state, the solver and
the CFG instantiation depend on each other at code level. Even a split Isabelle accepts
can fail later under `ocamlfind ocamlopt`, on a type-class dictionary field that
module-signature inference does not expose across the new boundary. Modularity belongs
in a handwritten OCaml facade over `Generated`, which this project does not yet have.

## What the proof attaches to

`export_code` translates the executable equations of `run_voblint` and everything it
transitively calls, down to the solver. It is not proving one function and shipping a
different hand-written one: the generated `run_voblint` *is* a translation of the
equations the soundness theorems (`Analysis_Run_Sound` through `Analysis_Certified`) are
proved about. The proof term is erased, as in any
`export_code` use; what survives is the identity of the constant.

## Checks

| Command | What it catches |
| --- | --- |
| `pixi run codegen` | regenerates `codegen/generated/` |
| `pixi run codegen-check` | fails if the checked-in export has drifted from the theories |
| `pixi run codegen-modules-check` | fails if the export emits any module but the three above — no Isabelle needed |
| `pixi run codegen-api-check` | fails if handwritten OCaml names something the export hides — no Isabelle needed |
| `pixi run codegen-regression` | compiles the generated OCaml with `ocamlfind ocamlopt` and runs a driver that builds a program purely through the exported constructors, checking results against values Isabelle already proves |

The generated source is tracked. Regenerating it is part of any change that adds or
moves a theory reachable from the export root — a moved definition changes serialization
order even when the emitted code is behaviourally identical.
