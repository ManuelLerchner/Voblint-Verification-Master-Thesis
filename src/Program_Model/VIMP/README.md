# VIMP

This session defines the scalar procedural source language used by Voblint.
Procedures have parameters, explicit calls and returns, global/local store
separation, and a frame-stack small-step semantics.

| File | Role |
| --- | --- |
| `VIMP_Syntax.thy` | Expression datatype, variable and store types, executable orders |
| `VIMP_Globals.thy` | Locals/globals classifier: fresh callee stores and caller/callee store combination |
| `VIMP_Expr.thy` | Expression evaluation |
| `VIMP_Special.thy` | Special-call vocabulary (`nondet_int`, `min`, `max`) |
| `VIMP_Proc.thy` | Procedural commands, declarations, frames, small-step execution, well-formedness |
| `VIMP_Program.thy` | The `imp_prog` record and program-level lookups |
| `VIMP_Source_Print.thy` | Executable source pretty-printer |
| `VIMP_Grammar_Generated.thy` | Generated from `grammar/vimp.yaml`; never edited by hand |
| `VIMP_Notation.thy` | The `imp` and `program` quotations |

## Procedure behavior

`Call dst p args` evaluates the actual parameters in the caller, initializes a
fresh callee store, binds the formals of `p`, and saves the caller store and
optional destination in a frame.

`Return (Some e)` publishes the value of `e` through the reserved return
channel. `Return None` performs a void return. Both enter `Unwind`, which
discards pending commands in the current activation until `Restore` combines
callee globals with caller locals and pops the frame.

Falling off the end of a procedure is a void completion. The distinguished main
activation has no caller and therefore terminates only by fall-through; accepted
source programs contain no return in main.

`wf_source_program` checks declared call targets, arity, formal names,
reserved-variable use, return behavior, and root-return exclusion.
`wf_compile_input` adds the finite, duplicate-free procedure enumeration used
by compilation. A destination-bearing call requires a `value_providing` body:
one with no syntactic fall-through or void return and at least one value
return. Calls without a destination may ignore either kind of completion.

## Store convention

`declared_global_vars` determines which variables have global storage; every
other identifier is implicitly local to the active procedure, and
`declared_global` is the derived classifier. This source-level split is
independent of abstract D/G placement. `enter_state` keeps globals and clears
locals. `combine_env caller callee` restores caller locals and keeps callee
globals.
