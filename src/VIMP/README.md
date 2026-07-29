# VIMP

This session defines the scalar procedural source language used by Voblint.
Procedures have parameters, explicit calls and returns, global/local store
separation, and a frame-stack small-step semantics.

| File | Role |
| --- | --- |
| `VIMP_Syntax.thy` | Arithmetic and Boolean expressions plus structured base commands |
| `VIMP_Expr.thy` | Expression evaluation |
| `HOL_IMP_Countable.thy` | Countability instances for wrapped HOL-IMP expression types |
| `VIMP_Globals.thy` | Global-variable convention, fresh callee stores, caller/callee state combination |
| `VIMP_Proc.thy` | Procedural commands, declarations, frames, small-step execution, and source syntax predicates |
| `VIMP_Notation.thy` | Concrete command syntax used by theories and examples |
| `VIMP_Source_Print.thy` | Executable source pretty-printer |

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

A variable is global when its name is empty or begins with `G`. `enter_state`
keeps globals and clears locals. `combine_states caller callee` restores caller
locals and keeps callee globals.
