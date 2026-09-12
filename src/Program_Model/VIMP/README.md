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
| `VIMP_Grammar_Generated.thy` | Generated from `manifests/vimp-grammar.yaml`; never edited by hand |
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

## Source syntax

Functions use `fun name(parameters) { ... }`. Assignments use `=`, while
`==` compares integer values. Assignments, calls, checks, `skip`, and returns
end in `;`; braced `if` and `while` statements do not. Braces are mandatory.
An `if` may omit its `else`, and `else if` chains may end with or without an
`else` block. Missing branches lower to `SKIP` in the core command language;
the compiler bypasses those branches without emitting a no-op node.

Comparisons are `<`, `<=`, `>`, `>=`, `==`, and `!=`, each represented by its
own expression constructor and evaluated to integer `0` or `1`. Relational
operators (`<`, `<=`, `>`, `>=`) bind more tightly than equality (`==`, `!=`),
as in C. Arithmetic binds more tightly, and `&&`/`||` less tightly. Each
comparison group is non-associative: chains within a group require parentheses.
The numeric domains handle each operator in expression evaluation, check
queries, and backward guard refinement.

Arithmetic supports `+`, `-`, `*`, `/`, and `%` over unbounded integers.
Multiplication, division, and remainder share one left-associative precedence
level. Division truncates toward zero; a nonzero remainder has the dividend's
sign. VIMP keeps expressions total with `a / 0 = 0` and `a % 0 = a`.
These zero-divisor cases are VIMP conventions, not C semantics.

The CLI separately reports possible or definite zero divisors from the solved
abstract states. This diagnostic layer leaves expression values and procedural
execution unchanged. It visits every `/` and `%` occurrence, including both
operands of `&&` and `||`; there is no short-circuit suppression. Thus
`0 && 1 / 0` has value `0` and still receives a division-by-zero diagnostic.
Unreachable program points produce no arithmetic diagnostics. The extractor
and its correctness interface live in
[`Arithmetic_Diagnostics.thy`](../../Executable_Surface/CLI/Arithmetic_Diagnostics.thy),
above this language session.

The domains evaluate division and remainder directly. Interval computes endpoint
bounds for finite division ranges and refines remainder ranges using the dividend
and divisor. Unbounded division ranges can return top. Sign retains weak signs;
Parity preserves parity for remainder by even divisors. Congruence computes exact
singleton results and retains modular information in other remainders. Int combines
and reduces these component results. Backward filtering checks forward feasibility
but does not invert division or remainder into constraints on their operands.

`global x, y;` declares shared variables. Every other variable name is local
to its activation, including an assignment's destination; local declarations
are implicit. `main` completes by falling through and cannot contain a return.
