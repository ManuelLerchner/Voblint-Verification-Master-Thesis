# VIMP

This session defines the whole source language Voblint analyzes: a scalar
procedural language over machine integers. Procedures have parameters, explicit
calls and returns, global/local store separation, and a frame-stack small-step
semantics.

There is one language at two levels. The parser builds *surface VIMP*
(`src_exp`, `src_com`, `imp_prog`) over variable names. *Elaboration*
(`elaborate`, `elab_com`, `elab_ptable`) resolves each name to a variable identity
`var_id`, gives every node a machine kind `ikind`, and makes C's implicit conversions
explicit, producing *core VIMP* (`exp`, `com`). The canonical step relation `pstep`
executes core VIMP; it is the instance of the generic `vimp_sem.gpstep` at `eval`,
`is_global`, the return slot `ReturnVar` and `kind_conv`, the conversion to the
destination's kind on every write. Surface VIMP has no semantics of its own: a
surface program means the core semantics of its elaboration. That is a definition,
part of the adequacy argument, not a proved transformation.

| File | Role |
| --- | --- |
| `Machine_Kind.thy` | the kinds `I8` ... `U64`, their ranges, `ik_norm` (wraparound into a kind), promotion and the usual arithmetic conversions |
| `VIMP_Syntax.thy` | surface expressions `src_exp`, variable names and surface stores |
| `VIMP_Globals.thy` | locals/globals classifier: fresh callee stores and caller/callee store combination |
| `VIMP_Expr.thy` | C division and remainder (`c_div`, `c_mod`), `truthy`, `src_aval`, an unbounded-integer evaluator of surface expressions that no step relation uses, and `lits_fit` |
| `VIMP_Special.thy` | special-call vocabulary (`__voblint_nondet_int`, `min`, `max`) |
| `VIMP_Proc.thy` | the command syntax `gcom` generic in annotation, variable and expression type; declarations, frames, the generic step rules `vimp_sem.gpstep`, well-formedness |
| `VIMP_Program.thy` | the `imp_prog` record and program-level lookups |
| `Var_Id.thy` | variable identities `var_id` (`GlobalId`, `ScopedId`, `ReturnId`, `ReturnVar`), name resolution, kind environments `kenv` and stores `store = var_id ⇒ int` |
| `Core_Exp.thy` | core expressions `exp`, their evaluation `eval`, kinds and typing, and `elaborate` from `src_exp` |
| `Core_Com.thy` | core commands `com`, `elab_com`, typing, and `kind_decls`/`kenv_of` (an undeclared identity is `I32`) |
| `VIMP_Semantics.thy` | `init_stores` (globals zero, every value in its kind), `kind_conv`, the canonical `pstep`, and `elab_ptable` |
| `VIMP_Grammar_Generated.thy` | Generated from `manifests/vimp-grammar.yaml`; never edited by hand |
| `VIMP_Notation.thy` | The `imp` and `program` quotations |

## Procedure behavior

`Call i dst p args` evaluates the actual parameters in the caller, initializes a
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

`declared_global` classifies which names have global storage; every other name is
local to the active procedure. Elaboration resolves a global to `GlobalId x` and a
local of procedure `q` to `ScopedId q x`. This source-level split is independent of
abstract D/G placement. `enter_state` keeps globals and clears locals.
`combine_env caller callee` restores caller locals and keeps callee globals.

## Source syntax

Functions use `fun name(parameters) { ... }`. Assignments use `=`, while
`==` compares integer values. Assignments, calls, checks, `skip`, and returns
end in `;`; braced `if` and `while` statements do not. Braces are mandatory.
An `if` may omit its `else`, and `else if` chains may end with or without an
`else` block. A missing branch becomes `SKIP`;
the compiler bypasses those branches without emitting a no-op node.

Comparisons are `<`, `<=`, `>`, `>=`, `==`, and `!=`, each represented by its
own expression constructor and evaluated to integer `0` or `1`. Relational
operators (`<`, `<=`, `>`, `>=`) bind more tightly than equality (`==`, `!=`),
as in C. Arithmetic binds more tightly, and `&&`/`||` less tightly. Each
comparison group is non-associative: chains within a group require parentheses.
The numeric domains handle each operator in expression evaluation, check
queries, and backward guard refinement.

Arithmetic supports `+`, `-`, `*`, `/`, and `%` on machine integers. Every operation
computes at its kind and wraps (`ik_norm`), signed or not; whether a signed overflow
is reported is the analyzer's concern, not the semantics'. Multiplication, division,
and remainder share one left-associative precedence level. Division truncates toward
zero; a nonzero remainder has the dividend's sign. VIMP keeps expressions total with
`a / 0 = 0` and `a % 0 = a`. These zero-divisor cases are VIMP conventions, not C
semantics. A well-formed program writes no literal outside `I64` (`lits_fit`).

The CLI separately reports arithmetic diagnostics from the solved abstract states:
division by zero, signed overflow, and conversions that may not fit. This layer
leaves expression values and procedural execution unchanged. It visits both operands
of `&&` and `||`; there is no short-circuit suppression. Thus `0 && 1 / 0` has value
`0` and still receives a division-by-zero diagnostic. The obligations live in
[`Run_Report.thy`](../../Executable_Surface/CLI/Run_Report.thy), above this language
session.

Kinds are declared in the source (`global u8 g;`, `fun u16 f(u8 n) { u8 x; ... }`);
the parser hands them to `run_voblint` as `kind_decls`. A local declared without an
initializer reaches Isabelle as the call `x = __voblint_nondet_int()`. The parser
resolves block scoping: a declaration that shadows a name gets a fresh name, and every
use names the innermost declaration in scope. Both are trusted parser behaviour, not
theorems.
