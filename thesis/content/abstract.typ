#import "../lib/stats.typ": stat

= Abstract <abstract>

Abstract interpretation is a static program analysis technique that
over-approximates every execution of a program. One way to implement it is to
reduce the program to a system of equations over abstract values and hand it
to a generic fixpoint solver. Goblint, a static analyzer for C, works this way
@vojdani16. The soundness of such an analyzer depends on every step of this
pipeline: the equations must describe the program, the solver's result must
satisfy them,
and the reported verdicts must follow from the solution. For Goblint's
top-down solver, only the middle step had been verified @stade24 @tilscher26.
The existing verification therefore stopped at the equation system: applying
it to program analysis still required a separate argument that the equations
soundly describe the program.

We show that the analysis pipeline can be verified from source executions to
the reported verdicts. We build Voblint, an Isabelle/HOL formalization of a
constraint-based, context-sensitive interprocedural analyzer for VIMP, a small
C-like language with global and local integer variables and recursive
procedures with parameters and return values. Voblint compiles the syntax
tree of a VIMP program into a control-flow graph and generates the equations
over that graph. A proved forward simulation maps source executions to
graph runs, so the main theorem covers source executions: if the solver terminates
and the analysis returns a result, that result covers every store a finite source
execution reaches, and every definite verdict there (the analyzer's answer to
a program assertion) is correct for that store, without
claiming that the assertion is reached. Further theorems show that a
check reported `DEAD` is unreachable and that reached divisors are nonzero absent a
warning.

Inspired by Goblint, the analyzer combines four
numeric domains (Sign, Interval, Parity and Congruence) and their reduced
product, with four update rules for the solver's global unknowns
and three context policies: none, bounded call strings and
entry-state contexts. The main theorem covers every combination. Isabelle's
code generator exports the verified analysis function to OCaml, which runs on the
command line and in the browser. We test this exported analyzer on a
regression suite of #stat("corpus.cases") VIMP programs. The Isabelle examples
contain #stat("eval_witnesses") proofs by evaluation, including end-to-end
analyses of concrete programs.

A context-sensitive analysis bounds the stores at each program point per
calling context, but the standard collecting semantics does not provide
context-indexed sets of stores against which to state such a bound. We
therefore develop an activation-local trace semantics. Like the local traces
of Schwarz et al. for threads @schwarz21, it describes an execution from the
perspective of one procedure activation, and the contexts an activation may carry are
determined by its trace. A totality
condition requires every reachable call to be admitted at some context, so the
per-context sets of stores together contain every reachable store.

Each domain, each context policy and the solver prove their own obligations,
and one theorem combines them for every configuration. The formalization
is modular: a new domain supplies its operations and
proofs, its registration for every policy and
update rule is generated, and after handwritten dispatch code, the main
theorem covers it.

Since the TD verification does not prove termination of the side-effecting
solver, we make no attempt at total correctness:
termination is a premise for each program, and we guarantee only partial
correctness. Several components lie outside the verification boundary, such as the
parser, Isabelle's code generator, the OCaml and WebAssembly toolchains, and
driver and rendering code. Finally, whether VIMP
captures the intended language is a modeling question no proof can settle, so
we document how it differs from C11.

