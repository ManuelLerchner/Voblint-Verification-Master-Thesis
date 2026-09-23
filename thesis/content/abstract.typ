= Abstract <abstract>

Abstract interpretation is a static program analysis technique that
over-approximates every execution of a program. One way to implement it is to
reduce the program to a system of equations over abstract values and hand it
to a generic fixpoint solver. Goblint, a static analyzer for C, works this way.
The soundness of such an analyzer depends on every step of this pipeline: the
equations must describe the program, the solver must solve them, and the
reported verdicts must follow from the solution. For Goblint's top-down
solver, only the middle step had been verified @stade24 @tilscher26. To use it for program
analysis, one had to supply the equations and trust, without proof, that they
describe the program.

We show that the whole pipeline can be verified. We build Voblint, an
Isabelle/HOL formalization of a constraint-based, context-sensitive
interprocedural analyzer for VIMP, a small C-like language with global and
local integer variables and recursive procedures with parameters and return
values. Its main theorem is about the analysis function itself: if the
solver terminates and the analysis returns a result, that result covers every
store a finite source execution reaches, and every definite verdict (the
analyzer's answer to a program assertion) holds there. Further theorems
justify `DEAD` verdicts and the absence of zero divisors where no arithmetic
warning is reported. A definite verdict holds whenever a run reaches its
assertion, but it does not claim that any run does.

Inspired by Goblint, we implement the analyzer for a range of configurations. It combines the
numeric domains Sign, Interval, Parity and Congruence, and their reduced
product, with four update rules for the solver's global unknowns and three
kinds of context sensitivity: none, bounded call strings and entry-state
contexts. The main theorem covers every combination. Isabelle's code generator
exports the verified function to OCaml, which runs on the command line and in
the browser.

A context-sensitive analysis bounds the stores at each program point per
calling context, but the standard collecting semantics records no context,
so such a bound has nothing concrete to be sound against. We therefore develop
an activation-local trace semantics. Like the local traces of Schwarz et al.
for threads @schwarz21, it describes an execution from the perspective of one
procedure activation, and the calling context of an activation is read from
its trace. A totality condition ensures that no
execution is lost when executions are grouped by context. The proof then
follows the structure of the analyzer. Each domain, each context policy and
the solver prove their own obligations, and one theorem combines them for
every configuration. Machine-checked counterexamples show that weakening
selected obligations lets the analyzer report unsound results.

The guarantee is partial correctness, since solver termination is a premise
for each program. Parsing, code generation, compilation and presentation lie outside the
proof, and the adequacy of the source semantics is argued, not proved.
