#import "../lib/code.typ": isathm
#import "../lib/stats.typ": stat
#import "../lib/figures.typ": verdict

= Abstract <abstract>

Abstract interpretation over-approximates program executions. Goblint, a static
analyzer for C, implements it by reducing a program to a system of equations
over abstract values and solving that system with a generic fixpoint solver
@vojdani16 @seidl26. End-to-end soundness requires that the control-flow graph
simulates the source program, that the equations over-approximate its
executions in every calling context, that the solver's result satisfies the
equations, and that the reported verdicts follow from that result. For
Goblint's top-down solver, only the third step had been verified @stade24
@tilscher26.

We present Voblint, an Isabelle/HOL formalization of a context-sensitive
interprocedural analyzer for VIMP, a small C-like language with fixed-width
global and local integer variables and recursive procedures with parameters
and return values. Isabelle elaborates a parsed program into core VIMP, where
every conversion and operation width is explicit, and a proved forward
simulation maps core executions to runs of the control-flow graph. The main theorem states that whenever the analyzer returns
a report, the report covers every store reached by a finite execution of the
elaborated program from an initial store whose globals are zero, and every
definite verdict at the corresponding program point holds for that store,
without claiming that the point itself is reached. Further theorems show that
a check reported #verdict("DEAD") is unreachable, that at a point without an
arithmetic diagnostic no divisor is zero, no signed operation overflows and no
conversion changes its value, and that a refuted diagnostic fails wherever its
point is reached. To our knowledge, Voblint is the first mechanized analyzer whose
soundness proof connects a source semantics to a side-effecting constraint
system and its verified solver.

A central difficulty is context sensitivity. A context-sensitive analyzer
claims a separate invariant for each program point and calling context, but the
standard collecting semantics merges the stores of all calls of a procedure. We
introduce activation traces, inspired by the local traces of Schwarz et al.
@schwarz21, which follow individual procedure activations and determine which
executions each context represents. If a context policy admits every reachable
call in some context, the union of the per-context sets of stores equals the
standard collecting semantics, so splitting by context loses no execution.

The formalization follows Goblint's architecture closely and is modular.
Domains, context policies, analyses, and the solver discharge separate proof
obligations, which are composed by a single soundness theorem. A numeric domain
proves only the soundness of its abstract value operations, and the framework
derives its transfer functions and their soundness once, as in the generic
abstract interpreter of Nipkow and Klein @nipkow14[§13.5]. The framework offers
several numeric domains, the reduced product of intervals and congruences, a
relational order analysis, cooperating analyses, several context policies, two
placements of program globals, and two treatments of signed overflow, and the
main theorem covers every combination.

The analysis function is exported to OCaml, runs in a command-line interface
and a #link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html")[browser playground], and is tested on
#stat("corpus.cases") regression programs. Proofs by evaluation show that the
main theorem is non-vacuous on concrete programs
(#isathm("nv_source_certified")).

The main result is partial correctness: termination of the solver is not
proved. The parser with its scope resolution and kind declarations, the code
generator, the OCaml and WebAssembly
toolchains, and the rendering code remain trusted. We document how VIMP
differs from C11 @iso-c11.
