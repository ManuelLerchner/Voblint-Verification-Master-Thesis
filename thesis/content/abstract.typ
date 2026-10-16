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
and return values. Inside Isabelle, a parsed program is translated into core VIMP,
in which every operation carries its integer type and every conversion
inside an expression is explicit, as CIL does for Goblint @necula02. A proved forward simulation maps core
executions to runs of the control-flow graph. The main theorem states that whenever the analyzer returns
a report, the report covers every store reached by a finite execution of the
translated program from an initial store, and every
definite verdict at the corresponding program point holds for that store,
without claiming that the point itself is reached. Further theorems show that
a check reported #verdict("DEAD") is unreachable, that at a point without an
arithmetic diagnostic no divisor is zero, no signed operation overflows and no
conversion changes its value, and that an arithmetic obligation reported as an error fails wherever its point is reached. To our knowledge, Voblint is the first mechanized analyzer whose
soundness proof connects a source semantics to a side-effecting constraint system, in which evaluating one unknown may contribute to others, and its verified solver.

A central difficulty is context sensitivity. A context-sensitive analyzer
claims a separate invariant for each program point and calling context, but the
collecting semantics merges the stores of all calls of a procedure. We
introduce activation traces, inspired by the local traces of Schwarz et al.
@schwarz21, which follow individual procedure activations and determine which
executions each context represents. If a context policy admits every reachable call in some context, the union of the per-context sets of stores equals the
collecting semantics, so splitting by context loses no execution.

The formalization is modular and follows Goblint's architecture.
Domains, context policies, analyses, and the solver discharge separate proof
obligations, which are composed by a single soundness theorem. A numeric domain
proves only the soundness of its abstract value operations, and the framework
derives its transfer functions and their soundness once, as in the generic
abstract interpreter of Nipkow and Klein @nipkow14[§13.5]. The main theorem covers every combination of the offered numeric and relational analyses, context policies, placements of program globals and treatments of signed overflow.

The analysis function is exported to OCaml, runs in a command-line interface
and a #link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html")[browser playground], and is tested on
#stat("corpus.cases") regression programs. Proofs by evaluation show that the
main theorem is non-vacuous on concrete programs.

The main result is partial correctness: termination of the solver is not
proved. The parser, the code generator, the OCaml and WebAssembly
toolchains, and the rendering code remain trusted. We document how VIMP
differs from C11 @iso-c11.
