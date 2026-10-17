#import "../lib/stats.typ": stat
#import "../lib/figures.typ": verdict

= Abstract <abstract>

An abstract interpreter over-approximates a program's executions, so any
property that holds for the over-approximation holds in every run. Goblint, an
abstract interpreter for C, builds a control-flow graph of the program,
translates the graph into a system of equations over abstract values, and solves
that system with a generic fixpoint solver @vojdani16 @seidl26. Its guarantee
therefore depends on four conditions: a control-flow graph that simulates the
source program, equations that over-approximate its executions in every calling
context, a solver result that is a post-solution of the equations, and verdicts
that follow from that result. For Goblint's top-down solver, only the third
condition had been verified @stade24 @tilscher26.

We present Voblint, an Isabelle/HOL formalization of a context-sensitive
interprocedural analyzer. Its soundness proof covers all four conditions for
VIMP, a small C-like language with fixed-width integer variables and recursive
procedures with parameters and return values. A parsed program is translated
into core VIMP, which makes every integer type and conversion explicit, as CIL
does for Goblint @necula02. The main theorem combines the proofs of the four
conditions. It states that if the analyzer returns a report, the report covers
every store that a finite execution of the translated program reaches from an
initial store, and that every definite verdict at the corresponding program
point holds for that store. We also prove that a check reported #verdict("DEAD")
is unreachable and that an arithmetic obligation reported as an error fails
wherever its point is reached. At a point without an arithmetic warning or
error, no divisor is zero, no signed operation overflows, and no conversion
changes its value. To our knowledge, Voblint is the first mechanized analyzer
whose soundness proof connects a source semantics to a side-effecting constraint
system and its verified solver.

The main difficulty is context sensitivity. A context-sensitive analyzer
computes a separate invariant for each program point and calling context. The
collecting semantics, however, merges the stores of all calls to a procedure, so
it cannot say which stores a given context must cover. To solve this, we
introduce activation traces, inspired by the local traces of Schwarz et al.
@schwarz21. Each trace follows one procedure activation, and a context policy
decides to which contexts it belongs. If the policy admits every reachable call
in some context, the union of the per-context sets of stores equals the
collecting semantics, so splitting by context loses no execution.

The proof is modular and follows Goblint's architecture. Domains, context
policies, analyses, and the solver each have their own proof obligations, and
one soundness theorem combines them. A numeric domain only has to implement a
shared interface and prove its abstract operations sound. The framework builds
transfer functions from these operations and proves them sound once for all
domains, as in Nipkow and Klein's generic abstract interpreter @nipkow14[§13.5].
The main theorem holds for every offered choice of analysis, context policy,
placement of program globals, and treatment of signed overflow.

The analysis function is exported to OCaml, runs in a command-line interface and
a
#link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html")[browser
  playground], and is tested on #stat("corpus.cases") regression programs. Proofs
by evaluation show that the main theorem is non-vacuous on concrete programs.

The main result is partial correctness: termination of the solver is not proved.
We trust everything outside the formalization: the hand-written OCaml code,
including the parser and the rendering, Isabelle's code generator, and the OCaml
and WebAssembly toolchains. We document how VIMP differs from C11 @iso-c11.
