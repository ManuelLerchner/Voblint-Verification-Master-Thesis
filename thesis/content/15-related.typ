#import "../lib/code.typ": *
#import "../lib/theme.typ": vb


= Related Work <ch:related>

@sec:state-of-art placed Voblint among unverified and mechanized analyzers by
what its theorem covers. This chapter compares mechanisms, which needs the
definitions of the preceding chapters. We compare Voblint with prior systems along three design choices: the
semantics an analyzer is proved against, how its fixpoint is computed, and how
much of the delivered tool the proof covers. Each section opens with the
question it compares and Voblint's answer, then reports each work's own claims
before relating them to this thesis. The
comparisons are based on a web and OpenAlex search with full-text reads of the
closest papers, not on a systematic review, so a work that search missed could
narrow the scoped claims below. Several comparisons depend on how the fixpoint
is formulated. Voblint is constraint-based, as Goblint is, whereas Verasco and the
analyzers of Nipkow and Klein and of Franceschino et al. are syntax-directed (@sec:why-graph).

== Verified analyzers: Verasco and the CompCert line

Can a soundness theorem be about the tool that users run? CompCert and Verasco
show how, and Voblint follows their pattern for a language with recursive
procedures and context-sensitive calls.

CompCert is a compiler from Clight, a large subset of C, to PowerPC assembly,
programmed and proved correct in Coq, now Rocq @leroy09. Its theorem is semantic
preservation: the compiled code behaves as the source semantics specifies, so
safety properties proved of the source hold for the executable. The executable
compiler is extracted from Coq to Caml and linked with handwritten, unverified
parts, and Leroy lists what remains trusted: the semantics of Clight and of the PowerPC
assembly, the unverified CIL-based parser, the assembler and the linker, and
Coq's extraction together with the Caml compiler and run-time system
@leroy09[§5]. AbsInt distributes CompCert commercially and reports its
qualification for certification projects in nuclear energy and avionics
@absint-compcert.
Voblint's guarantee has the same shape: a theorem
about the function the tool runs, code generated from the prover, and an
explicit list of trusted components (@sec:trust-boundary). Voblint's parser
corresponds to CompCert's parser, its code generator and OCaml toolchain to
the extraction and the Caml compiler, and its printing and rendering code to
the assembler and linker downstream. Compiler correctness
preserves the behaviour of a program. Analyzer soundness only over-approximates
it, so a coarser result remains sound.

Verasco is a Coq-verified analyzer for most of ISO C99, excluding recursion and
dynamic allocation, that proves the absence of run-time errors @jourdan15. Its
abstract interpreter iterates over the structure of C\#minor, a CompCert
intermediate language. Modular interfaces separate the abstract state from an
extensible combination of numerical domains, and CompCert's semantic
preservation extends the guarantee to compiled code. Functions are reanalyzed at
every call site up to a fuel bound, and a possible recursive call raises an
alarm @jourdan15[§4].

Verasco covers a far larger language, so the comparison concerns design only.
Voblint's language is small, but recursion and context-sensitive calls are
central to it: calls become equations over (program point, context) unknowns,
and a generic solver computes their solution. With fuel, Verasco needs no
termination argument. Voblint's source theorem takes termination of the solve as
a premise.
Both specify abstract operations through concretization alone.

The earlier value analysis of Blazy et al. @blazy13 does not verify
its fixpoint iterator. An untrusted OCaml implementation of Bourdoncle's
iteration strategy @bourdoncle93 computes a candidate, and a verified checker
accepts it as a post-fixpoint or falls back to top @blazy13[§4]. Voblint instead runs a
solver whose partial correctness is proved @tilscher26. The checker leaves the
iteration heuristics free and tests every result at run time. A verified solver
needs no such test, and its proof holds for that one algorithm.

CompCert hides its dataflow solvers behind a common Coq module type
@compcertKildall. A solver returns an optional map from program points to
abstract values, and clients rely on three properties: the result satisfies
the dataflow inequations (for transfer functions that map bottom to bottom),
it bounds the entry value, and it satisfies every property that holds for
bottom and for the entry value and is preserved by join and the transfer
functions. La Spina et al. @laspina25 verify in Coq two solvers based
on weak topological orderings against the same interface, and CompCert's
dataflow analyses run with them in place of its own solver. Both works are intraprocedural.
Voblint consumes its solver through a fixpoint guarantee in the same way, for
side-effecting, context-indexed systems, where the certificate
#isaconst("part_post_solution", thy: "Basics_side") also accounts for contributions to global
unknowns.

== Mechanized abstract interpretation

How have abstract interpreters been mechanized, and how are their proofs
factored for reuse? Voblint follows the design of Nipkow and Klein's generic
interpreter for its domains and splits the rest into analysis, context policy and solver.

Nipkow and Klein develop abstract interpretation in Isabelle/HOL over annotated
commands of the While language IMP @nipkow12 @nipkow14. A collecting semantics
annotates each program point with a set of states, and an abstract interpreter
annotates it with an abstract state. The development is syntax-directed and
intraprocedural. Its interpreter is parametric in a domain of abstract values:
the domain supplies abstract operations and inverse operations with their
soundness laws, and the interpreter derives forward evaluation, the backward
filtering of guards and the step of each command generically
@nipkow14[Sects. 13.5, 13.7]. Voblint's non-relational domains follow this
pattern. Each supplies one record of primitives
(#isatype("nonrelational_ops")), and #isalocale("sound_nonrelational_ops")
derives the transfer, branch, entry and check classifier from it and proves
them sound once (@sec:instances-supply). Voblint keeps the separation between collecting semantics and
abstraction. Its collecting semantics ranges over activation traces of a
procedure-aware control-flow graph (@ch:traces), because a return must know
which caller resumes. Their executable abstract state lists some variables and
reads every other variable as top; they call the map from such a list to the
function it represents `fun_rep` @nipkow14[§13.6]. Voblint's executable state also lists only
some names, but it needs two defaults, because the states it stores fill
unlisted names in two ways: the entry state reads every unlisted global as
zero, and the global half of a published state reads every local as bottom
(@sec:represented-function).

IMP2 @lammich19imp2, an Isabelle language with procedures, did not fit: its
semantics is deterministic, a procedure call takes no arguments and returns no
value, so parameters pass through variables set by generated code, and its
verification condition generator handles recursive procedures only for total
correctness (@sec:vimp).

Three works factor the soundness proof of an analyzer for reuse.
Michelland et al. @michelland24 build abstract interpreters in Coq from
monadic handlers stacked over a free monad: abstract control-flow combinators
are proved sound once against their concrete counterparts, and each effect
handler has an abstract variant with its own soundness condition.
Keidel et al. @keidel18 share one interpreter between the concrete and
the abstract semantics, parameterized over an arrow-based interface, and reduce
its soundness to lemmas about the two instances of that interface.
Darais et al. @darais15 make context, path and heap sensitivity monad
transformers that are proved sound once, on paper, and composed into an
analyzer. In Voblint, the soundness proofs of a non-relational domain's primitives play a
similar role for the generic transfer builder, which follows the design of
Nipkow and Klein. The analysis
specification it yields instantiates the equation generator of @ch:equations,
and the solver is a third, separately verified component.

#cite(<cachera10>, form: "prose") program and prove in Coq an abstract
interpreter for a While language without procedures. It iterates over the
syntax with widening and narrowing, is proved correct through an intermediate
collecting semantics defined with a generic least-fixpoint operator, and is
extracted to OCaml @cachera10[§§1, 6]. Voblint uses the same stepping stone, a
collecting semantics between execution and abstraction, but over
activation traces of a graph and with a separately verified solver
instead of a syntax-directed iterator.

Franceschino et al. @franceschino21 verify a syntax-directed abstract
interpreter for a small imperative language in F\*, using refinement types and
SMT automation instead of interactive proof. Their analyzer runs in a browser,
and Verasco ships an extracted command-line analyzer @jourdan15, so an
executable or interactive verified analyzer is not new with this thesis.

Interprocedural analyses have been verified in Isabelle before, without a
context abstraction. #cite(<lammich07afp>, form: "prose") prove soundness and
precision of a constraint-based conflict analysis for programs with recursive
procedures, thread creation and monitors; their flowgraph semantics abstracts
guarded branching by nondeterminism but interprets calls and returns exactly.
#cite(<wasserrab09afp>, form: "prose") proves the two-phase interprocedural
slicer of Horwitz, Reps and Binkley correct over an abstract control-flow graph
with matched calls and returns, instantiated for a While language with
procedures. #cite(<breitner10afp>, form: "prose") formalizes Shivers'
control-flow analysis for a continuation-passing functional language in
Isabelle/HOLCF and proves it correct with respect to an exact nonstandard
semantics. There the analysis is parametric in its contours through a type
class, which plays the role a context policy plays here. None of the three
entries claims an extracted analyzer. Code generated from an Isabelle proof has
replaced an unverified compiler component before:
Buchwald et al. @buchwald16 define SSA construction over an abstract
control-flow graph fixed by a locale, instantiate it for a While language, and
replace the SSA construction of CompCertSSA by OCaml code extracted from a
further instantiation.

None of the Isabelle semantics above represents one activation with its caller
chain, the object Voblint's context relation reads. The factorings above share
an interpreter, a handler stack or a monad stack between the concrete and the
abstract semantics. Voblint mechanizes a three-way split between analysis,
context policy and solver for a constraint-based analyzer, with one composition
theorem, #isathm("activation_collect_dg_sound"), instantiated for every shipped
analysis configuration. Lammich and Müller-Olm prove precision of their analysis for
every program. Voblint's precision statements compare two analysis settings on
one program.

== Verified fixpoint solvers <sec:rel-solvers>

What does a verified solver guarantee, and what must an analyzer add? Voblint
reuses the solver of Tilscher et al. @tilscher26 and supplies the
meaning of the equations it solves.

Hofmann et al. @hofmann10 verify the local generic solver RLD in Coq;
like the top-down solver, it records dependencies between unknowns while it
evaluates right-hand sides. Stade et al. @stade24 prove the top-down
solver partially correct in Isabelle/HOL, first for a simpler recursive
formulation and then for the optimized solver, which agrees with it on
termination and results. Tilscher et al. @tilscher26 extend the line to
mixed flow-sensitive analyses. They verify $"TD"_"side"$, which accepts
contributions to global unknowns during iteration, against a generic interface
for update rules, prove five update rules of
Stemmler et al. @stemmler25 sound, and refine the solver to executable
code. The copy Voblint vendors interprets the update-rule interface once for
each of the five rules and passes the results to the code generator. For precise updates without widening and narrowing, they also prove that
the solver returns the least partial post-solution, provided it terminates and
the equation system satisfies their monotonicity conditions.
Tilscher et al. @tilscher26jar treat the top-down solver without side
effects, extended either with warrowing or with separate widening and
narrowing phases. They prove that the warrowing variant returns partial
post-solutions and that the phased variant terminates when the set of unknowns
is finite. The two variants are equivalent under three assumptions: the widening
operator is precise, and the right-hand sides are monotonic and have monotonic
dependencies. Total correctness of both follows.

Voblint includes a copy of the solver of @tilscher26; the algorithm, the update
rules and their proofs belong to that work. The copy carries local
refactorings, such as renamings and an interface theory (@sec:upstream-td). A solver theorem speaks about
arbitrary right-hand sides and gives the equations no meaning. Voblint supplies that
meaning for its language: the certificate #isaconst("part_post_solution", thy: "Basics_side")
implies coverage of the concrete traces, and compiler correctness transfers the
coverage to source executions. The solver Voblint runs warrows every local
unknown at a widening point, whichever of the five selectable update rules
merges the global contributions. The least-solution theorem therefore does not
apply, and Voblint uses only partial correctness and claims no optimality for
its results. Soundness rests on #isaconst("part_post_solution", thy: "Basics_side") alone, for all
five selectable rules (@sec:update-rules). Voblint's precision statements are strict inequalities
between the results of named solves.

== Context sensitivity and trace partitioning

How have calling contexts been defined, and what does a relational context
add? Voblint's contexts index a collecting semantics, as trace partitioning
does, and one activation may belong to several of them.

#cite(<sharir81>, form: "prose") introduce the two classical approaches to
interprocedural analysis. The functional approach establishes input-output
relations for procedures and treats calls as super operations, and the
call-string approach tags propagated information with an encoded history of
the calls encountered, so that a return propagates only information whose
history matches @sharir81[§1]. For recursive programs, both may fail
to yield an effective solution for problems such as constant propagation
@sharir81[§1]. #cite(<knoop92>, form: "prose") extend the coincidence
theorem to recursive procedures with local variables. Their return function
combines the information before the call with the callee's exit information,
because the local variables must be reset to their values at call time
@knoop92[§4.1]. Voblint's return step has the same shape, combining the
caller's pre-call state with the callee's result (@sec:calls).
Reps et al. @reps95 solve interprocedural problems with finite fact
sets and distributive transfer functions precisely, as reachability over
interprocedurally valid paths, and state that semantic correctness is an
orthogonal issue @reps95[§2]. Voblint's domains need not be finite or
distributive, and Voblint proves no precision. It proves the semantic
correctness that these frameworks leave to the encoding.

Trace partitioning abstracts a set of traces by indexing it with control history
before abstracting states @rival07. Rival and Mauborgne define both partitions
and coverings, in which one trace may belong to several indices, and present
calling-context sensitivity as one such indexing; keeping the full stack amounts
to inlining and works only for nonrecursive calls. They also note that the
function mapping tokens to tokens in a covering may be replaced by a relation
@rival07[Rem. 3.2.4]. Voblint's context-indexed
collecting semantics is a covering of this relational kind, since a context policy may admit one activation in several contexts. Voblint mechanizes the indexing over
activation traces and proves that the solved, routed result bounds the activation
collecting semantics of every admitted context.

Contexts also determine how many unknowns a solve creates. The context lifters
of Erhard et al. @erhard25 bound the number of contexts on the fly and
guarantee finitely many contexts whenever the solver updates each unknown
finitely often @erhard25[Abstract]. Voblint's entry-state policy has no such bound, which is one reason the
termination of the solve is not proved (@sec:termination).

== Goblint, local traces, and thread-modular analysis <sec:rel-goblint>

Voblint follows Goblint's architecture and the local-trace semantics of its
research line. This section names what it adopts and where it departs.

Side-effecting constraint systems let one equation both define a local unknown
and publish contributions to global unknowns @apinis12. Seidl et al. @seidl26
describe how Goblint uses them to decouple a mixed flow-sensitive analysis from
the solver, with digests on the analysis side and update rules on the solver
side recovering precision. Voblint adopts the split: an analysis supplies local
and global transfer behaviour, and the generator and solver organize their
interaction. @sec:eval-goblint records where the model differs from Goblint's
implementation.

Goblint combines its analyses at run time. Its MCP runs every activated
analysis on its part of one combined state, meets the answers of all analyses
to a query, answers a query cycle with the top element and caches answers per
transfer, and raises `Deadcode` when one analysis finds a point unreachable
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/mCP.ml")[`mCP.ml`]
at revision `5320a6b7`). Voblint's combination of @ch:cooperation follows this
design for one query kind and for analyses without globals, and adds a proof
obligation per analysis that quantifies over every sound query channel. The
reduced product @cousot79 @rival20[§5.1.2] combines domains through a reduction
on the product carrier, as the Int domain of @sec:reduced-product does. The
combined state keeps separate carriers and exchanges facts only through
answers, so no reduction operator has to be defined or proved for a pair of
analyses. The open product of Cortesi et al. @cortesi94, designed for
logic programs, also lets each combined domain use information from the others
through queries.

Verasco combines its numerical domains through the channels of @sec:coop-channels
for the same reason: reduced products tend to be specific to the two domains
combined and scale poorly beyond two @jourdan15[§7]. The channels follow
those of Astrée @cousot07astree[§5.2]. Its
combinator threads the channels so that the second domain can query the state
the first has just computed. Voblint's answers describe the predecessor state
only, as Goblint's do. Voblint combines any list of components on the fields of
one state and proves the combination sound for calls, returns and
context-sensitive equations, where Verasco raises an alarm at a possible
recursive call.

Local traces give each thread of a concurrent program a semantics from which
thread-modular analyses can be derived and compared @schwarz21, later
extended to relational analyses @schwarz23. The digest framework uses
abstractions of execution histories to decide which observations may interact
@schwarz24digest, and #cite(<schwarz26vmcai>, form: "prose") define data races
in the same local-trace semantics. Voblint adapts the local view to sequential
procedure activations: a trace covers one activation and records its suspended
caller, so a return reads its caller from the trace instead of choosing one. A calling context becomes a
projection of the trace instead of a component of the state. Context policies can therefore be
proved against one fixed concrete semantics. Activations do not interfere, so
no concurrency result of that work transfers. We call our objects activation
traces to keep them apart from these local traces, which are a semantics of
multithreaded programs.

#cite(<sotin11>, form: "prose") also replace a stack semantics by a local one,
in which every instruction acts on the top activation record only. They prove
the two semantics equivalent with respect to reachable stacks @sotin11[§3]
and derive a
relational interprocedural analysis from the local semantics. Their motive is
pointers into the stack, which VIMP lacks. For activation traces, Voblint
proves only the direction soundness needs: every graph run is represented by a
valid trace (@sec:valid).

A digest is a total function on local traces that splits the unknowns $[u]$
into $[u, A]$ already in the concrete semantics @schwarz25phd[§2.3]. Seidl et
al. describe digests as generalizing calling contexts @seidl26[§4, p. 456]. The local-trace semantics itself
has no procedures: its programs are sets of thread control-flow graphs without
a call action, and Schwarz lists procedures among the features that Goblint
implements but the local-trace semantics does not yet support
@schwarz25phd[§8, p. 277].
In Voblint, the context relation #isaconst("activation_context_rel") (@sec:contexts)
takes the digest's place for sequential activations. It is a relation, because a context policy may admit an activation in several
contexts or in none.

Mixed flow sensitivity has been mechanized before.
Cachera et al. @cachera05 prove in Coq that a constraint-based analysis
of Carmel, an intermediate representation of Java Card bytecode, is sound with
respect to a small-step operational semantics. It keeps one flow-insensitive
heap and flow-sensitive local variables and operand stacks per program point,
is context-insensitive, and solves ordinary inequations with a verified
round-robin solver extracted to OCaml @cachera05[§§2, 3.2]. #cite(<dabrowski09>, form: "prose")
prove sound in Coq a context-sensitive points-to analysis with a
flow-insensitive heap, a component of their certified data race analyzer. They
instrument the concrete semantics with contexts through a Coq functor over a
module type of contexts, whose call-context function computes the context
of a callee from the call site, the caller's context and the receiver, and
they instantiate it, among others, with $k$-object sensitivity. The authors
state that the specification is not executable: the analyses are specified
only as sets of constraints, and no solver computes them @dabrowski09[§7]. Voblint's instance with
flow-insensitive program globals, and the exact scope of its proof, are
described in @sec:mixed-flow.

Dabrowski and Pichardie are the closest precedent for the context semantics: a mechanized
concrete semantics that carries contexts, parameterized by a context policy.
Voblint's differs in three respects. Contexts are admitted by a relation, so one call
may enter several contexts; the totality condition
#isaconst("call_context_total_on") makes the context-indexed collection
exhaustive (#isathm("node_collect_eq_Union_activation_collect")); and the
indexing is connected to an executable solver. The adaptation of local traces
to activations has no mechanized predecessor that we found.
