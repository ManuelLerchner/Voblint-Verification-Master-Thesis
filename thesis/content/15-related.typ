#import "../lib/code.typ": *
#import "../lib/theme.typ": vb
#import "../lib/alignment.typ": alignment, alignment-count


= Related Work <ch:related>

@sec:state-of-art compared Voblint by what its theorem covers, first with
unverified analyzers and then with mechanized ones (@tab:production-analyzers,
@tab:state-of-art). This chapter compares its mechanisms with the closest lines
of work: verified analyzers, mechanized abstract interpretation, verified
fixpoint solvers, context sensitivity, and Goblint together with local-trace
semantics. The comparisons are based on a web and OpenAlex search with
full-text reads of the closest papers, not on a systematic review.

== Verified analyzers: Verasco and the CompCert line

CompCert and Verasco state their theorems about the tool that users run, and
Voblint follows their pattern for a language with recursive procedures and
context-sensitive calls.

CompCert is a compiler from Clight, a large subset of C, to PowerPC assembly,
programmed and proved correct in Coq, now Rocq @leroy09. Its theorem is semantic
preservation: the compiled code behaves as the source semantics specifies, so
safety properties proved of the source hold for the executable. The executable
compiler is extracted from Coq to Caml and linked with handwritten, unverified
parts, and Leroy lists what remains trusted: the semantics of Clight and of the PowerPC
assembly, the unverified CIL-based parser, the assembler and the linker, and
Coq's extraction together with the Caml compiler and run-time system
@leroy09[§5].
Voblint's guarantee has the same shape: a theorem
about the function the tool runs, code generated from the prover, and an
explicit list of trusted components (@sec:trust-boundary). Voblint's parser
corresponds to CompCert's parser, and its code generator and OCaml toolchain to
the extraction and the Caml compiler. Compiler correctness
preserves the behavior of a program. Analyzer soundness only over-approximates
it, so a coarser result remains sound.

Verasco is a Coq-verified analyzer for most of ISO C99, excluding recursion and
dynamic allocation, that proves the absence of run-time errors @jourdan15. Its
abstract interpreter iterates over the structure of C\#minor, a CompCert
intermediate language. Modular interfaces separate the abstract state from an
extensible combination of numerical domains, and CompCert's semantic
preservation extends the guarantee to compiled code.

Verasco covers a far larger language, so the comparison concerns design only.
Voblint's language is small, but recursion and context-sensitive calls are
central to it: calls become equations over (program point, context) unknowns,
and a generic solver computes their solution. Verasco reanalyzes functions at every call site up to a fuel bound and raises
an alarm at a possible recursive call (@tab:state-of-art, @jourdan15[§4]), so it
needs no termination argument. Voblint's analyzer returns a report only where its solve
terminates, and termination is not proved for every program (@sec:termination).
Both state the soundness of abstract operations through their concretization.

The earlier value analysis of Blazy et al. @blazy13 does not verify
its fixpoint iterator. An untrusted OCaml implementation of Bourdoncle's
iteration strategy @bourdoncle93 computes a candidate, and a verified checker
accepts it as a post-fixpoint or falls back to top @blazy13[§4]. Voblint instead runs a
solver whose partial correctness is proved @tilscher26. The checker leaves the
iteration heuristics free and tests every result at run time. A verified solver
needs no such test, and its proof holds for that one algorithm.

CompCert hides its dataflow solvers behind a common Coq module type whose
clients rely only on fixpoint properties of the result @compcertKildall, and La
Spina et al. @laspina25 verify two solvers based on weak topological orderings
against it, with which CompCert's dataflow analyses then run. Both works are
intraprocedural.
Voblint consumes its solver through a fixpoint guarantee in the same way, for
side-effecting, context-indexed systems, where the certificate
#isaconst("part_post_solution", thy: "Basics_side") also accounts for contributions to global
unknowns.

== Mechanized abstract interpretation

Abstract interpreters have been mechanized in several provers, with different
ways of factoring their proofs for reuse. Voblint follows the design of Nipkow
and Klein's generic interpreter for its domains and splits the rest into
analysis, context policy and solver.

Nipkow and Klein develop abstract interpretation in Isabelle/HOL over annotated
commands of the While language IMP @nipkow12 @nipkow14. A collecting semantics
annotates each program point with a set of states, and an abstract interpreter
annotates it with an abstract state. The development is syntax-directed and
intraprocedural. Its interpreter is parametric in a domain of abstract values:
the domain supplies abstract operations and inverse operations with their
soundness laws, and the interpreter derives forward evaluation, the backward
filtering of guards and the step of each command generically
@nipkow14[Sects. 13.5, 13.7]. Voblint's non-relational domains follow this
pattern (@sec:domain-contract). Voblint keeps the separation between collecting semantics and
abstraction. Its collecting semantics ranges over activation traces of a
procedure-aware control-flow graph (@ch:traces), because a return must know
which caller resumes. Their executable abstract state lists some variables and
reads every other variable as top; they call the map from such a list to the
function it represents `fun_rep` @nipkow14[§13.6]. Voblint's executable state also lists only
some names, but with two defaults instead of one (@sec:represented-function).

Michelland et al. @michelland24, Keidel et al. @keidel18 and Darais et al.
@darais15 make soundness proofs reusable by sharing one interpreter between
the concrete and the abstract semantics, through monadic handlers, an
arrow-based interface or monad transformers. Voblint instead splits analysis, context policy and solver for
a constraint-based analyzer and composes them in one theorem,
#isathm("activation_collect_dg_sound"), instantiated for every shipped
analysis configuration.

#cite(<cachera10>, form: "prose") program and prove in Coq an abstract
interpreter for a While language without procedures, proved correct through an
intermediate collecting semantics and extracted to OCaml @cachera10[§§1, 6].
Voblint uses the same stepping stone, a collecting semantics between execution
and abstraction, but over activation traces of a graph and with a separately
verified solver instead of a syntax-directed iterator. Franceschino et al.
@franceschino21 verify a syntax-directed interpreter in F\* with SMT
automation, and their analyzer runs in a browser, so an executable or
interactive verified analyzer is not new with this thesis.

Interprocedural analyses have been verified in Isabelle before, but not with a
context-indexed collecting semantics like Voblint's. #cite(<lammich07afp>, form: "prose") prove soundness and,
for every program, precision of a conflict analysis for programs with
recursive procedures, threads and monitors, interpreting calls and returns
exactly. #cite(<wasserrab09afp>, form: "prose") proves an interprocedural
slicer correct over an abstract control-flow graph with matched calls and
returns. #cite(<breitner10afp>, form: "prose") proves Shivers' control-flow
analysis correct in Isabelle/HOLCF, parametric in its contours through a type
class, which plays the role a context policy plays here. None of these entries
claims an extracted analyzer, and none of their semantics represents one
activation with its caller chain, the object Voblint's context relation reads.
Code generated from an Isabelle proof has, however, replaced an unverified
compiler component: Buchwald et al. @buchwald16 replace the SSA construction of
CompCertSSA by OCaml code extracted from an instantiation of their locale-based
construction.

== Verified fixpoint solvers <sec:rel-solvers>

A verified solver guarantees a property of its result for arbitrary
equations, and the analyzer must give the equations their meaning. Voblint
reuses the solver of Tilscher et al. @tilscher26 and supplies that meaning.

An early Isabelle instance of a verified solver consumed through a
specification is the bytecode verifier of Klein and Nipkow @klein03bcv[§3].
A function is a bytecode verifier if it reports no error exactly when a stable,
error-free method type, a post-fixpoint of the flow functions, exists above the
initial state. Kildall's algorithm is proved to be one for every semilattice
with the ascending chain condition and monotone, bounded flow functions
@klein03bcv[Thm. 1]. Their system is finite and intraprocedural, and the
specification also demands completeness. Voblint's solver explores a
context-indexed system with side effects on demand, and Voblint uses only the
soundness direction of its certificate.

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
code. For precise updates without widening and narrowing, they also prove that
the solver returns the least partial post-solution, provided it terminates and
the equation system satisfies their monotonicity conditions.
Tilscher et al. @tilscher26jar treat the termination of the solver without
side effects; @sec:termination explains why these results do not apply to
Voblint's equations.

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
five selectable rules (@sec:update-rules).

== Context sensitivity and trace partitioning

Calling contexts have been defined by call history, by procedure summaries
and as an index of traces. Voblint's contexts index a collecting semantics, as
trace partitioning does, and one activation may belong to several of them.

#cite(<sharir81>, form: "prose") introduce the two classical approaches to
interprocedural analysis. The functional approach establishes input-output
relations for procedures and treats calls as super operations, and the
call-string approach tags propagated information with an encoded history of
the calls encountered, so that a return propagates only information whose
history matches @sharir81[§1]. For recursive programs, both may fail
to yield an effective solution for problems such as constant propagation
@sharir81[§1]. #cite(<knoop92>, form: "prose") extend the coincidence
theorem to recursive procedures with local variables. Their return function
combines the information before the call with the callee's exit information
@knoop92[§4.1]. Voblint's return step has the same shape, combining the
caller's pre-call state with the callee's result (@sec:calls).
Reps et al. @reps95 solve interprocedural problems with finite fact
sets and distributive transfer functions precisely, as reachability over
interprocedurally valid paths, and state that semantic correctness is an
orthogonal issue @reps95[§2]. Voblint's domains need not be finite or
distributive, and Voblint proves no precision.

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

Voblint follows Goblint's architecture and adapts the local-trace semantics
of Schwarz et al. This section names what it adopts and where it departs.

=== Architecture

Side-effecting constraint systems let one equation both define a local unknown
and publish contributions to global unknowns @apinis12. Seidl et al. @seidl26
describe how Goblint uses them to decouple a mixed flow-sensitive analysis from
the solver, with digests on the analysis side and update rules on the solver
side recovering precision. Voblint adopts the split: an analysis supplies local
and global transfer behavior, and the generator and solver organize their
interaction.

The correspondence with Goblint's implementation is architectural. We compared
Voblint with the framework interface of Goblint's
#link("https://github.com/goblint/analyzer/blob/" + alignment.revision + "/src/framework/constraints.ml")[constraint generator] at revision #raw(alignment.revision.slice(0, 8)) by
source inspection. There, a call runs the analysis's `enter`, selects the
callee context from the entered state, publishes the callee entry, and combines
the callee's exit with the caller. Voblint's equations have the same four
steps, with enter and combine from the D/G specification and the context
chosen by the routing policy. The project site's side-by-side comparison
(#link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/#goblint")[site])
lists #alignment.rows.len() Goblint constructs:
#alignment-count("modeled") are modeled, #alignment-count("simplified")
simplified, and #alignment-count("absent") not modeled. No row claims that the
two compute the same fixpoint.

Three simplifications affect how results transfer to Goblint. The callee
entry is published to a global seed and read back by the entry's local
unknown, where Goblint writes the local entry directly; under the warrowing
rules the seed itself can be widened, so widening is placed differently, in a
direction we have not proved. Call targets are resolved statically. The
analyses share one combined state and one query kind without globals, where
Goblint's MCP also passes events, spawns and per-analysis globals. No agreement
rate between the verdicts of the two analyzers is reported: the corpus has not
been run through Goblint, whose annotations the adapted fixtures record only as
prose.

=== Combining analyses

Goblint combines its analyses at run time in its MCP (@sec:coop-mcp), which
also answers a query cycle with the top element, caches answers per transfer,
and raises `Deadcode` when one analysis finds a point unreachable
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/mCP.ml")[`mCP.ml`]
at revision `5320a6b7`). Voblint's combination follows this
design for one query kind and for analyses without globals, and adds a proof
obligation per analysis that quantifies over every sound query channel. The
reduced product @cousot79 @rival20[§5.1.2] combines domains through a reduction
on the product carrier, as the Int domain of @sec:reduced-product does. The
combined state keeps separate carriers and exchanges facts only through
answers, so no reduction operator has to be defined or proved for a pair of
analyses.

Verasco, whose channels Voblint's follow (@sec:coop-channels), threads them so
that the second domain can query the state the first has just computed
@jourdan15[§7]. Voblint's answers describe the predecessor state only, as
Goblint's do. Voblint combines any list of components on the fields of one
state and proves the combination sound for calls, returns and
context-sensitive equations.

=== Local traces and contexts

Local traces give each thread of a concurrent program a semantics from which
thread-modular analyses can be derived and compared @schwarz21, later
extended to relational analyses @schwarz23. The digest framework uses
abstractions of execution histories to decide which observations may interact
@schwarz24digest. Voblint adapts the local view to sequential
procedure activations: a trace covers one activation and records its suspended
caller, so a return reads its caller from the trace instead of choosing one. A calling context becomes a
projection of the trace instead of a component of the state. Context policies can therefore be
proved against one fixed concrete semantics. Activations do not interfere, so
no concurrency result of that work transfers.

#cite(<sotin11>, form: "prose") also replace a stack semantics by a local one,
in which every instruction acts on the top activation record only. They prove
the two semantics equivalent with respect to reachable stacks @sotin11[§3]
and derive a
relational interprocedural analysis from the local semantics. Their motive is
pointers into the stack, which VIMP lacks. Voblint proves for activation traces
only that every graph run is represented by a valid trace (@sec:valid).

A digest is a total function on local traces that splits the unknowns $[u]$
into $[u, A]$ already in the concrete semantics @schwarz25phd[§2.3]. Seidl et
al. describe digests as generalizing calling contexts @seidl26[§4, p. 456]. The local-trace semantics itself
has no procedures, and Schwarz lists procedures among the features that Goblint
implements but the local-trace semantics does not yet support
@schwarz25phd[§8, p. 277].
In Voblint, the context relation #isaconst("activation_context_rel") (@sec:contexts)
takes the digest's place for sequential activations. It fixes a context when
an activation is created and keeps it until the activation returns, so a
digest that splits unknowns by history within one activation would need the
relation to advance at every step of a trace, an extension we have not made.

== Where Voblint sits <sec:rel-summary>

Two mechanized analyzers come closest to Voblint's combination of mixed flow
sensitivity and calling contexts.
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
only as sets of constraints, and no solver computes them @dabrowski09[§7].

The concrete semantics of Dabrowski and Pichardie, which carries contexts and
is parameterized by a context policy, is the closest precedent for Voblint's. Voblint's differs in three respects. Its contexts are admitted by a relation,
the totality condition #isaconst("call_context_total_on") makes the
context-indexed collection exhaustive
(#isathm("node_collect_eq_Union_activation_collect")), and the indexing is
connected to an executable solver. The adaptation of local traces
to activations has no mechanized predecessor that we found.

Voblint thus takes its trust pattern from CompCert and Verasco, its domain
interface from Nipkow and Klein, its solver from Tilscher et al., and its
architecture from Goblint, and combines these with what we did not find
mechanized elsewhere: a
context-indexed collecting semantics over activation traces, covered by
equations that a verified side-effecting solver computes.
