#import "../lib/code.typ": *
#import "../lib/theme.typ": vb
#import "../lib/alignment.typ": alignment, alignment-count


= Related Work <ch:related>

@sec:state-of-art compared what Voblint's theorem covers with unverified and
with mechanized analyzers (@tab:production-analyzers, @tab:state-of-art). Here
we compare its mechanisms with the closest lines of work. The comparisons rest
on a web and OpenAlex search with full-text reads of the closest papers, not on
a systematic review.

== Verified analyzers: Verasco and the CompCert line

CompCert and Verasco state their theorems about the tool that users run, and
Voblint follows their pattern for a language with recursive procedures and
context-sensitive calls.

CompCert is a compiler from Clight, a large subset of C, to PowerPC assembly,
programmed and proved correct in Coq, now Rocq @leroy09. Its theorem is
semantic preservation, so safety properties proved of the source hold for the
executable. The compiler is extracted to Caml and linked with unverified
parts, and Leroy lists what remains trusted, from the semantics of Clight and
PowerPC assembly and the CIL-based parser to the assembler, the linker, and
Coq's extraction with the Caml toolchain @leroy09[§5]. Voblint's guarantee has
the same shape, a theorem about
the function the tool runs, code generated from the prover, and an explicit
list of trusted components (@sec:trust-boundary). The two theorems constrain
different things, however. Compiler correctness requires the executable to
preserve the behavior of the source. Analyzer soundness requires only that the
result over-approximate the behavior, so the theorem also accepts a less
precise result, and precision must be assessed separately
(@sec:eval-precision).

Verasco is a Coq-verified analyzer for most of ISO C99, excluding recursion and
dynamic allocation, that proves the absence of run-time errors @jourdan15. Its
abstract interpreter iterates over the structure of the CompCert intermediate
language C\#minor and combines numerical domains through modular interfaces,
and CompCert's semantic preservation extends the guarantee to compiled code.
Verasco covers a far larger language, so the comparison concerns design only.
Verasco reanalyzes functions at every call site and raises an alarm at a
possible recursive call (@tab:state-of-art, @jourdan15[§4]), whereas Voblint
turns calls into equations over (program point, context) unknowns that a
generic solver computes. Its extracted
analyzer runs with unbounded fuel, and termination is proved only on paper
@jourdan16phd[§§3.1.2, 4.3.1], so its theorem, like Voblint's
(@sec:termination), covers only the results it returns.

The earlier value analysis of Blazy et al. @blazy13 does not verify its
fixpoint iterator. An untrusted OCaml implementation of Bourdoncle's iteration
strategy @bourdoncle93 computes a candidate, and a verified checker accepts it
as a post-fixpoint or falls back to top @blazy13[§4]. This leaves the iteration
heuristics free at the cost of a test of every result at run time, whereas the
proof of Voblint's solver @tilscher26 needs no such test but holds for that one
algorithm.

Witness validation also checks results instead of the analyzer. A verifier that
claims a program correct exports invariants at program locations, a
_correctness witness_, from which an independent validator re-establishes the
result. The need is real, since in the 2016 software verification competition
ten of 13 verifiers claimed correctness for some programs known to contain a
bug @beyer16[§1]. The validator Saan et al. @saan24 build on Goblint's abstract
interpreter confirms one result at a time and, unlike the checker of Blazy et
al., is itself unverified.

CompCert hides its dataflow solvers behind a common Coq module type whose
clients rely only on fixpoint properties of the result @compcertKildall. La
Spina et al. @laspina25 verify two solvers based on weak topological orderings
against it, and CompCert's dataflow analyses then run with these solvers. Both
works are intraprocedural. Voblint consumes its solver through a fixpoint
guarantee in the same way, for side-effecting, context-indexed systems, where
the certificate #isaconst("part_post_solution", thy: "Basics_side") also
accounts for contributions to global unknowns.

== Mechanized abstract interpretation

Abstract interpreters have been mechanized in several provers, with different
ways of factoring their proofs for reuse. Nipkow and Klein develop abstract
interpretation in Isabelle/HOL over annotated commands of the While language
IMP @nipkow12 @nipkow14. Their syntax-directed, intraprocedural interpreter is
parametric in a domain of abstract values, which supplies abstract and inverse
operations with their soundness laws, and derives forward evaluation, the
backward filtering of guards, and the step of each command generically
@nipkow14[Sects. 13.5, 13.7]. Voblint's non-relational domains follow this
pattern (@sec:domain-contract). Voblint also keeps their separation between a
collecting semantics and its abstraction, but its collecting semantics ranges
over activation traces of a procedure-aware control-flow graph (@ch:traces),
because a return must know which caller resumes.

Michelland et al. @michelland24, Keidel et al. @keidel18, and Darais et al.
@darais15 make soundness proofs reusable by sharing one interpreter between the
concrete and the abstract semantics, through monadic handlers, an arrow-based
interface, or monad transformers. They reuse the interpreter, and a new
analysis replaces the abstract operations it calls. Voblint's analyzer is
constraint-based instead, so the iteration belongs to a generic solver, and
the proof splits along analysis, context policy, and solver.
#isathm("activation_collect_dg_sound") composes an analysis with a context
policy for any post-solution, @sec:cert-param attaches the solver, and
#isathm("run_voblint_source_sound") states the composed result for every
analysis configuration (@sec:headline).

Syntax-directed interpreters for While languages without procedures have also
been verified in Coq, through an intermediate collecting semantics and with
extraction to OCaml @cachera10[§§1, 6], and in F\* with SMT automation, running
in a browser @franceschino21. An executable or interactive verified analyzer is
therefore not new with this thesis.

Isabelle verifications of interprocedural analyses include a conflict analysis
for programs with recursive procedures, threads, and monitors, proved sound
and, for every program, precise @lammich07afp, an interprocedural slicer
over an abstract control-flow graph with matched calls and returns
@wasserrab09afp, and Shivers' control-flow analysis in Isabelle/HOLCF,
parametric in its contours through a type class that plays the role a context
policy plays here @breitner10afp. None of these entries claims an extracted
analyzer, and none of their semantics represents one activation with its
caller chain, the object Voblint's context relation reads. Code extracted
from an Isabelle proof has, however, already replaced an unverified component
of a larger tool. Buchwald et al. @buchwald16 replace the SSA construction of
CompCertSSA by OCaml code extracted from their locale-based construction.

== Verified fixpoint solvers <sec:rel-solvers>

A verified solver guarantees a property of its result for arbitrary equations,
and the analyzer must give the equations their meaning. Voblint reuses the
solver of Tilscher et al. @tilscher26 and supplies that meaning.

The bytecode verifier of Klein and Nipkow is an early Isabelle instance of a
verified solver consumed through a specification. It must report no error
exactly when a post-fixpoint of the flow functions without errors exists above
the initial state, and Kildall's algorithm meets this specification for every
semilattice with the ascending chain condition and monotone, bounded flow
functions @klein03bcv[§3, Thm. 1]. Their system is finite and
intraprocedural, and the specification also demands completeness, whereas
Voblint's solver explores a context-indexed system with side effects on demand
and Voblint uses only the soundness direction of its certificate.

Hofmann et al. @hofmann10 verify the local generic solver RLD in Coq, and De
Vilhena et al. @devilhena20 verify in Iris a local generic solver that
discovers dependencies dynamically and computes the least fixpoint of a
monotone system. Stade et al. @stade24 prove the top-down solver partially
correct in Isabelle/HOL, first for a simpler recursive formulation and then for
the optimized solver. Tilscher et al. @tilscher26
verify $"TD"_"side"$, which accepts contributions to global unknowns during
iteration, against a generic interface for update rules, prove five update
rules of Stemmler et al. @stemmler25 sound, and refine the solver to executable
code. For the solver variant without widening and narrowing, which joins
every contribution into its target, they also prove that the solver returns
the least partial post-solution, provided it terminates and
the equation system satisfies their monotonicity conditions. Tilscher et al.
@tilscher26jar treat the termination of the solver without side effects, and
@sec:termination explains why these results do not apply to Voblint's
equations.

The algorithm, the update rules, and their proofs belong to that work, of
which Voblint includes a locally refactored copy (@sec:upstream-td). Voblint
contributes the meaning of the equations, since its certificate
#isaconst("part_post_solution", thy: "Basics_side") implies coverage of the
concrete traces and compiler correctness transfers the coverage to source
executions. The solver Voblint runs warrows every local unknown at a widening
point, whichever update rule merges the global contributions, so the
least-solution theorem does not apply. Voblint uses only partial correctness,
for all five rules (@sec:update-rules), and claims no optimality.

== Context sensitivity and trace partitioning

Calling contexts have been defined by call history, by procedure summaries, and
as an index of traces. Voblint's contexts index a collecting semantics, as
trace partitioning does, and one activation may belong to several of them.

#cite(<sharir81>, form: "prose") introduce the two classical approaches to
interprocedural analysis. The functional approach computes input-output
relations of procedures, and the call-string approach tags propagated
information with an encoded call history, so that a return propagates only
information whose history matches. For recursive programs, both may fail to
yield an effective solution for problems such as constant propagation
@sharir81[§1]. #cite(<knoop92>, form: "prose") extend the coincidence theorem
to recursive procedures with local variables, with a return function that
combines the information before the call with the callee's exit information
@knoop92[§4.1], as Voblint's return step combines the caller's pre-call state
with the callee's result (@sec:calls). Reps et al. @reps95 solve
interprocedural problems with finite fact sets and distributive transfer
functions precisely, as reachability over interprocedurally valid paths, and
state that semantic correctness is an orthogonal issue @reps95[§2]. Voblint
needs neither finite nor distributive domains and proves no precision result.

Trace partitioning abstracts a set of traces by indexing it with control
history before abstracting states @rival07. Rival and Mauborgne define both
partitions and coverings, in which one trace may belong to several indices,
present calling-context sensitivity as one such indexing, and note that a
relation may replace the function mapping tokens to tokens in a covering
@rival07[Rem. 3.2.4]. Voblint's activation collecting semantics is a
covering of this relational kind, since a context policy may admit one
activation in several contexts. Voblint mechanizes the indexing over activation
traces and proves that the solved, routed result bounds the activation
collecting semantics of every admitted context.

Contexts also determine how many unknowns a solve creates. The context lifters
of Erhard et al. @erhard25 bound the number of contexts on the fly and
guarantee finitely many contexts whenever the solver updates each unknown
finitely often @erhard25[Abstract]. Voblint's entry-state policy has no such
bound, which is one reason the termination of the solve is not proved
(@sec:termination).

== Goblint, local traces, and thread-modular analysis <sec:rel-goblint>

Voblint follows Goblint's architecture and adapts the local-trace semantics of
Schwarz et al.

=== Architecture

Side-effecting constraint systems let one equation both define a local unknown
and publish contributions to global unknowns @seidl03 @apinis12. Seidl et al.
@seidl26 describe how Goblint uses them to decouple a mixed flow-sensitive
analysis from the solver, with digests on the analysis side and update rules on
the solver side recovering precision. Voblint adopts this split between
transfer behavior and the organization of its interaction.

The correspondence with Goblint's implementation is architectural. We compared
Voblint with the framework interface of Goblint's
#link("https://github.com/goblint/analyzer/blob/" + alignment.revision + "/src/framework/constraints.ml")[constraint generator] by source inspection, at revision
#raw(alignment.revision.slice(0, 8)), which the flavors comparison of
@sec:eval-flavors also runs. There,
a call runs the analysis's `enter`, selects the callee context from the entered
state, publishes the callee entry, and combines the callee's exit with the
caller. Voblint's equations have the same four steps, with enter and combine
supplied by the analysis (@sec:calls) and the context chosen by routing
(@sec:eq-routing). The project site's side-by-side comparison
(#link(site("#goblint"))[site])
lists #alignment.rows.len() Goblint constructs, of which
#alignment-count("modeled") are modeled, #alignment-count("simplified")
simplified, and #alignment-count("absent") not modeled. The constructs not
modeled are Goblint's `sync` hook, threads, and C itself, which Goblint reads
through CIL. No row claims that the two compute the same fixpoint.

The two differ in several places. Voblint publishes the callee entry to a
global seed that the entry's local unknown reads back, where Goblint writes the
callee's entry unknown directly, and under the warrowing rules the seed itself can be
widened. Widening thus acts one step later than in Goblint, and we have not
compared the precision of the two placements. Call targets are resolved
statically. The analyses share one combined state and one query kind without
globals, where Goblint's MCP also passes events, spawns, and per-analysis
globals. No agreement rate between the two analyzers' verdicts is reported.
Apart from the flavors programs of @sec:eval-flavors, whose C versions we ran
through Goblint, the corpus has not been run through Goblint, and the adapted
fixtures record Goblint's annotations only as prose.

=== Combining analyses

Goblint combines its analyses at run time in its MCP (@sec:coop-mcp), which
also answers a query cycle with the top element, caches answers per transfer,
and raises `Deadcode` when one analysis finds a point unreachable
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/mCP.ml")[`mCP.ml`]
at the same revision). Voblint's combination follows this design for one
query kind and for analyses without globals, and adds a proof obligation per
analysis that quantifies over every sound query channel. Unlike the reduced
product @cousot79 @rival20[§5.1.2], which combines domains through a reduction
on the product carrier as the Int domain of @sec:reduced-product does, the
combined state keeps separate carriers and exchanges facts only through
answers, so no reduction operator has to be defined or proved for a pair of
analyses. Verasco, whose channels Voblint's follow (@sec:coop-channels),
threads them so that the second domain can query the state the first has just
computed @jourdan15[§7]. Voblint's answers describe the predecessor state only,
as Goblint's do.

=== Local traces and contexts

Local traces give each thread of a concurrent program a semantics against which
thread-modular analyses are proved sound and compared @schwarz21, later
extended to relational analyses @schwarz23, with detailed proofs in
@schwarz25phd[Ch. 6]. Voblint adapts the local view to sequential procedure
activations. A trace covers one activation and records its suspended caller, so
a return reads its caller from the trace instead of choosing one, and a calling
context becomes a projection of the trace instead of a component of the state.
Context policies can therefore be proved against one fixed concrete semantics.
VIMP's activations run one at a time, so no concurrency result of that work
transfers.
#cite(<sotin11>, form: "prose") also replace a stack semantics by a local one,
in which every instruction acts on the top activation record only, prove the
two equivalent with respect to reachable stacks @sotin11[§3], and derive a
relational interprocedural analysis from the local semantics. Their motive is
pointers into the stack, which VIMP lacks. Voblint proves for activation traces
only that every graph run is represented by a valid trace (@sec:source-bridge).

The digest framework uses abstractions of execution histories to decide which
observations may interact @schwarz24digest. A digest is a total function on
local traces that splits the unknowns $[u]$ into $[u, A]$ already in the
concrete semantics @schwarz25phd[§2.3]. That local-trace semantics has no
procedures yet, although Goblint's analyzer handles procedure calls
@schwarz25phd[§8, p. 277].
In Voblint, the context relation
#isaconst("activation_context_rel") (@sec:contexts) plays a similar role for
sequential activations, with two differences. A digest is a function, so every
trace has exactly one digest and the traces split into disjoint groups
@schwarz25phd[§2.3, Def. 4, Thm. 4]. One activation may instead carry several
contexts, so Voblint's groups may overlap, and together they still contain
every collected store (#isathm("node_collect_eq_Union_activation_collect")). A
digest is also updated at every step of a trace, whereas an activation's
contexts are fixed when it is called, so Voblint distinguishes activations only
by how they were entered.

== Where Voblint sits <sec:rel-summary>

Two mechanized analyzers come closest to Voblint's combination of mixed flow
sensitivity and calling contexts. Cachera et al. @cachera05 prove in Coq that a
constraint-based analysis of Carmel, an intermediate representation of Java
Card bytecode, is sound with respect to a small-step operational semantics. It
keeps one flow-insensitive heap and flow-sensitive local variables and operand
stacks per program point, is context-insensitive, and solves ordinary
inequations with a verified round-robin solver extracted to OCaml
@cachera05[§§2, 3.2]. #cite(<dabrowski09>, form: "prose") prove in Coq that a
context-sensitive points-to analysis with a flow-insensitive heap, a component
of their certified data race analyzer, is sound. They instrument the concrete
semantics with contexts through a Coq functor over a module type of contexts,
whose call-context function computes a callee's context from the call site,
the caller's context, and the receiver, and instantiate it with, among others,
$k$-object sensitivity. By the authors' account the specification is not
executable, since the analyses are only sets of constraints that no solver
computes @dabrowski09[§7]. This concrete semantics, which carries contexts and
is parameterized by a context policy, is the closest precedent for Voblint's.
Voblint's differs in
that a relation admits its contexts, the totality condition
#isaconst("call_context_total_on") makes the context-indexed collection
exhaustive (#isathm("node_collect_eq_Union_activation_collect")), and the
indexing is connected to an executable solver.

Voblint thus takes its trust pattern from CompCert and Verasco, its domain
interface from Nipkow and Klein, its solver from Tilscher et al., and its
architecture from Goblint. It combines these with what we did not find
mechanized elsewhere, a context-indexed collecting semantics over activation
traces, covered by equations that a verified side-effecting solver computes.
