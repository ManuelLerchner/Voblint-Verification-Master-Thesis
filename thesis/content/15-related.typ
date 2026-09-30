#import "../lib/code.typ": *
#import "../lib/theme.typ": vb

#let _todo(body) = text(fill: vb.unproved)[TODO: #body]

= Related Work <ch:related>

We compare Voblint with prior systems along three design choices: the
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
parts, and Leroy lists what remains trusted: the source and target semantics,
the parser, assembler and linker, the extraction and the Caml compiler and
runtime, and Coq itself @leroy09 #_todo[check the target and the trusted list
  against the paper.]. AbsInt distributes CompCert commercially and
reports its use in the certification of control software @absint-compcert
#_todo[check claim.].
Voblint's guarantee has the same shape: a theorem
about the function the tool runs, code generated from the prover, and an
explicit list of trusted components (@sec:trust-boundary). Voblint's parser
corresponds to CompCert's parser, its code generator and OCaml toolchain to
the extraction and the Caml compiler, and its printing and rendering code to
the assembly printer, assembler and linker downstream. Compiler correctness
preserves the behaviour of a program. Analyzer soundness only over-approximates
it, so a coarser result remains sound.

Verasco is a Coq-verified analyzer for most of ISO C99, excluding recursion and
dynamic allocation, that proves the absence of run-time errors @jourdan15. Its
abstract interpreter iterates over the structure of C\#minor, a CompCert
intermediate language. Modular interfaces separate the abstract state from an
extensible combination of numerical domains, and CompCert's semantic
preservation extends the guarantee to compiled code. Functions are reanalyzed at
every call site up to a fuel bound, and a possible recursive call raises an
alarm #_todo[check scope, fuel and recursion alarm against @jourdan15.].

Verasco covers a far larger language, so the comparison concerns design only.
Voblint's language is small, but recursion and context-sensitive calls are
central to it: calls become equations over (program point, context) unknowns,
and a generic solver computes their solution. With fuel, Verasco needs no
termination argument. Voblint's source theorem takes termination of the solve as
a premise.
Both specify abstract operations through concretization alone.

The earlier value analysis of #cite(<blazy13>, form: "prose") does not verify
its fixpoint iterator. An untrusted OCaml implementation of Bourdoncle's
iteration strategy @bourdoncle93 computes a candidate, and a verified checker
accepts it as a post-fixpoint or falls back to top #_todo[check claim.]. Voblint instead runs a
solver whose partial correctness is proved @tilscher26. The checker leaves the
iteration heuristics free and tests every result at run time. A verified solver
needs no such test, and its proof holds for that one algorithm.

CompCert hides its dataflow solvers behind a common Coq module type
@compcertKildall. A solver returns an optional map from program points to
abstract values, and clients rely on three properties: the result satisfies
the dataflow inequations, satisfies the entry constraint, and preserves every
property that holds for bottom and is preserved by join and the transfer
functions #_todo[check the three properties.]. #cite(<laspina25>, form: "prose") verify two solvers based on weak
topological orderings in Coq and make them compatible with that interface, so
CompCert's analyses can use them unchanged #_todo[check claim.]. Both works are intraprocedural.
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
@nipkow14[Sects. 13.5--13.7] #_todo[check locator.]. Voblint's non-relational domains follow this
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
semantics is deterministic, its procedures take no arguments and return no
value, and its program logic covers only terminating runs (@sec:vimp)
#_todo[check claim.].

Three works factor the soundness proof of an analyzer for reuse.
#cite(<michelland24>, form: "prose") build abstract interpreters in Coq from
monadic handlers stacked over a free monad: abstract control-flow combinators
are proved sound once against their concrete counterparts, and each effect
handler has an abstract variant with its own soundness condition.
#cite(<keidel18>, form: "prose") share one interpreter between the concrete and
the abstract semantics, parameterized over an arrow-based interface, and reduce
its soundness to lemmas about the two instances of that interface.
#cite(<darais15>, form: "prose") make context, path and heap sensitivity monad
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

#cite(<franceschino21>, form: "prose") verify a syntax-directed abstract
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
class, which plays the role a context policy plays here. The entries' pages
do not claim an extracted analyzer #_todo[check the four AFP entries' claims.]. Code generated from an Isabelle proof has
replaced an unverified compiler component before:
#cite(<buchwald16>, form: "prose") define SSA construction over an abstract
control-flow graph fixed by a locale, instantiate it for a While language, and
replace the SSA construction of CompCertSSA by OCaml code extracted from a
further instantiation.

None of the Isabelle semantics above represents one activation with its caller
chain, the object Voblint's context relation reads. The factorings above share
an interpreter, a handler stack or a monad stack between the concrete and the
abstract semantics. Voblint mechanizes a three-way split between analysis,
context policy and solver for a constraint-based analyzer, with one composition
theorem, #isathm("activation_collect_dg_sound"), instantiated for every shipped
configuration. Lammich and Müller-Olm prove precision of their analysis for
every program. Voblint's precision statements compare two configurations on
one program.

== Verified fixpoint solvers <sec:rel-solvers>

What does a verified solver guarantee, and what must an analyzer add? Voblint
reuses the solver of #cite(<tilscher26>, form: "prose") and supplies the
meaning of the equations it solves.

#cite(<hofmann10>, form: "prose") verify the local generic solver RLD in Coq;
like the top-down solver, it records dependencies between unknowns while it
evaluates right-hand sides. #cite(<stade24>, form: "prose") prove the top-down
solver partially correct in Isabelle/HOL, first for a simpler recursive
formulation and then for the optimized solver, which agrees with it on
termination and results. #cite(<tilscher26>, form: "prose") extend the line to
mixed flow-sensitive analyses. They verify $"TD"_"side"$, which accepts
contributions to global unknowns during iteration, against a generic interface
for update rules, prove five update rules of
#cite(<stemmler25>, form: "prose") sound, and refine the solver to executable
code. The copy Voblint vendors interprets the update-rule interface once for
each of the five rules #_todo[check the scope of the executable refinement
  against @tilscher26.]. For precise updates without widening and narrowing, they also prove that
the solver returns the least partial post-solution, provided it terminates and
the equation system satisfies their monotonicity conditions.
#cite(<tilscher26jar>, form: "prose") treat the top-down solver without side
effects, extended either with warrowing or with separate widening and
narrowing phases. They prove that the warrowing variant returns partial
post-solutions and that the phased variant terminates when the set of unknowns
is finite. The two variants are equivalent under three assumptions: the widening
operator is precise, and the right-hand sides are monotonic and have monotonic
dependencies. Total correctness of both follows #_todo[check the three
  assumptions.].

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

== Goblint, local traces, and thread-modular analysis <sec:rel-goblint>

Voblint follows Goblint's architecture and the local-trace semantics of its
research line. This section names what it adopts and where it departs.

Side-effecting constraint systems let one equation both define a local unknown
and contribute to global unknowns @apinis12. #cite(<seidl26>, form: "prose")
describe how Goblint uses them to decouple a mixed flow-sensitive analysis from
the solver, with digests on the analysis side and update rules on the solver
side recovering precision. Voblint adopts the split: an analysis supplies local
and global transfer behaviour, and the generator and solver organize their
interaction. @app:goblint-alignment records where the model differs from
Goblint's implementation.

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
analyses. The open product of #cite(<cortesi94>, form: "prose"), designed for
logic programs, also lets each combined domain use information from the others
through queries.

Verasco combines its numerical domains through the channels of @sec:coop-oracle
for the same reason: reduced products tend to be specific to the two domains
combined and scale poorly beyond two @jourdan15[§7] @cousot07astree[§5.2]
#_todo[check claim.]. Its
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
the two semantics equivalent with respect to reachability and derive a
relational interprocedural analysis from the local semantics. Their motive is
pointers into the stack, which VIMP lacks. For activation traces, Voblint
proves only the direction soundness needs: every graph run is represented by a
valid trace (@sec:valid). #_todo[check the equivalence claim of @sotin11.]

A digest is a total function on local traces that splits the unknowns $[u]$
into $[u, A]$ already in the concrete semantics @schwarz25phd[§2.3]. Seidl et
al. describe digests as generalizing calling contexts @seidl26[§4, p. 456]. The local-trace semantics itself
has no procedures: its programs are sets of thread control-flow graphs without
a call action, and Schwarz lists procedures among the features that Goblint
implements but the local-trace semantics does not yet support
@schwarz25phd[§8, p. 277].
In Voblint, the context relation #isaconst("activation_context_rel") (@sec:contexts)
takes the digest's place for sequential activations. It is a relation, because an entry-state context is
read off the analysis's result.

Mixed flow sensitivity has been mechanized before.
#cite(<cachera05>, form: "prose") prove in Coq that a constraint-based analysis
of Carmel, an intermediate representation of Java Card bytecode, is sound with
respect to a small-step operational semantics. It keeps one flow-insensitive
heap and flow-sensitive local variables and operand stacks per program point,
is context-insensitive, and solves ordinary inequations with a verified
round-robin solver extracted to OCaml #_todo[check claim.]. #cite(<dabrowski09>, form: "prose")
prove sound in Coq a context-sensitive points-to analysis with a
flow-insensitive heap, a component of their certified data race analyzer. They
instrument the concrete semantics with contexts through a Coq functor over a
module type of contexts, whose call-context function computes the context
of a callee from the call site, the caller's context and the receiver, and
they instantiate it, among others, with $k$-object sensitivity. The authors
state that the specification is not executable: the analyses are sets of
constraints, and no solver computes them #_todo[check claim.]. Voblint's instance with
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

== Context sensitivity and trace partitioning

How have calling contexts been defined, and what does a relational context
add? Voblint's contexts index a collecting semantics, as trace partitioning
does, and one activation may belong to several of them.

#cite(<sharir81>, form: "prose") introduce the two classical approaches to
interprocedural analysis. The functional approach establishes input-output
relations for procedures and treats calls as super operations, and the
call-string approach tags propagated information with an encoded history of
the calls encountered, so that a return propagates only information whose
history matches @sharir81[pp. 191--192] #_todo[check locator.]. For recursive programs, both may fail
to yield an effective solution for problems such as constant propagation
@sharir81[p. 192]. #cite(<knoop92>, form: "prose") extend the coincidence
theorem to recursive procedures with local variables. Their return function
combines the information before the call with the callee's exit information,
because the local variables must be reset to their values at call time
@knoop92[§4.1] #_todo[check locator.]. Voblint's return step has the same shape, combining the
caller's pre-call state with the callee's result (@sec:calls).
#cite(<reps95>, form: "prose") solve interprocedural problems with finite fact
sets and distributive transfer functions precisely, as reachability over
interprocedurally valid paths, and state that semantic correctness is an
orthogonal issue @reps95[§2] #_todo[check locator.]. Voblint's domains need not be finite or
distributive, and Voblint proves no precision. It proves the semantic
correctness that these frameworks leave to the encoding.

Trace partitioning abstracts a set of traces by indexing it with control history
before abstracting states @rival07. Rival and Mauborgne define both partitions
and coverings, in which one trace may belong to several indices, and present
calling-context sensitivity as one such indexing; keeping the full stack amounts
to inlining and works only for nonrecursive calls. They also note that the
function mapping tokens to tokens in a covering may be replaced by a relation
@rival07[Rem. 3.2.4] #_todo[check locator.]. Voblint's context-indexed
collecting semantics is a covering of this relational kind, since a context relation may admit one
activation in several contexts. Voblint mechanizes the indexing over
activation traces and proves that the solved, routed result bounds the activation
collecting semantics of every admitted context.

Contexts also determine how many unknowns a solve creates. The context lifters
of #cite(<erhard25>, form: "prose") bound the number of contexts on the fly and
guarantee finitely many contexts whenever the solver updates each unknown
finitely often #_todo[check claim.]. Voblint's entry-state policy has no such bound, which is one reason the
termination of the solve stays a per-program premise (@sec:termination).

== Unverified analyzers and their testing <sec:rel-testing>

Most abstract interpreters in use are not mechanized, and they earn trust by
testing. Astrée proves the absence
of run-time errors in safety-critical C programs of up to 132,000 lines, with
few or no false alarms, by refining a general analyzer for a program family
@blanchet03 #_todo[check the line count.]. It analyzes a call by abstract execution of the body at the call
point, which is equivalent to inlining since the programs do not use recursion
@blanchet03[§5.4]. #cite(<livshits15>, form: "prose") observe that realistic
whole-program analyses purposely make unsound choices and ask authors to state
the nature and extent of the unsoundness explicitly.

#figure(
  {
    set text(size: 8pt)
    set par(justify: false, leading: 0.45em)
    table(
      columns: (auto, auto, auto, auto, auto, auto, auto, auto),
      align: (col, _) => (if col == 0 { left } else { center }) + horizon,
      stroke: none,
      inset: (x: 3pt, y: 2.6pt),
      table.hline(stroke: 0.5pt),
      [*Tool*], [*Language*], [*Stance*], [*Calls*], [*Recursion*], [*Relational*],
      [*Combination*], [*Mechanized*],
      table.hline(stroke: 0.4pt),
      [Astrée @cousot07astree], [C subset], [sound], [inlining], [not used], [octagons],
      [channels], [none],
      [Eva @eva-manual], [C], [sound], [inlining], [contract], [Apron], [via values],
      [none],
      [MOPSA @journault19], [C, Python], [sound], [inlining], [unsupported], [Apron],
      [products, queries], [none],
      [IKOS @brat14], [C/C++], [sound], [inlining], [assumptions], [Apron],
      [fixed products], [none],
      [Pulse-X @le22], [C/C++], [bug finding], [summaries], [unrolled], [pure conditions],
      [one domain], [none],
      [Goblint @saan23], [C], [sound], [per context], [analyzed], [Apron], [queries],
      [TD algorithm],
      table.hline(stroke: 0.4pt),
      [*Voblint*], [VIMP], [proved sound], [per context], [covered], [order analysis],
      [queries], [end to end],
      table.hline(stroke: 0.5pt),
    )
  },
  kind: table,
  placement: top,
  caption: [Unverified analyzers and Voblint, as described by each tool's papers
    and documentation. _Stance_ is the tool's own soundness claim. Under
    _calls_, inlining re-analyzes the callee at every call, a summary is
    computed once per procedure, and _per context_ means one unknown per
    program point and context. _Recursion_ says how a recursive call is
    treated, and _covered_ means Voblint's theorem includes recursive calls.
    _Combination_ names how domains exchange facts, and _mechanized_ records
    what a proof assistant has checked. _End to end_ means from source
    executions to the verdicts of the exported function, under a per-program
    termination premise and with the trusted components of
    @sec:trust-boundary. #_todo[check the IKOS and Pulse-X cells against
      @brat14 and @le22.]],
) <tab:production-analyzers>

@tab:production-analyzers compares Voblint with six analyzers that have no
machine-checked soundness proof. Four of them handle a call by inlining, which
analyzes the callee anew at every call and so never needs a context policy
@blanchet03[§5.4] @eva-manual[§5.3] @journault19[§5.1] @brat14[§3]. Recursion
is where they differ. The programs Astrée targets do not recurse
@blanchet03[§5.4]. Eva relies on a user-written contract or unrolls to a given
depth @eva-manual[§6.3.9], MOPSA lists recursion as unsupported
@mopsa-manual[Limitations], and IKOS assumes that a recursive call may update
any value in memory @ikos-readme[Analysis Assumptions]. Goblint, like Voblint,
solves for one unknown per program point and context and analyzes recursive
programs, but its documentation warns that the default configuration may not
terminate on them
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/docs/user-guide/running.md")[`running.md`]
at revision `5320a6b7`). Voblint's theorem covers recursive procedures under
each policy, with the termination of the solve as a premise.

Pulse-X, which represents Infer, is the one tool whose whole analysis has a
soundness theorem. It is proved on paper for a formal model and states that reported errors are real
within that model @le22[pp. 81:2--81:3], an under-approximating guarantee. For
Goblint, the partial correctness of the top-down solver is proved in
Isabelle/HOL @stade24 @tilscher26 for a formulation of the algorithm, not for
the OCaml solver Goblint runs. Voblint's theorem is about the function its
executable runs, with the trusted components of @sec:trust-boundary.

Testing checks such tools against executions. #cite(<cuoq12>, form: "prose")
compare Frama-C's value analysis with compiled execution on programs generated
by Csmith and report fifty bugs found and fixed #_todo[check number.].
#cite(<klinger19>, form: "prose") find soundness or precision issues in four
of six analyzers, and #cite(<kaindlstorfer24>, form: "prose") find 16
soundness issues in seven of eight, including MOPSA #_todo[check numbers.]. A test exposes a defect on
one program and cannot show its absence. Voblint's regression corpus is testing
of this kind (@sec:eval-corpus), and the Goblint defect replayed in
@sec:eval-1161 is the kind of transfer-function error that a per-operation
soundness obligation excludes inside the proof boundary.

The table also shows the price of the proof. The unverified analyzers accept
C, C++ or Python, and Astrée and IKOS have been applied to safety-critical
control software @blanchet03 @brat14[§3]. Voblint's theorem covers VIMP
(@sec:vimp), which has no pointers, heap or machine integers, and the proof
covers only the definitions it is about. Such approaches assume a formal
semantics of the analyzed language @cuoq12[§1], which is the adequacy question
of @sec:vimp-vs-c.

== Where Voblint sits <sec:where-voblint-sits>

Much of Voblint is inherited. The solver and the soundness proofs of its update
rules come from #cite(<tilscher26>, form: "prose"), the rules from
#cite(<stemmler25>, form: "prose"), side-effecting constraint systems from
#cite(<apinis12>, form: "prose"), and the local/global analysis architecture
from Goblint. Widening, narrowing and the reduced product are standard
@cousot77 @cousot79. Deriving forward and backward transfer from sound
value operations follows the generic abstract interpreter of Nipkow and Klein
@nipkow14[Sects. 13.5--13.7]. The activation traces adapt the local traces of
@schwarz21 to procedure activations, and the context-indexed collecting
semantics is a relational covering in the sense of @rival07. Compared with
the works above, the scoped claims of @sec:contributions are the following.
Each records an absence of evidence in the search described at the start of
this chapter, and none is a priority claim.

- *End-to-end soundness.* No mechanized analyzer we found proves soundness of its exported
  executable for a language with recursive procedures under configurable
  context sensitivity. Verasco raises an alarm on recursion, the analyzer of
  #cite(<cachera05>, form: "prose") is context-insensitive, and the analysis of #cite(<dabrowski09>, form: "prose") is not
  executable.
- *Context semantics.* The relational context semantics with its totality
  condition differs from the functional context module of @dabrowski09 in
  admitting several contexts per call. Over activation traces, it
  mechanizes a relational variant of coverings that @rival07 mention.
- *Composition.* The certificate-based solver interface follows CompCert's. The
  three-way composition separates analysis, context policy and solver.
  @darais15 separate sensitivities as monad transformers, proved on paper, which
  is a different split. From one record of
  primitives proved sound, the abstract transfer and the executable transfer the
  analyzer runs are derived together and proved to agree on every live store
  (#isathm("sound_nonrelational_ops.tf_st_for_commute")), and one rule
  registers the domain with #isalocale("dg_analysis_exec")
  (#isathm("sound_nonrelational_ops.dg_analysis_execI")).
- *Precision.* We found no strict precision separation between configurations
  of one analyzer that is checked in a proof assistant. Ours is evaluated
  (#isathm("sign_k2_strictly_more_precise_than_k1_at_g")).
