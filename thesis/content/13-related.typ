#import "../lib/code.typ": *

= Related Work <ch:related>

We compare Voblint with prior systems along three design choices: the
semantics an analyzer is proved against, how its fixpoint is computed, and how
much of the delivered tool the proof covers. For each work we report its
authors' claims before relating them to this thesis, and each section ends with
the consequences for the contributions of @sec:contributions. The
comparisons are based on a web and OpenAlex search with full-text reads of the
closest papers, not on a systematic review, so a work that search missed could
narrow the scoped claims below. Several comparisons depend on how the fixpoint
is formulated. Voblint is constraint-based, as Goblint is, whereas Verasco and the
analyzers of Nipkow and Klein and of Franceschino et al. are syntax-directed (@sec:why-graph).

== Verified analyzers: Verasco and the CompCert line

CompCert is a compiler from Clight, a large subset of C, to PowerPC assembly,
programmed and proved correct in Coq, now Rocq @leroy09. Its theorem is semantic
preservation: the compiled code behaves as the source semantics specifies, so
safety properties proved of the source hold for the executable. The executable
compiler is extracted from Coq to Caml and linked with handwritten, unverified
parts, and Leroy lists what remains trusted: the source and target semantics,
the parser, assembler and linker, the extraction and the Caml compiler and
runtime, and Coq itself @leroy09. AbsInt now distributes CompCert under licence
from INRIA. Its product page states that the proof covers the whole
translation of the abstract syntax tree into machine code, that an external C
preprocessor, assembler, linker and C libraries are required, and reports a
certification of control software under IEC 60880 and IEC 61508-3:2010 that
used it @absint-compcert. Voblint's guarantee has the same shape: a theorem
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
alarm.

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
accepts it as a post-fixpoint or falls back to top. Voblint instead runs a
solver whose partial correctness is proved @tilscher26. The checker leaves the
iteration heuristics free and tests every result at run time. A verified solver
needs no such test, and its proof holds for that one algorithm.

CompCert hides its dataflow solvers behind a common Coq module type
@compcertKildall. A solver returns an optional map from program points to
abstract values, and clients rely on three properties: the result satisfies
the dataflow inequations, satisfies the entry constraint, and preserves every
property that holds for bottom and is preserved by join and the transfer
functions. #cite(<laspina25>, form: "prose") verify two solvers based on weak
topological orderings in Coq and make them compatible with that interface, so
CompCert's analyses can use them unchanged. Both works are intraprocedural.

For end-to-end soundness, CompCert is the precedent for stating the theorem about the delivered
executable and naming its trusted base. Verasco is the closest mechanized
analyzer that ships an executable. It reanalyzes each call up to a fuel bound and raises an alarm where a recursive
call can occur, whereas Voblint's theorem covers recursive procedures under
each of its context policies. For compositionality, CompCert's interface is the precedent
for consuming a solver through its fixpoint guarantee alone. Voblint applies
the same discipline to side-effecting, context-indexed systems, where the
certificate #isaconst("part_post_solution") has to account for contributions
to global unknowns.

== Mechanized abstract interpretation

Nipkow and Klein develop abstract interpretation in Isabelle/HOL over annotated
commands of the While language IMP @nipkow12 @nipkow14. A collecting semantics
annotates each program point with a set of states, and an abstract interpreter
annotates it with an abstract state. The development is syntax-directed and
intraprocedural. Voblint keeps the separation between collecting semantics and
abstraction. Its collecting semantics ranges over activation-local traces of a
procedure-aware control-flow graph (@ch:traces), because a return must know
which caller resumes. Their executable abstract state reads every variable it
does not list as top. Voblint's carrier needs one default for local and one
for global names: the entry state reads every global as zero, and the global
half of a published state reads every local as bottom (@ch:solving).

We did not state the theorem against IMP2 @lammich19imp2, the Isabelle
formalization of an imperative language with procedures and a
verification-condition generator. Its small-step semantics is a partial
function, so it cannot express VIMP's nondeterministic input, on which the
regression programs that show `UNKNOWN` to be the only sound answer rely. Its
procedure calls take no arguments and return no value, and its operators are
HOL functions, on which an executable analyzer cannot dispatch
(@sec:vimp). Its program logic is stated over the big-step semantics, which
relates only terminating runs, whereas the source-level theorem covers every
finite prefix of a run.

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
analyzer. Voblint's per-domain obligations play a similar role. The shared
structure they instantiate is the equation generator of @ch:equations, and the
solver is a third, separately verified component.

#cite(<cachera10>, form: "prose") program and prove in Coq an abstract
interpreter for a While language without procedures. It iterates over the
syntax with widening and narrowing, is proved correct through an intermediate
collecting semantics defined with a generic least-fixpoint operator, and is
extracted to OCaml @cachera10[§§1, 6]. Voblint uses the same stepping stone, a
collecting semantics between execution and abstraction, but over
activation-local traces of a graph and with a separately verified solver
instead of a syntax-directed iterator.

#cite(<franceschino21>, form: "prose") verify a syntax-directed abstract
interpreter for a small imperative language in F\*, using refinement types and
SMT automation instead of interactive proof. Their analyzer also runs in a
browser, and Verasco ships an extracted command-line analyzer @jourdan15, so an
executable or interactive verified analyzer is not new with this thesis. The
F\* demonstration page takes a program and prints the analyzer's text output; it
has no configuration controls. Voblint's playground selects the domain, update
rule and context policy and shows the solved state per context
(@sec:playground). We have not compared the two interfaces beyond this.
Deductive verifiers such as Velvet @velvet26 check user-supplied contracts and
loop invariants. Voblint computes invariants without annotations, but only
those its abstract domain can express.

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
do not claim an extracted analyzer. Code generated from an Isabelle proof has
replaced an unverified compiler component before:
#cite(<buchwald16>, form: "prose") define SSA construction over an abstract
control-flow graph fixed by a locale, instantiate it for a While language, and
replace the SSA construction of CompCertSSA by OCaml code extracted from a
further instantiation.

For the context semantics, the Isabelle semantics above model whole executions or valid paths.
None of them represents one activation with its caller chain, the object Voblint's
context relation reads. For compositionality, the factorings above share an interpreter, a
handler stack or a monad stack between the concrete and the abstract
semantics. Voblint mechanizes a three-way split between domain, context policy
and solver for a constraint-based analyzer, and its one composition theorem,
#isathm("activation_collect_dg_sound"), is instantiated for every shipped
configuration. For precision, Lammich and Müller-Olm prove precision of their
analysis for every program. Voblint's precision statements compare two
configurations on one program.

== Verified fixpoint solvers <sec:rel-solvers>

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
code. For precise updates without widening and narrowing, they also prove that
the solver returns the least partial post-solution, provided it terminates and
the equation system satisfies their monotonicity conditions.
#cite(<tilscher26jar>, form: "prose") treat the top-down solver without side
effects, extended either with warrowing or with separate widening and
narrowing phases. They prove that the warrowing variant returns partial
post-solutions and that the phased variant terminates when the set of unknowns
is finite. The two variants are equivalent under three assumptions: the widening
operator is precise, and the right-hand sides are monotonic and have monotonic
dependencies. Total correctness of both follows.

Voblint includes a copy of the solver of @tilscher26; the algorithm, the update
rules and their proofs belong to that work. A solver theorem speaks about
arbitrary right-hand sides and gives the equations no meaning. Voblint supplies that
meaning for its language: the certificate #isaconst("part_post_solution")
implies coverage of the concrete traces, and compiler correctness transfers the
coverage to source executions. The solver Voblint runs warrows every local
unknown at a widening point, whichever of the four selectable update rules
merges the global contributions. The least-solution theorem therefore does not
apply, and Voblint uses only partial correctness and claims no optimality for
its results.

For compositionality, soundness is derived from
#isaconst("part_post_solution") alone, so the four selectable update rules need
no separate soundness argument on the Voblint side. For precision, the
least-solution theorem is a general result. Voblint's precision statements are
strict inequalities between the results of named solves.

== Goblint, local traces, and thread-modular analysis <sec:rel-goblint>

Side-effecting constraint systems let one equation both define a local unknown
and contribute to global unknowns @apinis12. #cite(<seidl26>, form: "prose")
describe how Goblint uses them to decouple a mixed flow-sensitive analysis from
the solver, with digests on the analysis side and update rules on the solver
side recovering precision. Voblint adopts the split: an analysis supplies local
and global transfer behaviour, and the generator and solver organize their
interaction. @app:goblint-alignment records where the model differs from
Goblint's implementation.

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
no concurrency result of that work transfers.

#cite(<sotin11>, form: "prose") also replace a stack semantics by a local one,
in which every instruction acts on the top activation record only. They prove
the two semantics equivalent with respect to reachability and derive a
relational interprocedural analysis from the local semantics. Their motive is
pointers into the stack, which VIMP lacks. For activation-local traces, Voblint
proves only the direction soundness needs: every graph run is represented by a
valid trace (@sec:valid).

A digest is a total function on local traces, and it splits the unknowns $[u]$
into $[u, A]$ already in the concrete semantics @schwarz25phd[§2.3].
Seidl et al. @seidl26[§4] describe digests as generalizing calling contexts to
the full, possibly concurrent trace reaching a point, but the local-trace
semantics of that line has no procedures @schwarz25phd[§8].
#isaconst("trace_context") (@sec:contexts) takes the digest's place for
sequential activations, with one difference: it is a relation. Goblint's
`enter` returns a list of alternatives, each routed to its own context, so one
concrete call may be admitted at several contexts, which a function cannot
express. Calls and returns need no separate digest, since the admitted contexts
are read off the activation-local trace.

Mixed flow sensitivity has been mechanized before.
#cite(<cachera05>, form: "prose") prove in Coq that a constraint-based analysis
of Carmel, an intermediate representation of Java Card bytecode, is sound with
respect to a small-step operational semantics. It keeps one flow-insensitive
heap and flow-sensitive local variables and operand stacks per program point,
is context-insensitive, and solves ordinary inequations with a verified
round-robin solver extracted to OCaml. #cite(<dabrowski09>, form: "prose")
prove sound in Coq a context-sensitive points-to analysis with a
flow-insensitive heap, a component of their certified data race analyzer. They
instrument the concrete semantics with contexts through a Coq functor over a
module type of contexts, whose call-context function computes the context
of a callee from the call site, the caller's context and the receiver, and
they instantiate it, among others, with $k$-object sensitivity. The authors
state that the specification is not executable: the analyses are sets of
constraints, and no solver computes them. Voblint's instance with
flow-insensitive program globals, and the exact scope of its proof, are
described in @sec:mixed-flow.

Dabrowski and Pichardie are the closest precedent for the context semantics: a mechanized
concrete semantics that carries contexts, parameterized by a context policy.
Voblint's differs in three respects. Contexts are admitted by a relation, so one call
may enter several contexts; the totality condition
#isaconst("call_context_total_on") makes the context-indexed collection
exhaustive (#isathm("ltr_collect_eq_Union_activation_collect")); and the
indexing is connected to an executable solver. The adaptation of local traces
to activations has no mechanized predecessor that we found.

== Context sensitivity and trace partitioning

#cite(<sharir81>, form: "prose") introduce the two classical approaches to
interprocedural analysis. The functional approach establishes input-output
relations for procedures and treats calls as super operations, and the
call-string approach tags propagated information with an encoded history of
the calls encountered, so that a return propagates only information whose
history matches @sharir81[pp. 191--192]. For recursive programs, both may fail
to yield an effective solution for problems such as constant propagation
@sharir81[p. 192]. #cite(<knoop92>, form: "prose") extend the coincidence
theorem to recursive procedures with local variables. Their return function
combines the information before the call with the callee's exit information,
because the local variables must be reset to their values at call time
@knoop92[§4.1]. Voblint's return step has the same shape, combining the
caller's pre-call state with the callee's result (@sec:calls).
#cite(<reps95>, form: "prose") solve interprocedural problems with finite fact
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
@rival07[Rem. 3.2.4]. Voblint's context-indexed collecting semantics is a
covering of this relational kind, since a context relation may admit one
activation in several contexts. Voblint mechanizes the indexing over
activation-local traces and proves that the solved, routed result bounds every
admitted bucket.

Contexts also determine how many unknowns a solve creates. The context lifters
of #cite(<erhard25>, form: "prose") bound the number of contexts on the fly and
guarantee finitely many contexts whenever the solver updates each unknown
finitely often. Voblint's entry-state policy has no such bound
(@sec:eq-finite).

For the context semantics, trace partitioning already allows overlapping, relational indices on
paper. Voblint adds their mechanization over activation-local traces together
with the exhaustiveness theorem. For end-to-end soundness, the missing context bound is
one reason the termination of the solve stays a per-program premise.

== Unverified analyzers and their testing <sec:rel-testing>

Most abstract interpreters in use are not mechanized. Astrée proves the absence
of run-time errors in safety-critical C programs of up to 132,000 lines, with
few or no false alarms, by refining a general analyzer for a program family
@blanchet03. It analyzes a call by abstract execution of the body at the call
point, which is equivalent to inlining since the programs do not use recursion
@blanchet03[§5.4]. #cite(<livshits15>, form: "prose") observe that realistic
whole-program analyses purposely make unsound choices and ask authors to state
the nature and extent of the unsoundness explicitly.

Testing checks such tools against executions. #cite(<cuoq12>, form: "prose")
run Frama-C on programs generated by Csmith, compare the value analysis used as
an interpreter with compiled execution and check printed invariants at run
time, and report fifty bugs found and fixed. #cite(<klinger19>, form: "prose")
compare analyzers on programs with synthesized assertions and find soundness or
precision issues in four of six, and #cite(<kaindlstorfer24>, form: "prose")
build oracles from sequences of analyzer queries and find 16 soundness issues
in seven of eight analyzers, including the abstract interpreter MOPSA. A test exposes a
defect on one program and cannot show its absence. Voblint's regression corpus
is testing of this kind (@sec:eval-corpus), and the Goblint defect replayed in
@sec:eval-1161 is the kind of transfer-function error that a per-operation
soundness obligation excludes inside the proof boundary.

For end-to-end soundness, these works show that a mature analyzer can pass
testing and still contain soundness defects. The proof
covers only the definitions it is about, and #cite(<cuoq12>, form: "prose")
note that such approaches assume a formal semantics of the analyzed language
@cuoq12[§1], which is the adequacy question of @sec:vimp-vs-c.

== Where Voblint sits <sec:where-voblint-sits>

Much of Voblint is inherited. The solver and the soundness proofs of its update
rules come from #cite(<tilscher26>, form: "prose"), the rules from
#cite(<stemmler25>, form: "prose"), side-effecting constraint systems from
#cite(<apinis12>, form: "prose"), and the local/global analysis architecture
from Goblint. Widening, narrowing and the reduced product are standard
@cousot77 @cousot79. The activation-local traces adapt the local traces of
@schwarz21 to procedure activations, and the context-indexed collecting
semantics is a relational covering in the sense of @rival07. Compared with
the works above, the scoped claims of @sec:contributions are the following.

- *End-to-end soundness.* No mechanized analyzer we found proves soundness of its exported
  executable for a language with recursive procedures under configurable
  context sensitivity. Verasco raises an alarm on recursion, the analyzer of
  #cite(<cachera05>, form: "prose") is context-insensitive, and the analysis of #cite(<dabrowski09>, form: "prose") is not
  executable.
- *Context semantics.* The relational context semantics with its totality condition extends
  the functional context module of @dabrowski09 and mechanizes, over
  activation-local traces, the relational coverings that @rival07 describe on
  paper.
- *Composition.* The certificate-based solver interface follows CompCert's. The
  three-way composition mechanizes a modular separation of the kind that
  @darais15 prove on paper for monadic interpreters.
- *Precision.* We found no machine-checked strict precision separation between
  configurations of one analyzer.

Each claim records an absence of evidence in the search described at the start
of this chapter. None of them is a priority claim.
