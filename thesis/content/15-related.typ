#import "../lib/code.typ": *
#import "../lib/theme.typ": vb
#import "../lib/alignment.typ": alignment, alignment-count


= Related Work <ch:related>

Most parts of Voblint build on earlier work, from verified analyzers and
solvers to Goblint and its local-trace semantics. The sections below compare
each line of work with Voblint and separate what Voblint inherits from what it
adds. The literature was found through web and OpenAlex searches. AI agents supported this work heavily, from the search
to checking each claim against its source
(#link(<ai-use>)[statement on the use of generative AI]).

== Unverified analyzers for C <sec:rel-practice>

Most analyzers applied to real C programs have no machine-checked soundness
proof, and they differ from Voblint most in how they treat procedures.
@tab:production-analyzers compares six of them with Voblint. Five of them claim
to be sound. Pulse-X is a bug finder instead, and its under-approximating
soundness theorem is proved on paper @le22[pp. 81:2--81:3]. Four of them inline
the callee at every call and therefore need no context policy
@blanchet03[§5.3] @eva-manual[§5.3] @journault19[§5.1] @brat14[§3]. Inlining
cannot handle unbounded recursion, and these tools exclude recursion, unroll it
to a bounded depth, rely on user-written contracts, or assume that a recursive
call may change any value @blanchet03[§5.3] @eva-manual[§6.3.9]
@mopsa-manual[Limitations] @ikos-readme[Analysis Assumptions]. Goblint, in
contrast, keeps one abstract state per program point and calling context and
analyzes recursive programs.

Without a proof, these tools are tested against independent evidence, such as
compiled execution, other analyzers, or the known verdicts of benchmark
programs. Such testing keeps finding errors. On eight analyzers for C and C++,
metamorphic testing found 24 issues, 16 of them related to soundness, and
seven of the analyzers had soundness issues, MOPSA among them
@kaindlstorfer24[p. 326, Tab. 2; p. 329].

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
      [Pulse-X @le22], [C], [bug finding], [summaries], [unrolled], [pure conditions],
      [one domain], [none],
      [Goblint @saan23], [C], [sound], [per context], [analyzed], [Apron], [products, queries],
      [TD algorithm],
      table.hline(stroke: 0.4pt),
      [*Voblint*], [VIMP], [proved sound], [per context], [covered], [order analysis],
      [products, queries], [end to end],
      table.hline(stroke: 0.5pt),
    )
  },
  kind: table,
  placement: auto,
  caption: [Unverified analyzers and Voblint, as described by each tool's papers
    and documentation. _Stance_ is the tool's own soundness claim. Under
    _calls_, inlining reanalyzes the callee at every call, a summary is
    computed once per procedure, and _per context_ means one abstract state
    per program point and context. _Recursion_ says how a recursive call is
    treated. _Analyzed_ means the tool analyzes recursive calls, and _covered_
    means that Voblint's theorem includes them. _Relational_ names the domains
    that relate variables. Apron is a library of relational numeric domains,
    and Voblint's order analysis tracks which variable is at most which.
    _Combination_ names how domains exchange facts. Astrée's domains send each
    other constraints through reduction channels, Eva's domains communicate
    through the abstract values of expressions, a product runs domains side by
    side on one state, and a query lets one analysis ask another for a fact
    at the current point. _Mechanized_ records what a proof assistant has
    checked. _End to end_ means from source
    executions to the verdicts of the exported function, for every answer it
    returns (partial correctness) and with the trusted components of
    @fig:intro-trust.],
) <tab:production-analyzers>

== Verified analyzers in the CompCert line

CompCert and Verasco state their theorems about the tool that users run, and
Voblint follows their pattern for a language with recursive procedures and
context-sensitive calls. CompCert is a compiler from Clight, a large subset of
C, to PowerPC assembly, programmed and proved correct in Coq, now Rocq
@leroy09. Its theorem is semantic preservation, so safety properties proved of
the source hold for the executable. The compiler is extracted to Caml and
linked with unverified parts, and Leroy lists what remains trusted: the
semantics of Clight and of the PowerPC assembly, the CIL-based parser, the
assembler and the linker, and Coq's extraction together with the Caml compiler
and run-time system @leroy09[§5]. Voblint's guarantee has the same shape, a
theorem about the function the tool runs, code generated from the prover, and
an explicit list of trusted components (@fig:intro-trust). Analyzer soundness
is weaker than compiler correctness, however, since it only over-approximates
the behavior of a program, so a coarser result remains sound.

Verasco is a Coq-verified analyzer for most of ISO C99, excluding recursion
and dynamic allocation, that proves the absence of run-time errors @jourdan15.
Its abstract interpreter iterates over the structure of C\#minor, a CompCert
intermediate language, and CompCert's semantic preservation extends the
guarantee to compiled code. Verasco covers a far larger language, so the
comparison concerns design only. Verasco reanalyzes functions at every call
site and raises an alarm at a possible recursive call (@tab:state-of-art,
@jourdan15[§4]). In Voblint, calls instead become equations over unknowns
indexed by program point and context, which a generic solver computes.
Verasco's extracted analyzer runs with unbounded fuel, and termination is
proved only on paper @jourdan16phd[§§3.1.2, 4.3.1], so its theorem, like
Voblint's (@sec:certificate), covers only the results it returns.

The earlier value analysis of Blazy et al. @blazy13 does not verify its
fixpoint iterator. An untrusted OCaml implementation of Bourdoncle's iteration
strategy @bourdoncle93 computes a candidate, and a verified checker accepts it
as a post-fixpoint or falls back to top @blazy13[§4]. Voblint instead runs a
solver whose partial correctness is proved @tilscher26. The checker leaves the
iteration heuristics free and tests every result at run time. A verified
solver needs no such test, but its proof holds for that one algorithm.

== Mechanized abstract interpreters <sec:rel-mechanized>

Abstract interpreters have been mechanized in several provers.
@tab:state-of-art compares those most closely related to Voblint. Their proofs
cover small or intermediate languages, from While and IMP to C\#minor, and the
differences that matter for Voblint lie in recursion, contexts, and the
fixpoint computation. Three of the works have no procedures at all. In every work of the table, a call is analyzed in at most one context. An
analysis that splits a call into several alternatives, however, needs one
context for each. Voblint's context policy may therefore admit several
contexts for one call, and its semantics and proofs cover this case, although
the shipped analyses do not use it (@sec:contexts). Only Cachera et al. compute the fixpoint with a verified
solver, and that solver handles ordinary inequations, not side-effecting ones
@cachera05.

#figure(
  {
    set text(size: 9pt)
    set par(justify: false, leading: 0.45em)
    table(
      columns: (auto, auto, auto, auto, auto, auto, auto),
      align: (col, _) => (if col == 0 { left } else { center }) + horizon,
      stroke: none,
      inset: (x: 2.4pt, y: 2.6pt),
      table.hline(stroke: 0.5pt),
      [*Work*], [*Prover*], [*Language*], [*Recursion*], [*Contexts*], [*Fixpoint*],
      [*Executable*],
      table.hline(stroke: 0.4pt),
      [Verasco @jourdan15], [Coq], [C\#minor], [alarm], [per call site], [structural],
      [yes],
      [Blazy et al. @blazy13], [Coq], [Cminor CFG], [covered], [intraprocedural],
      [checked], [yes],
      [Cachera et al. @cachera05], [Coq], [Java Card], [covered], [none], [solver],
      [yes],
      [Cachera, Pichardie @cachera10], [Coq], [While], [no procedures], [none],
      [structural], [yes],
      [Dabrowski, Pichardie @dabrowski09], [Coq], [Java-like], [covered],
      [object-sensitive], [specified], [no],
      [Nipkow, Klein @nipkow14], [Isabelle], [IMP], [no procedures], [none],
      [iterator], [in prover],
      [Lammich, Müller-Olm @lammich07afp], [Isabelle], [flowgraphs], [exact],
      [summaries], [specified], [no],
      [Franceschino et al. @franceschino21], [F\*], [IMP], [no procedures], [none],
      [structural], [yes],
      table.hline(stroke: 0.4pt),
      [*Voblint*], [Isabelle], [VIMP], [covered], [set per call], [TD solver], [yes],
      table.hline(stroke: 0.5pt),
    )
  },
  kind: table,
  placement: auto,
  caption: [Mechanized abstract interpreters with machine-checked soundness
    proofs, as described in each work. _Prover_ is the proof assistant and
    _Language_ the analyzed language. _Recursion_ says how a recursive call is
    treated: _alarm_ raises an alarm, _covered_ means the theorem includes
    recursive programs, _exact_ interprets calls and returns exactly, and _no
    procedures_ means the language has none. _Contexts_ says how calls are
    distinguished: _per call site_ reanalyzes a function at every call site,
    _object-sensitive_ computes contexts by a function, _summaries_ computes
    one summary per procedure, _set per call_ lets the context policy return
    several contexts for one call, and _none_ and _intraprocedural_ mean that
    calls are not distinguished or not analyzed. _Fixpoint_ says how the
    result is computed: _structural_ iterates over the program's syntax,
    _iterator_ over the whole annotated program, _checked_ verifies the result
    of an untrusted iterator, _solver_ and _TD solver_ use a verified solver,
    and _specified_ only states the constraints. _Executable_ says whether the
    analyzer runs outside the prover.],
) <tab:state-of-art>

Nipkow and Klein develop abstract interpretation in Isabelle/HOL over annotated
commands of the While language IMP @nipkow12 @nipkow14. A collecting semantics
annotates each program point with a set of states, and an abstract interpreter
annotates it with an abstract state. Their interpreter is parametric in a
domain of abstract values. The domain supplies abstract and inverse operations
with their soundness laws, and the interpreter derives forward evaluation, the
backward filtering of guards, and the step of each command generically
@nipkow14[Sects. 13.5, 13.7]. Voblint's non-relational domains follow this
pattern (@sec:domain-contract). Its collecting semantics, however, ranges over
activation traces of a procedure-aware control-flow graph (@ch:traces),
because a return must know which caller resumes.

Other works make soundness proofs reusable by sharing one interpreter between
the concrete and the abstract semantics @michelland24 @keidel18 @darais15.
Voblint instead splits analysis, context policy, and solver for a
constraint-based analyzer and composes them in one theorem,
#isathm("activation_collect_dg_sound"). Executable verified analyzers are not
new either. Cachera and Pichardie extract theirs to OCaml @cachera10[§§1, 6],
and the analyzer of Franceschino et al. runs in a browser @franceschino21.
Interprocedural analyses have also been verified in Isabelle before
@lammich07afp @wasserrab09afp @breitner10afp. None of these entries claims an
extracted analyzer, however, and none of their semantics represents one
activation with its caller chain, the object Voblint's context relation reads.

== Verified solvers and termination results <sec:rel-solvers>

A verified solver guarantees a property of its result for arbitrary
equations, and the analyzer must give the equations their meaning. Hofmann et
al. verify the local generic solver RLD in Coq @hofmann10, and de Vilhena et
al. verify in Iris a local solver that discovers dependencies dynamically
@devilhena20. Stade et al. prove the top-down solver partially correct in
Isabelle/HOL @stade24. Tilscher et al. @tilscher26 extend this line to
$"TD"_"side"$, which accepts contributions to global unknowns, verify it
against a generic interface for update rules, prove five update rules of
Stemmler et al. @stemmler25 sound, and refine the solver to executable code.
For updates without widening and narrowing, they also prove that a terminating
solve returns the least partial post-solution. CompCert similarly hides its
intraprocedural dataflow solvers behind a module type whose clients rely only
on fixpoint properties of the result @compcertKildall @laspina25.

Termination results exist, but none applies to Voblint. Tilscher et al. prove
termination for top-down solvers without side effects over a finite type of
unknowns @tilscher26jar[Thm. 2, Cor. 1], whereas Voblint's unknowns pair nodes
of an infinite type with contexts (@sec:certificate). Seidl and Vogler prove on
paper that their side-effecting solver terminates when side effects target
only unknowns without a right-hand side and only finitely many unknowns are
encountered @seidl21[§9, Thm. 5]. Their result assumes widening and narrowing
operators whose iterations stabilize @seidl21[§3], so it does not carry over to
the joining update rules, which never widen. Schulze Frielinghaus et al. give
a local solver that terminates on every non-recursive program
@schulzefrielinghaus18, and both programs whose solves exceed their time limits
in @sec:eval-precision are recursive.

Voblint includes a copy of the solver of @tilscher26, whose algorithm, update
rules, and proofs belong to that work, and connects its certificate
#isaconst("part_post_solution", thy: "Basics_side") to the program. The
certificate implies coverage of the concrete traces, and compiler correctness
transfers the coverage to source executions. The solver Voblint runs warrows every local
unknown at a widening point, so the least-solution theorem does not apply, and
Voblint uses only partial correctness and claims no optimality
(@sec:update-rules).

== Calling contexts and trace partitioning

An interprocedural analysis must decide how information about a call reaches
the callee and returns to the caller. Sharir and Pnueli distinguish two
classical answers @sharir81. The functional approach computes input-output
relations for procedures, and the call-string approach tags information with
the history of calls that led to it. Voblint's call-string policy follows the
second approach, and its entry-state policy, which indexes a callee's results
by its entered state, resembles a functional approach tabulated per input. At
the return, Voblint combines the caller's state before the call with the
callee's result (@sec:calls), the shape of the return function of
#cite(<knoop92>, form: "prose", supplement: [§4.1]). Reps et al. solve such
problems precisely when the facts are finite and the transfer functions
distributive @reps95, whereas Voblint requires neither and proves no precision
result.

Trace partitioning abstracts a set of traces by indexing it with control
history before abstracting states @rival07. Rival and Mauborgne define both
partitions and coverings, in which one trace may belong to several indices,
and present calling-context sensitivity as one such indexing. They also note
that the function mapping tokens to tokens in a covering may be replaced by a
relation @rival07[Rem. 3.2.4]. Voblint's context-indexed collecting semantics
is a covering of this relational kind, since a context policy may admit one
activation in several contexts. Voblint mechanizes the indexing over
activation traces and proves that the solved, routed result bounds the
activation collecting semantics of every admitted context. Contexts also
determine how many unknowns a solve creates. The context lifters of Erhard et
al. @erhard25 guarantee finitely many contexts whenever the solver updates each
unknown finitely often @erhard25[Abstract]. Voblint's entry-state policy has
no such bound, which is one reason the termination of the solve is not proved
(@sec:certificate).

== Goblint and its local-trace semantics <sec:rel-goblint>

Voblint follows Goblint's architecture and adapts the local-trace semantics of
Schwarz et al. to procedure activations.

=== Correspondence with Goblint's architecture

Side-effecting constraint systems let one equation both define a local unknown
and publish contributions to global unknowns @seidl03 @apinis12. Seidl et al.
@seidl26 describe how Goblint uses them to decouple a mixed flow-sensitive
analysis from the solver, with digests on the analysis side and update rules on
the solver side recovering precision. Voblint adopts the split. An analysis
supplies local and global transfer behavior, and the generator and solver
organize their interaction.

The correspondence with Goblint's implementation is architectural. Voblint was compared
with the framework interface of Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/"
    + alignment.revision
    + "/src/framework/constraints.ml",
)[constraint generator]
at revision #raw(alignment.revision.slice(0, 8)) by source inspection. There,
a call runs the analysis's `enter`, selects the callee context from the
entered state, publishes the callee entry, and combines the callee's exit with
the caller. Voblint's equations have the same four steps, with enter and
combine from the D/G specification and the context chosen by the routing
policy. The project site's side-by-side comparison
(#link(site("#goblint"))[site]) lists #alignment.rows.len() Goblint
constructs. Of these, #alignment-count("modeled") are modeled,
#alignment-count("simplified") simplified, and #alignment-count("absent") not
modeled. No row claims that the two compute the same fixpoint.

Where Voblint simplifies Goblint, its results do not carry over directly. For
instance, Voblint publishes the callee entry to a global seed, which the
entry's local unknown reads back, whereas Goblint writes the local entry
directly. Under the warrowing rules the seed itself can be widened, so widening applies
at a different place than in Goblint, and it is not proved which of the two
is more precise. Voblint also resolves call targets statically, and its
analyses share one combined state and one query kind without globals, whereas
Goblint's MCP also passes events, spawns, and per-analysis globals. No agreement rate between
the verdicts of the two analyzers is reported, since the corpus has not been
run through Goblint and the adapted fixtures record Goblint's annotations only
as prose.

Goblint's MCP (@sec:coop-mcp) also answers a query cycle with the top element
and caches answers per transfer
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/mCP.ml")[`mCP.ml`]
at revision `5320a6b7`). Voblint's combination follows this design and adds a
proof obligation per analysis that quantifies over every sound query channel.
Unlike a reduced product @cousot79 @rival20[§5.1.2], which Int uses
(@sec:reduced-product), the combined state keeps separate carriers and
exchanges facts only through answers, so no reduction operator has to be
proved for a pair of analyses. Verasco threads its channels so that the second
domain can query the state the first has just computed @jourdan15[§7], whereas
Voblint's answers describe the predecessor state only, as Goblint's do.

=== Digests and the context relation

Local traces give each thread of a concurrent program a semantics against which
thread-modular analyses are proved sound and compared @schwarz21, later
extended to relational analyses @schwarz23 @schwarz25phd[Ch. 6].
@sec:activation-trace described how Voblint adapts them to procedure
activations. Activations do not interfere, so no concurrency result of that
work transfers. #cite(<sotin11>, form: "prose") also replace a stack semantics
by a local one, motivated by pointers into the stack, which VIMP lacks.

Schwarz refines the local-trace semantics through _digests_
@schwarz25phd[§2.3]. A digest is a total function on local traces, and the
concrete semantics already splits each unknown $[u]$ of a program point into
unknowns $[u, A]$, one per digest value $A$. The collecting semantics thus
keeps one set of traces per program point and digest value, much as Voblint's
activation collecting semantics keeps one per node and context. Voblint's
context relation #isaconst("activation_context_rel") (@sec:contexts) plays the
role of the digest for procedure activations, and it differs in two ways.
First, a digest is a function, so each trace has exactly one digest value and
the traces split into disjoint groups @schwarz25phd[§2.3, Def. 4, Thm. 4]. The
context relation, in contrast, may admit one activation in several contexts,
so Voblint's groups may overlap. Second, a digest is updated at every step of a
trace, whereas an activation's contexts are fixed when it is called, so
Voblint distinguishes activations only by how they were entered.

== Closest precedents and inherited parts <sec:rel-summary>

Two mechanized analyzers come closest to Voblint's combination of mixed flow
sensitivity and calling contexts. Cachera et al. @cachera05 combine a flow-insensitive heap with flow-sensitive
local state for Java Card bytecode, but their analysis is context-insensitive. #cite(<dabrowski09>, form: "prose")
prove in Coq that a context-sensitive points-to analysis with a
flow-insensitive heap is sound. They instrument the concrete semantics with
contexts through a Coq functor over a module type of contexts, whose
call-context function computes the context of a callee from the call site, the
caller's context, and the receiver. Their specification is not executable, however, since the analyses are given
only as constraints that no solver computes @dabrowski09[§7]. This concrete
semantics, which carries contexts and is parameterized by a context policy, is
the closest precedent for Voblint's. Voblint's differs in three respects. Its
contexts are admitted by a relation, the totality condition
#isaconst("call_context_total_on") makes the context-indexed collection
exhaustive (#isathm("node_collect_eq_Union_activation_collect")), and the
indexing is connected to an executable solver.

Voblint thus takes its trust pattern from CompCert and Verasco, its domain
interface from Nipkow and Klein @nipkow14[Sects. 13.5, 13.7], its solver from
Tilscher et al. @tilscher26, its update rules from Stemmler et al.
@stemmler25, side-effecting constraint systems from Seidl et al. @seidl03 and
Apinis et al. @apinis12, widening, narrowing, and the reduced product from
Cousot and Cousot @cousot77 @cousot79, its activation traces from the local
traces of Schwarz et al. @schwarz21, and its architecture from Goblint. As far as the author is aware, the connection between these parts has not been mechanized
before, namely a soundness proof that leads from a source semantics, through a
context-indexed collecting semantics over activation traces, to a
side-effecting constraint system and its verified solver.
