#import "../lib/code.typ": *
#import "../lib/theme.typ": vb
#import "../lib/math.typ": ctor
#import "../lib/alignment.typ": alignment


= Related Work <ch:related>

This chapter separates the parts of Voblint that come from earlier work from the
new ones. Most parts
have a precedent, from verified analyzers and solvers to Goblint and its
local-trace semantics. The new part is their connection in one mechanized
soundness proof (@sec:rel-summary). The literature was found through web and
OpenAlex searches. AI agents supported this work heavily, from the search
to checking each claim against its source
(#link(<ai-use>)[statement on the use of generative AI]).

== Unverified analyzers for C <sec:rel-practice>

The analyzers applied to real C programs are tested rather than proved
(@sec:state-of-art), and they differ from Voblint most in how they treat
procedures.
@tab:production-analyzers compares six of them with Voblint. Five of them claim
to be sound. Pulse-X is a bug finder instead. Its under-approximating
soundness theorem says that, in its formal model, every outcome described by
a procedure summary is reachable from some input satisfying that summary's
precondition. This theorem is proved on paper @le22[§§3.1, 4.1]. Four of the
analyzers reanalyze the callee at each call
@blanchet03[§5.4] @eva-manual[§5.3] @journault19[§5.1] @brat14[§3]. Inlining
cannot handle unbounded recursion, and these tools exclude recursion, unroll it
to a bounded depth, rely on user-written contracts, or assume that a recursive
call may change any value @blanchet03[§5.4] @eva-manual[§6.3.9]
@mopsa-manual[Limitations] (#link("https://github.com/NASA-SW-VnV/ikos/blob/ac7f7c1738976cabc58c6a53413df6e458995c38/analyzer/README.md#analysis-assumptions")[IKOS README]). Goblint and
Voblint, in contrast, keep one abstract state per program point and calling
context (@sec:intro-goblint), and Voblint's theorem covers recursive calls.

These tools are tested against independent evidence, such as
compiled execution, other analyzers, or the known verdicts of benchmark
programs. Such testing keeps finding errors. On eight analyzers for C and C++,
interrogation testing found 24 issues, 16 of them related to soundness, and
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
      [TD solver @stade24 @tilscher26],
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
    Pulse-X's _pure conditions_ constrain variable values separately from its
    assertions about allocated memory @le22[§3, Fig. 1].
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

CompCert and Verasco (@ch:intro) state their theorems about the code
that actually runs, and Voblint follows their pattern for a language with recursive procedures and
context-sensitive calls. CompCert is a compiler from Clight, a large subset of
C, to PowerPC assembly, programmed and proved correct in Coq, now Rocq
@leroy09. Its theorem is semantic preservation, so safety properties proved of
the source hold for the executable. The compiler is extracted to Caml and
linked with unverified parts. Leroy lists what remains trusted: the
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
Verasco bounds recursive computation in Coq by a natural-number parameter,
called _fuel_, which decreases at each recursive step. Its correctness theorem
holds for every finite fuel supply. The extracted OCaml analyzer instead uses
a cyclic value that never runs out, so a returned result consumes only a finite
prefix, to which the theorem applies @jourdan16phd[§1.2.4]. Termination is proved
only on paper @jourdan16phd[§§3.1.2, 4.3.1], so its theorem, like Voblint's
(@sec:certificate), covers only the results it returns.

The earlier value analysis of Blazy et al. @blazy13 does not verify its
fixpoint iterator. An untrusted OCaml implementation of Bourdoncle's iteration
strategy @bourdoncle93 computes a candidate, and a verified checker accepts it
as a post-fixpoint or falls back to top @blazy13[§4]. Voblint instead runs a
solver whose partial correctness is proved @tilscher26. The checker leaves the
iteration heuristics free and tests every result at run time. A verified
solver needs no such test, but its proof holds for that one algorithm.

== Mechanized abstract interpreters <sec:rel-mechanized>

@tab:state-of-art compares the mechanized abstract interpreters closest to
Voblint. Their proofs cover small or intermediate languages, from While and IMP
to C\#minor, and they differ from Voblint in recursion, contexts, and the
fixpoint computation. Three of the works have no procedures at all. Every work
in the table analyzes a call in at most one context. An analysis that splits a
call into several alternatives, however, needs one context for each alternative. Voblint's
context policy may therefore admit several contexts for one call, and its
semantics and proofs cover this case, although the shipped analyses do not use
it (@sec:contexts). Only Cachera et al. compute the fixpoint with a verified
solver, and that solver handles only ordinary inequations without side effects
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
      [functional policy], [specified], [no],
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
    _functional policy_ computes a context by a function, _summaries_ computes
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

Other works derive concrete and abstract interpreters from shared semantic
definitions @michelland24 @keidel18 @darais15.
Voblint instead splits analysis, context policy, and solver for a
constraint-based analyzer. Their composition bounds the stores collected in
each context by a solved abstract state (#isathm("activation_collect_dg_sound")). Executable verified analyzers are not
new either. Cachera and Pichardie extract theirs to OCaml @cachera10[§§1, 6],
and the analyzer of Franceschino et al. runs in a browser @franceschino21.
Other Isabelle developments verify conflict analysis @lammich07afp,
Horwitz--Reps--Binkley (HRB) interprocedural slicing @wasserrab09afp, and Shivers'
control-flow analysis @breitner10afp. A slice retains the parts of a program
that affect a selected observation. The slicing result uses a _weak simulation_
between the original and sliced graphs: it matches observable execution steps
while allowing unobservable steps between them. Voblint instead bounds stores
in each admitted calling context.

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
They also study a variant that aborts and restarts a right-hand-side evaluation
if an update destabilizes the unknown being evaluated, avoiding an answer
assembled from inconsistent reads. When global contributions accumulate
exactly by join and local unknowns use no widening or
narrowing, they prove minimality of the returned valuation and solved set.
This requires three monotonicity properties: increasing the input valuation
cannot decrease a right-hand side's result or side-effect contributions, or
remove any of its dependencies @tilscher26[§6]. CompCert similarly hides its
intraprocedural dataflow solvers behind a module type whose clients rely only
on fixpoint properties of the result @compcertKildall @laspina25.

Tilscher et al. prove termination for top-down solvers without side effects
over a finite set of unknowns, with further hypotheses on widening and
monotonicity @tilscher26jar[Thm. 2, Cor. 1]. These conditions have not been
established for Voblint (@sec:certificate). Seidl and Vogler prove on
paper that their side-effecting solver terminates when side effects target
only unknowns without a right-hand side and only finitely many unknowns are
encountered @seidl21[§9, Thm. 5]. Their result assumes widening and narrowing
operators whose iterations stabilize @seidl21[§3], so it does not carry over to
the joining rules, which never widen. Schulze Frielinghaus et al. give
a local solver that terminates on every non-recursive program
@schulzefrielinghaus18, and both programs whose solves exceed their time limits
in @sec:eval-precision are recursive.

Voblint reuses this solver and its proofs, connecting its certificate to source
executions as described in @sec:certificate and @sec:chain. The solver Voblint
runs warrows every local unknown at a widening point, so the least-solution
theorem does not apply, and Voblint uses only partial correctness and claims no
optimality (@sec:update-rules).

== Calling contexts and trace partitioning

Of the two classical approaches of Sharir and Pnueli (@sec:interproc), Voblint's
call-string policy follows the call-string approach, and its entry-state policy
resembles the functional approach tabulated per input @sharir81. At the return, Voblint combines the caller's state before the call with the
callee's exit state (@sec:calls), the shape of the return function of
#cite(<knoop92>, form: "prose", supplement: [§4.1]). Reps et al. solve such
problems precisely when the facts are finite and the transfer functions
distributive @reps95, whereas Voblint requires neither and proves no general
precision guarantee. Seidl and Fecht model procedures by a pushdown automaton that pushes an
activation record at each call and pops it at each return @seidl00[§4], and
Voblint's activation traces keep this structure per activation (@ch:traces).
The entry-state policy's unknowns, a node
paired with the abstract entry state of its procedure, resemble the unknowns
$⟨v, d⟩$ of their forward accumulation @seidl00[§7.1].

Trace partitioning abstracts a set of traces by indexing it with control
history before abstracting states @rival07. Rival and Mauborgne define both
partitions and coverings, in which one trace may belong to several indices,
and present calling-context sensitivity as one such indexing. Voblint's activation collecting semantics
forms an overlapping covering: a context policy may admit one activation in
several contexts. Voblint mechanizes the indexing over
activation traces and proves that the solved, routed result bounds the
activation collecting semantics of every admitted context. Contexts also
determine how many unknowns a solve creates. The context lifters of Erhard et
al. @erhard25 guarantee finitely many contexts whenever the solver updates each
unknown finitely often @erhard25[Abstract]. Voblint's entry-state policy has
no such bound, which is one reason the termination of the solve is not proved
(@sec:certificate).

== Goblint and its local-trace semantics <sec:rel-goblint>

Voblint follows Goblint's architecture and adapts the local traces of Schwarz
et al. to activations.

=== Correspondence with Goblint's architecture

Goblint uses the side-effecting constraint systems of @sec:side-effects
@seidl03 @apinis12 to decouple a mixed flow-sensitive analysis from the solver.
On the analysis side, a _digest_ is a total function that assigns each local
trace a summary value (@sec:rel-digests). Digests and the solver's update rules
recover precision @seidl26. Voblint adopts the split. An analysis supplies
the transfer behavior, and the solver applies one of the update rules of
@sec:update-rules.

The correspondence with Goblint's implementation is architectural. Voblint was compared
with the framework interface of Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/"
    + alignment.revision
    + "/src/framework/constraints.ml",
)[constraint generator]
at revision #raw(alignment.revision.slice(0, 8)) by source inspection. There,
a call runs the analysis's `enter`, selects the callee context from the
entry state, publishes it, and combines the callee's exit state with
the caller. Voblint's equations have the same four steps, with enter and
combine from the analysis (#isatype("dg_spec")) and the context chosen by the context
policy. This correspondence does not establish that the two compute the same
fixpoint. For instance, Voblint publishes the entry state to a global seed, which the
entry's local unknown reads back, whereas Goblint publishes it to the local entry
unknown directly. Under the warrowing rules the seed itself can be widened, so widening applies
at a different place than in Goblint, and it is not proved which of the two
is more precise. Voblint also resolves call targets statically, and its
analyses share one product state and one query kind without globals, whereas
Goblint's MCP also passes events, spawns, and per-analysis globals. No agreement rate between
the verdicts of the two analyzers is reported, since the corpus has not been
run through Goblint and the adapted fixtures record Goblint's annotations only
as prose.

Goblint's MCP (@sec:coop-mcp) also answers a query cycle with the top element
and caches answers per transfer
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/mCP.ml")[`mCP.ml`]
at revision `5320a6b7`). Voblint's combination follows this design and adds a
proof obligation per analysis that quantifies over every channel that holds.
Int uses an explicit reduced-product operator @cousot79 @rival20[§5.1.2]
(@sec:reduced-product). The cooperating analyses exchange facts through
queries, without a pair-specific reduction operator. Verasco threads its channels so that the second
domain can query the state the first has just computed @jourdan15[§7], whereas
Voblint's answers describe the predecessor state only, as Goblint's do.

=== Digests and the context relation <sec:rel-digests>

Local traces give each thread of a concurrent program a semantics against which
thread-modular analyses are proved sound and compared @schwarz21, and they
were later extended to relational analyses @schwarz23 @schwarz25phd[Ch. 6].
Voblint adapts them to procedure activations (@sec:activation-trace), which do
not interfere, so no concurrency result of that work transfers.

Schwarz refines the local-trace semantics through digests @schwarz25phd[§2.3].
The concrete semantics splits each program-point unknown $[u]$ into
unknowns $[u, A]$, collecting traces separately per digest value $A$.
Voblint's relation between activations and admitted contexts (@sec:contexts)
(#isaconst("activation_context_rel")) plays the role of the digest.
A digest assigns each trace exactly one value, yielding disjoint groups
@schwarz25phd[§2.3, Def. 4, Thm. 4]. Voblint may admit an activation in several
contexts, so its groups may overlap. Also, a digest is updated at every trace
step, whereas an activation's contexts are fixed at its call.

== Closest prior work and reused components <sec:rel-summary>

Two mechanized analyzers come closest to Voblint's combination of mixed flow
sensitivity and calling contexts. Cachera et al. @cachera05 combine a flow-insensitive heap with flow-sensitive
local state for Java Card bytecode, but their analysis is context-insensitive. #cite(<dabrowski09>, form: "prose")
prove in Coq that a context-sensitive points-to analysis with a
flow-insensitive heap is sound. Their concrete semantics is parameterized by a module of contexts.
Its call-context function computes the callee context from the call site,
caller's context, and receiver. The specification gives constraints without an
executable solver @dabrowski09[§7]. This context-parameterized semantics is
the closest precedent for Voblint's, which differs in three respects. Its
contexts are admitted by a relation; requiring a context for every call from a
covered store, together with the other coverage obligations, makes the union
of the context-indexed collecting sets equal the node collecting set (#isaconst("call_context_total_on"),
#isathm("node_collect_eq_Union_activation_collect")); and the
indexing is connected to an executable solver.

Voblint inherits its trust pattern from CompCert and Verasco, domain interface
from Nipkow and Klein @nipkow14[Sects. 13.5, 13.7], solver from Tilscher et al.
@tilscher26, update rules from Stemmler et al. @stemmler25, side-effecting
constraints from Seidl et al. @seidl03 and Apinis et al. @apinis12, widening,
narrowing, and reduced product from Cousot and Cousot @cousot77 @cousot79,
local traces from Schwarz et al. @schwarz21, and architecture from Goblint.
As far as the author is aware, no earlier mechanization connects source
semantics through context-indexed activation collecting semantics to
side-effecting constraints and a verified TD solver.
