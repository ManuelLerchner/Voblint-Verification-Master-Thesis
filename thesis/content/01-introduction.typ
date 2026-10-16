#import "../lib/code.typ": fixture, isaconst, isalocale, isathm, isatype, listing, oblig
#import "../lib/figures.typ": check-row, partref, verdict
#import "../lib/sources.typ": proved
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/claims.typ": claim-ref

= Introduction <ch:intro>

A static analyzer answers questions about every execution of a program at once:
whether a divisor can be zero at some point, or whether a check always holds.
The analyzer
is itself a program, and an error in a transfer operation, in the
treatment of a call, or in the reading of the computed state produces a
confident answer that real executions contradict. Goblint #link("https://github.com/goblint/analyzer/issues/1156")[issue 1156] reports
that Goblint claimed `c % 2 == 1` for $c in {-5, -7}$ @goblint1156, although
the truncating remainder of C11 @iso-c11[§6.5.5p6] gives $-1$. #link("https://github.com/goblint/analyzer/pull/1161")[Pull request
  1161] fixed the congruence domain, which had ignored the sign of the dividend
@goblint1161. A user who trusts such an answer has no reason to look for the
bug it hides, whereas an imprecise answer only leaves the check undecided.
This thesis asks under which assumptions the answers of an executable analyzer
are sound for every execution of the analyzed program.

Formal verification states such a claim as a proposition over explicit
definitions, and a proof assistant checks its proof @nipkow14. Isabelle/HOL
constructs every theorem through a small trusted inference kernel, following
the LCF approach @paulson19, so the kernel accepts a proof regardless of who or
what wrote it. This matters now that LLM coding agents produce large
formalizations. Bryant et al. @bryant26munkres report agents that wrote over
85,000 lines of Isabelle/HOL covering Munkres' general topology, with all 806
results proved. This thesis was developed with AI assistance as well (see
#link(<ai-use>)[Use of Generative AI]), and its proofs pass the same check.

The kernel guarantees only that the formal statement follows from the
definitions. Whether the definitions model the intended objects, and whether
the statement expresses the intended claim, is left to human review. A review
of parts of the Munkres formalization found definitions logically weaker than
the textbook's, harmless only because each theorem assumes the missing
constraints again @bryant26munkres[§8.1].

Verification projects therefore state this boundary explicitly. The seL4 proof
relates the kernel's C implementation to an abstract specification in
Isabelle/HOL and names the compiler, assembly code, boot code, cache
management, and hardware as assumptions @klein09. Voblint, the analyzer this
thesis verifies, draws its boundary at the source language. Its main theorem
starts from _source executions_, the executions of the elaborated program
under the small-step semantics #isaconst("pstep") of Voblint's input language
VIMP. _Elaboration_ translates the parsed program into core VIMP with explicit
integer kinds. Every later representation is connected to source executions
by proof, so only elaboration and #isaconst("pstep") need an adequacy
argument. That argument states which fragment of C they model, where they
depart from C11 (@sec:vimp-vs-c), and why no existing verified semantics
serves as the anchor. IMP2 @lammich19imp2, for instance, represents operators
by HOL functions, which an executable analyzer cannot inspect to choose its
abstract operation.

== From executions to static guarantees

Software is usually checked by testing. A failing test demonstrates a bug, but
a passing test suite has observed only finitely many executions
@rival20[§1.4.1], and a test of an analyzer says nothing about the next
program it analyzes. A static analysis reasons about all
executions instead. At each program point it computes an _abstract state_, a
finite representation of a set of program states, for instance an interval
that contains every value a variable takes whenever execution reaches the
point. The analysis is _sound_ if the abstract state contains every state that
occurs in a real run, although it may contain more. If a sound abstract state
contains no state that violates a check, no execution violates it, tested or
not (@fig:intro-runs). The converse does not hold.
An abstract state can contain violating states that no execution reaches, and
the analysis then cannot decide the check even when every execution satisfies
it.

Suppose the analysis computes $x in [43, +infinity]$ at a point that divides
by `x`. Every execution reaching the point has $x >= 43$, so the division is
safe. If it computes only $x in [0, 100]$, the abstract state contains $x = 0$
and the division stays unproved, although every real execution may still have
$x >= 43$, for instance because of a relation to another variable that an
interval cannot express.

#figure(
  image("/shared/generated/svg/runs.svg", width: 100%),
  placement: none,
  caption: [Testing and static analysis, schematically. Each curve is one
    execution, and the vertical axis stands for the program state over time.
    Left: tests observe only the runs they execute, and a run on an input nobody
    tried (dashed) stays unknown. Right: a sound analysis result (shaded)
    contains every run, tried or not, and may also contain states that no run
    reaches. Because it does not overlap the bad states, no execution can reach
    them.],
) <fig:intro-runs>

For a general-purpose language this incompleteness is unavoidable. By Rice's
theorem, no algorithm decides a nontrivial semantic property for every program
of a Turing-complete language @rice53 @rival20[§1.3.3]. A sound analysis
therefore permits false alarms and undecided checks but no false claims, and it
is useful as long as it decides the checks of interest often enough
@rival20[§1.3.5]. Since every sound analysis over-approximates the same
executions, analyses can specialize. One tracks intervals, another parities,
another relations between variables, and a check that any one of them proves
holds in every run. An analysis can also separate the activations of a
procedure by their _calling context_, an abstraction of how the call was
reached such as the call site or the abstract state at entry, and keep one
abstract state per program point and context. A richer domain or more contexts
decide more checks but enlarge the analysis, and with very many contexts it may
not finish in practice.

Voblint answers every check that the user writes into the source program as a
statement `__voblint_check(e);`. It also warns at every arithmetic operation
where it cannot exclude a hazard: a zero divisor, a signed overflow, or a
conversion that changes a value. @fig:intro-answers shows a run in the
#link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html")[browser
  playground] together with what each answer guarantees. Only #verdict("DEAD")
makes a claim about reachability, and #verdict("REFUTED") is not a verified
counterexample. Each run fixes an analysis configuration: the abstract domain
(Sign, Interval, Parity, Congruence, or the reduced-product domain Int), the
context policy that chooses the contexts, and the rule that combines
contributions to global values. The run shown uses intervals without calling
contexts.

#let _ans-warn = check-row("intro-answers", cond: "WARNING")
#let _ans-proved = check-row("intro-answers", cond: "0 <= p && p <= 100")
#let _ans-refuted = check-row("intro-answers", cond: "p > 100")
#let _ans-unknown = check-row("intro-answers", cond: "p == 50")
#let _ans-dead = check-row("intro-answers", cond: "p == 0")
#let _ans-run = json("/shared/generated/playground/playground.json").clamp
// Line numbers are read from the screenshot's own program, so the table cannot
// drift from the image; a needle must match exactly one line.
#let _ans-src = read("/shared/generated/playground/" + _ans-run.program).split("\n")
#let _line(needle) = {
  let hits = _ans-src.enumerate().filter(((i, l)) => l.contains(needle))
  assert(hits.len() == 1, message: "clamp line for " + needle + ": " + str(hits.len()) + " matches")
  str(hits.first().first() + 1)
}
#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    let tag(color, body) = box(
      inset: (x: 3pt, y: 2pt),
      radius: 2pt,
      stroke: 0.6pt + color,
      fill: color.lighten(90%),
      text(size: 7.5pt, weight: "bold", fill: color, body),
    )
    grid(
      columns: (56%, 1fr),
      column-gutter: 8pt,
      align: horizon,
      link(_ans-run.url, image("/shared/generated/playground/" + _ans-run.image, width: 100%)),
      table(
        columns: (auto, auto, 1fr),
        align: (right + horizon, left + horizon, left + horizon),
        stroke: none,
        inset: (x: 3pt, y: 2.5pt),
        table.hline(stroke: 0.5pt),
        [*Line*], [*Answer*], [*What it guarantees*],
        table.hline(stroke: 0.4pt),
        [#_line("check(0 <= p && p <= 100)")], verdict(_ans-proved.verdict),
        [the condition holds whenever a run reaches it],
        [#_line("check(p > 100)")], verdict(_ans-refuted.verdict),
        [the condition fails whenever a run reaches it; not a counterexample],
        [#_line("check(p == 50)")], verdict(_ans-unknown.verdict), [nothing],
        [#_line("check(p == 0)")], verdict(_ans-dead.verdict),
        [no run reaches the check],
        [#_line("1000 / p;")], tag(vb.verdict-warning, raw(_ans-warn.cond)),
        [a zero divisor could not be excluded; no run is shown to divide by zero],
        [#_line("1000 / (p + 1)")], tag(vb.muted, [none]),
        [no run reaching this point divides by zero],
        table.hline(stroke: 0.5pt),
      ),
    )
  },
  kind: image,
  placement: none,
  caption: [One analyzer run on a clamp function, as the browser playground
    shows it, with the interval domain and no calling contexts. The analysis
    covers every value of `t` at once. The screenshot opens the run in the
    playground, as does the #box[`VIMP ↗`] tag on every later VIMP listing
    (claim #claim-ref("intro-answers"), fixture
    #fixture("24-site-figures/precision/48-clamp_every_answer.vimp")).],
) <fig:intro-answers>

== State of the art <sec:state-of-art>

Most abstract interpreters in use have no machine-checked soundness proof and
earn trust by testing. Livshits et al. @livshits15 observe that realistic
whole-program analyses purposely make unsound choices and ask authors to state
the nature and extent of the unsoundness.

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
  placement: bottom,
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
    @sec:trust-boundary.],
) <tab:production-analyzers>

@tab:production-analyzers compares Voblint with six analyzers that have no
machine-checked soundness proof. Four of them handle a call by inlining, which
reanalyzes the callee at every call and so never needs a context policy
@blanchet03[§5.3] @eva-manual[§5.3] @journault19[§5.1] @brat14[§3]. Astrée,
which proves the absence of run-time errors in C programs of up to 132,000 lines
@blanchet03, targets programs without recursion @blanchet03[§5.3]. For
recursion, Eva relies on a user-written contract or unrolls to a given depth
@eva-manual[§6.3.9], MOPSA has no support @mopsa-manual[Limitations], and IKOS
assumes that a recursive call may update any value in memory
@ikos-readme[Analysis Assumptions]. Goblint, like Voblint, keeps one abstract
state per program point and context and analyzes recursive programs. Pulse-X,
built from Infer on incorrectness logic, has an under-approximating soundness
theorem proved on paper, by which reported errors are real within a formal
model @le22[pp. 81:2--81:3].

Such tools are checked against executions. Cuoq et al. @cuoq12 compare
Frama-C's value analysis with compiled execution on programs generated by
Csmith and report fifty bugs found and fixed. By differential testing, which
flags answers on which analyzers disagree, Klinger et al. @klinger19 find
soundness or precision issues in four of six analyzers, and Kaindlstorfer et
al. @kaindlstorfer24 find 16 soundness issues in seven of eight, including MOPSA.
Goblint had no incorrect result in five years of SV-COMP, yet its developers
report soundness issues its benchmarks missed @saan26phd[§3.4.6]. The Goblint
defect at the start of this chapter is an error in one abstract operation, the
kind that a per-operation soundness obligation excludes inside the proof
boundary.

CompCert provides a precedent for a theorem about a delivered tool. It proves
that its compiled code behaves as the source semantics specifies and lists the
components that remain trusted @leroy09. Verasco carries the approach to a
static analyzer for C @jourdan15. For Goblint, local traces give each thread a
concrete semantics against which its thread-modular analyses are proved sound
on paper @schwarz21 @schwarz23 @schwarz25phd[Ch. 6].

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
  placement: bottom,
  caption: [Mechanized abstract interpreters with machine-checked soundness
    proofs. The text explains the entries. @ch:related gives
    the details.],
) <tab:state-of-art>

@tab:state-of-art compares the mechanized abstract interpreters closest to
Voblint. For _recursion_, Verasco @jourdan15 raises an alarm where a recursive
call can occur, Lammich and Müller-Olm @lammich07afp interpret calls and
returns exactly, and the theorems of Blazy et al. @blazy13 (whose analysis is
intraprocedural), Cachera et al. @cachera05, Dabrowski and Pichardie
@dabrowski09, and Voblint quantify over all programs, recursive ones included.
For _contexts_, Verasco reanalyzes a function at every call site, Dabrowski and
Pichardie compute object-sensitive contexts by a function, and Lammich and
Müller-Olm use per-procedure summaries. Voblint's context policy instead
returns a set of contexts per call ("set per call"), since an analysis may
split one call into several alternatives. For the _fixpoint_, three analyzers iterate over the
program's syntax ("structural"), Nipkow and Klein over the whole annotated
program, Blazy et al. check the result of an untrusted iterator, Cachera et
al. use a verified solver of ordinary inequations, and two works only specify
constraints.

Voblint's architecture follows Goblint, an abstract interpreter for
multithreaded C programs @vojdani16 @seidl26. Goblint defines analyses
independently of the generic solvers that compute their results. The
interface between the two is a side-effecting constraint system @seidl03
@apinis12 @seidl26, which relates unknown abstract values by inequalities and
lets the inequality of one unknown also contribute to others. Goblint's
top-down solver, including its extension to side effects, has been formalized
and proved partially correct in Isabelle/HOL @stade24 @tilscher26. When it
terminates, it returns values that satisfy the inequalities of the queried
unknown and of every unknown it transitively reads
(#isaconst("part_post_solution", thy: "Basics_side")). Whether that system
describes the program, and whether the verdicts read off its solution hold,
lies outside the solver's theorem.

Calling contexts add a further gap, since the per-context abstract states of
an analyzer have no counterpart in an ordinary concrete semantics. Suppose
`main` calls `bump(5)` and `bump(4)`, and `bump` returns its argument plus
one. An analysis whose contexts record the argument at entry claims the result
$6$ in the first context and $5$ in the second. The collecting semantics at
the point where `bump` returns holds both results, and neither it nor the call
stack of a run says which store belongs to which context. To state these
claims, the concrete semantics must record the context of every _activation_,
one execution of a procedure from its call to its return.

To our knowledge, no prior mechanized analyzer connects a source semantics to
a side-effecting constraint system or is proved sound through a verified
solver for such systems. Among the works of @tab:state-of-art, Dabrowski and
Pichardie come closest on contexts. Their context function is a parameter of
the concrete semantics, but it gives each call exactly one context, and their
analyses are constraints that no solver computes @dabrowski09[§7]. Voblint's
theorem combines four properties that no work in the table has together. It
covers recursive procedures, takes the context policy as a parameter that may give one call
several contexts, goes through a verified solver, and holds for the executable
analyzer. It is also stated over source executions, whereas Verasco's theorem
concerns C\#minor, an intermediate language of CompCert. Voblint claims no
better precision than any of these tools. Its language VIMP has no pointers or
heap and is far smaller than the C, C++, and Python dialects the unverified
tools accept, which Astrée and IKOS have applied to safety-critical control
software @blanchet03 @brat14[§3].

== Contributions <sec:contributions>

The contribution is the Isabelle/HOL formalization of Voblint and its
machine-checked soundness proof, available at
#link(
  "https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis",
)[`github.com/ManuelLerchner/Voblint-Verification-Master-Thesis`]
and archived on Zenodo @voblint. The proof follows every execution through
each representation the analyzer uses: the source program, its control-flow
graph, the equations over abstract states, and the reported verdicts. Each
change of representation may add states that no execution reaches, which costs
precision, but must not lose a reachable state. A compiler that drops an edge,
a return to the wrong caller, a solver that stops before its equations hold, or
a verdict read at the wrong program point would each lose an execution and
yield a guarantee that some run violates. @fig:intro-nest shows the resulting
chain of inclusions at one program point.

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    let ring(color, title, body, inner) = block(
      width: 100%,
      inset: (x: 6pt, top: 3pt, bottom: 3pt),
      radius: 6pt,
      fill: color.lighten(95%),
      stroke: 0.8pt + color,
    )[
      #text(weight: "bold", fill: color, title) #h(0.5em) #text(fill: vb.neutral, body)
      #if inner != none {
        v(1pt)
        inner
      }
    ]
    ring(
      vb.proved,
      [Verdicts],
      [stores in which every definite verdict at $v$ holds (#isaconst("PROVED"),
        #isaconst("REFUTED"), @ch:results)],
      ring(
        vb.accent,
        [Report],
        [stores the states #isaconst("report_states_at") lists at $v$ describe
          (@ch:results)],
        ring(
          vb.cong,
          [Collecting semantics],
          [#isaconst("node_collect"): stores of valid traces ending at $v$, which equals
            $union.big_c$ #isaconst("activation_collect"), the same stores split by context
            $c$ (@ch:traces)],
          ring(
            vb.called,
            [Graph runs],
            [stores that #isaconst("cstep") runs of the compiled graph hold at $v$
              (@ch:program-model)],
            ring(
              vb.neutral,
              [Source executions],
              [stores that #isaconst("pstep") runs reach (@ch:program-model)],
              none,
            ),
          ),
        ),
      ),
    )
  },
  kind: image,
  placement: none,
  caption: [Soundness at a program point $v$ as nested sets. A valid trace
    records, besides the stores of a graph run, which call created each
    activation, and every graph run is represented by one. Splitting the node
    collecting semantics by context loses no store. The source-level
    theorem chains these inclusions for every report the analyzer returns
    (#isathm("run_voblint_source_sound"), @ch:results).],
) <fig:intro-nest>

- _End-to-end soundness._ Whenever the analysis function
  #isaconst("run_voblint") returns a report, its definite verdicts
  (#verdict("PROVED") and #verdict("REFUTED")) hold for every source execution
  from an initial store with zeroed globals that reaches the corresponding
  program point, under every analysis configuration the function offers
  (#isathm("run_voblint_source_sound"), @sec:headline). Companion theorems
  justify #verdict("DEAD") and the absence of arithmetic warnings
  (@ch:results).
- _A concrete semantics of calling contexts._ An activation trace records the
  path of one activation together with the activation that called it, so the
  contexts a policy assigns to a call can be read off the concrete execution.
  A policy may assign one call several contexts. As long as it assigns at
  least one to every call the analysis considers reachable, the stores
  collected per context together are exactly the stores of the node collecting
  semantics, which ignores contexts
  (#isathm("node_collect_eq_Union_activation_collect"), @sec:contract).
- _Separately verified components._ Domains, context policies, analyses, and
  the solver are each verified against their own interface, and generic
  theorems compose them for every configuration. A numeric domain proves only
  its primitive operations sound, and the transfer functions derived from them
  are sound for every such domain (#isathm("nonrel_spec_sound")). A context
  policy proves only that its contexts agree with the concrete semantics and
  that every call from a store the claim contains gets one, analyses that ask one another for facts compose under conditions on their
  answers (@ch:cooperation), and the solver enters the proof only through
  proved facts about its result (@sec:cert-param).
- _Needed assumptions and nonempty results._ For several conditions of the
  proof, a theorem shows that dropping or weakening the condition admits an
  answer that a concrete execution contradicts, such as an analysis result that
  misses a store some run reaches or an abstract remainder that excludes the
  concrete one, so none of them can simply be dropped (@sec:eval-1161). Dropping the requirement that every such call gets a context is one example (#isathm("total_dropped_unsound")). Since a soundness
  theorem would also hold for an analyzer that answers #verdict("UNKNOWN")
  everywhere, further theorems show definite verdicts on concrete programs
  (@sec:nonvacuity) and one context policy strictly more precise than another
  on one program (@sec:eval-precision).

== Scope and limitations <sec:intro-scope>

Voblint is a Goblint-style analyzer with several context policies, over a
small language with parameters, return values, and recursive procedures. It
isolates the parts of Goblint's architecture the proof is about (calling
contexts, side-effecting constraint systems, configurable domains, analyses
that answer one another's queries, and the top-down solver) and is not a
verification of Goblint itself. _End to end_ means from source executions to the result
the analysis function returns. Voblint provides the semantic connections on
both sides of the solver and depends on it only through its post-solution
guarantee and three facts about a returned run, namely that its solved set
is finite, that the run lies in the solver's domain, and that the executable
solver returns the same result (@sec:cert-param). @fig:intro-trust places each
stage of the analyzer relative to the proof.

#figure(
  {
    set text(size: 7.5pt)
    set par(first-line-indent: 0pt, justify: false, leading: 0.45em)
    let zone(color, title, body, dash: none) = block(
      width: 100%,
      inset: 3.5pt,
      radius: 3pt,
      fill: color.lighten(95%),
      stroke: (paint: color, thickness: 0.7pt, dash: dash),
    )[
      #text(size: 6.8pt, weight: "bold", fill: color, title)
      #v(1pt)
      #align(center, body)
    ]
    let box-of(color, body) = box(
      inset: (x: 3pt, y: 2pt),
      radius: 2pt,
      fill: white,
      stroke: 0.6pt + color,
      body,
    )
    let arrow = text(fill: vb.neutral)[#sym.arrow.r]
    let p(body) = box-of(vb.proved, body)
    let u(body) = box-of(vb.unproved, body)
    grid(
      columns: (19%, auto, 1fr, auto, 15%),
      column-gutter: 3pt,
      row-gutter: 3pt,
      align: horizon,
      zone(vb.unproved, [unverified input], dash: "dashed")[
        #u[source text] \ #text(fill: vb.neutral)[#sym.arrow.b] \ #u[lexer, parser]
      ],
      arrow,
      stack(
        dir: ttb,
        spacing: 2pt,
        align(center, box(
          inset: 3pt,
          radius: 3pt,
          stroke: (paint: vb.neutral, thickness: 0.7pt, dash: "dashed"),
        )[Source semantics: elaboration, #isaconst("pstep") and its operators]),
        align(center, text(fill: vb.neutral)[#sym.arrow.b]),
        zone(vb.proved, [proved in Isabelle/HOL])[
          #p[CFG compiler] #arrow #p[equations] #arrow #p[solver] #arrow #p[result, verdicts]
        ],
      ),
      arrow,
      grid.cell(align: bottom, zone(vb.unproved, [unverified output], dash: "dashed")[
        #u[adapter, \ rendering]
      ]),
      grid.cell(colspan: 5, zone(vb.trusted, [trusted foundation])[
        Isabelle kernel · code generator and target mappings · OCaml and WebAssembly
        toolchains · Zarith · browser
      ]),
    )
  },
  placement: none,
  caption: [Where the proof starts and stops, for accepted programs whose solve
    terminates. The adequacy of elaboration and #isaconst("pstep") is argued
    (@sec:vimp-vs-c). The handwritten adapters connect the generated code to
    the command line and the browser, Zarith is OCaml's arbitrary-precision
    integer library, and @sec:trust-boundary gives the exact boundary.],
) <fig:intro-trust>

Voblint builds on prior work. The solver and the soundness proofs of its
update rules come from the Isabelle formalization of Tilscher et al.
@tilscher26, which Voblint uses in a copy with changes made for this thesis
and checks in every build (@sec:upstream-td). The rules come from Stemmler et
al. @stemmler25, side-effecting constraint systems from Seidl et al. @seidl03
and Apinis et al. @apinis12, and the local/global analysis architecture from
Goblint. Widening, narrowing, and the reduced product are well studied
@cousot77 @cousot79. The derivation of transfer functions from sound value
operations follows Nipkow and Klein @nipkow14[Sects. 13.5, 13.7], and the
activation traces adapt the local traces of Schwarz et al. @schwarz21 to
procedure activations. Isabelle's code generator @haftmann10 produces the
OCaml code the tools run.

The theorem has the following limits (@sec:limitations).

- _Language._ VIMP has no pointers, heap, or threads. Its integers have fixed
  widths and wrap, every operation is defined, division by zero included, and
  a local declared without an initializer holds some value of its kind. A
  verdict therefore does not necessarily transfer to a C program with the same
  text (@sec:vimp-vs-c).
- _Properties._ Voblint checks assertions and arithmetic hazards: division and
  remainder by zero, signed overflow, and conversions that may change a value.
  Goblint also checks data races, memory safety, memory leaks, and program
  termination @saan26phd[§3.3].
- _Adequacy._ We argue, but do not prove, that elaboration and the core
  semantics #isaconst("pstep") model the intended language (@sec:vimp-vs-c).
- _Partial correctness._ The theorem covers every answer the analyzer returns.
  Termination of the solve is not proved for every program (@sec:termination).
- _Trusted components._ The parser, the code generator, and the target
  toolchains lie outside the proof (@sec:trust-boundary).
- _Precision._ No completeness or general precision ordering is proved
  (@sec:eval-precision).
- _Goblint._ The correspondence is architectural, and no theorem transfers to
  Goblint's implementation (@sec:rel-goblint).
- _Direction._ Every source run is proved to have a matching graph run, and
  every graph run a representing trace, but not conversely. Soundness needs
  only this direction (@sec:csim).
- _Executable cost._ The executable keeps the proofs' data representations,
  and no time or memory measurement is reported (@sec:limitations).
- _Evidence beyond the theorem._ Each counterexample theorem weakens one
  condition on one program (@sec:eval-1161), and the regression corpus is
  small and was written or adapted for this work (@sec:eval-corpus).

== Outline

After @ch:background, the thesis follows the nested sets of @fig:intro-nest
from the inside out. #partref(<part:over-approx>) fixes what an analysis must
over-approximate: VIMP and its compilation to a control-flow graph
(@ch:program-model), and activation traces indexed by calling context with the
coverage contract analyses must meet (@ch:traces). #partref(<part:analyses>) develops what each analysis
contributes, without contexts or a solver: the abstract domains
(@ch:domains), the interface through which an analysis supplies its transfer
functions (@ch:analysis-interface), and the combination of analyses that query
one another (@ch:cooperation).

#partref(<part:verdicts>) turns any analysis that meets this interface into a
sound result. @ch:equations generates the equations of a program, @ch:solving
computes their solution with the verified solver, and @ch:results composes
these parts into the source-level theorem. #partref(<part:instances>) puts the
theorem to use. @ch:instances instantiates it for five domains and an order
analysis, @ch:executable follows #isaconst("run_voblint") to the delivered
tools and their trust boundary, @ch:evaluation tests the premises and
obligations, the precision, and the unverified code, and @ch:tooling describes
the tooling. #partref(<part:assessment>) compares Voblint with prior work
(@ch:related) and closes with limitations and future work (@ch:conclusion).
