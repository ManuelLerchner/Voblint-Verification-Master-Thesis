#import "../lib/code.typ": (
  fixture, isaconst, isalocale, isathm, isatype, listing, oblig, rebase, site,
)
#import "../lib/figures.typ": check-row, partref, verdict
#import "../lib/sources.typ": proved
#import "../lib/math.typ": *
#import "../lib/theme.typ": metro, vb

#let metro-line(c, body) = text(fill: c, weight: "bold", body)
#import "../lib/claims.typ": claim-ref

= Introduction <ch:intro>

A static analyzer answers questions about every execution of a program at once.
It can answer, for instance, whether a divisor can be zero at some program
point, whether a point is reachable at all, or whether a condition always holds
there. The developers who run the analyzer act on these answers without running
the program, so the answers have to be right. The analyzer, however, is itself a program, and its errors produce
confident answers that real executions contradict. The issue tracker of
Goblint, an analyzer for C programs @vojdani16 @seidl26, lists more than a
hundred #link("https://github.com/goblint/analyzer/issues?q=label%3Aunsound")[issues labeled as unsound]
that have been opened since 2021. In
#link("https://github.com/goblint/analyzer/issues/1156")[issue 1156], for
instance, Goblint claimed that `c % 2 == 1` holds for $c in {-5, -7}$, although
the truncating remainder of C11 @iso-c11[§6.5.5p6] gives $-1$ for both values.
Goblint's congruence domain, which groups integers whose differences are
multiples of a fixed number, had ignored the sign of the dividend, and
#link("https://github.com/goblint/analyzer/pull/1161")[pull request 1161] fixed
it. An error of this kind is worse than imprecision. An imprecise
answer leaves the question undecided, whereas a wrong answer gives a developer
who trusts it no reason to look for the error.

Fixing one such bug does not rule out the next. Ruling out every such bug
requires a proof that the analyzer's answers hold for every execution of every
program. Such a proof is too long to check reliably by reading it. In a proof
assistant such as Isabelle/HOL @nipkow14, definitions and theorems are stated in a formal logic,
and a small trusted kernel checks every inference step of every proof
@paulson19. An error in a proof therefore stops the proof, and the faulty
theorem is never established.

This thesis presents Voblint, short for verified Goblint. Voblint is an
analyzer modeled on Goblint's architecture and formalized in Isabelle/HOL,
together with a machine-checked soundness proof for well-formed VIMP programs
whose analysis terminates. It analyzes VIMP, a small C-like language with integer
variables and recursive procedures. Isabelle's code generator exports the
proved analysis function to OCaml, where a command-line tool runs it. The same
code runs in a #link(site("playground.html"))[browser playground], a web page
that analyzes a program the reader enters. The soundness theorem starts from
_source executions_, the executions described by VIMP's rules for individual
computation steps (#isaconst("pstep")). The analyzer computes on a control-flow
graph (CFG), whose nodes are program points and whose edges are possible steps
between them. Every later representation, from this graph to the solver's
result, is connected to source executions by proof. The kernel,
however, checks proofs only against the definitions it is given. Whether
these rules describe the intended language, their _adequacy_, therefore
lies outside the proof. @sec:vimp-vs-c argues it by comparing VIMP with C11.

== Sound static analysis and its verdicts <sec:intro-static>

Software is usually checked by testing. A failing test shows a bug, but
a passing test suite has observed only finitely many executions
@rival20[§1.4.1]. A static analysis reasons about all
executions instead. At each program point, it computes an _abstract state_, a
finite representation of a set of _stores_. A store maps each program variable
to its current value. For instance, an interval can contain every value a
variable takes whenever execution reaches the point. The analysis is _sound_ if
the abstract state contains every store that occurs in a real run, although it
may contain more. Such a result is an _over-approximation_. If a sound abstract
state contains no store that violates a condition, no execution violates it,
tested or not (@fig:intro-runs). The converse does not hold.
An abstract state can contain violating stores that no execution reaches, and
the analysis then cannot decide the condition, even when every execution satisfies
it.

Suppose the analysis computes $x in [43, +infinity)$ at a point that divides
by `x`. Every execution that reaches this point has $x >= 43$, so the division is
safe. If it computes only $x in [0, 100]$, the abstract state contains $x = 0$,
and the analysis cannot prove the division safe. However, every real execution
may still have
$x >= 43$, for instance, because of a relation to another variable that an
interval cannot express.

#figure(
  image("/shared/generated/svg/runs.svg", width: 100%),
  placement: none,
  caption: [Testing and abstract interpretation, schematically. Each curve is one
    execution, the horizontal axis is time, and the vertical axis the program
    state.
    Left: tests observe only the runs they execute, and a run on an input nobody
    tried (dashed) stays unknown. Right: a sound analysis result (shaded)
    contains every run, tried or not, and may also contain states that no run
    reaches. Because it does not overlap the bad states, no execution can reach
    them.],
) <fig:intro-runs>

For a general-purpose language, this incompleteness is unavoidable. By Rice's
theorem, no algorithm decides a nontrivial semantic property for every program
of a Turing-complete language @rice53 @rival20[§1.3.3]. A sound analysis may
therefore raise false alarms and leave questions undecided, but it never makes a
false claim. It is
useful as long as it decides the questions of interest often enough
@rival20[§1.3.5]. Since every sound analysis over-approximates the same
executions, analyses can specialize. One tracks intervals, another parities, and
another relations between variables. If any one of them, or their combination,
proves a condition, the condition holds in every run that reaches it.
Procedures add a further choice. Each call starts an _activation_, one
invocation of a procedure including any calls it makes @aho06[§7.2.1], and an analysis can
separate activations by their _calling context_, an abstraction of how
the call was reached, such as the call site or the abstract state at entry. It
then keeps one abstract state per program point and context, and it may analyze
one call in several contexts, for instance, one per abstract state that reaches
the call. A richer domain or more contexts
can decide more conditions, but they also make the analysis more expensive. If there
are
many contexts, the analysis may not finish in practice.

A user of Voblint states such a condition by writing a _check_
`__voblint_check(e)` into the program, and Voblint answers each check with a verdict. It also warns
at every division and remainder where it cannot exclude a zero divisor.
@fig:intro-answers shows a run in the playground together with what each answer
guarantees. #verdict("PROVED") and
#verdict("REFUTED") are the _definite_ verdicts, and #verdict("UNKNOWN") claims
nothing. Only #verdict("DEAD") makes a claim about reachability, and
#verdict("REFUTED") is not a verified counterexample. Voblint offers several abstract domains and context policies
(@ch:instances), and the run shown uses intervals and the unit context policy, which gives every
call the same context.

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
      link(rebase(_ans-run.url), image(
        "/shared/generated/playground/" + _ans-run.image,
        width: 100%,
      )),
      table(
        columns: (auto, auto, 1fr),
        align: (right + horizon, left + horizon, left + horizon),
        // Rules between the body rows keep each guarantee with its line.
        stroke: (_, y) => if y > 1 { (top: 0.3pt + vb.muted.lighten(50%)) },
        inset: (x: 3pt, y: 2.5pt),
        table.hline(stroke: 0.5pt),
        [*Line*], [*Answer*], [*Guarantee*],
        table.hline(stroke: 0.4pt),
        // Rows in source order, so the table reads top to bottom like the program.
        ..(
          (
            "check(0 <= p && p <= 100)",
            verdict(_ans-proved.verdict),
            [the condition holds whenever a run reaches it],
          ),
          (
            "check(p > 100)",
            verdict(_ans-refuted.verdict),
            [the condition fails whenever a run reaches it; not a counterexample],
          ),
          ("check(p == 50)", verdict(_ans-unknown.verdict), [nothing]),
          ("check(p == 0)", verdict(_ans-dead.verdict), [no run reaches the check]),
          (
            "1000 / p;",
            tag(vb.verdict-warning, raw(_ans-warn.cond)),
            [a zero divisor could not be excluded; no run is shown to divide by zero],
          ),
          ("1000 / (p + 1)", tag(vb.muted, [none]), [no run reaching this point divides by zero]),
        )
          .map(((needle, answer, text)) => (int(_line(needle)), answer, text))
          .sorted(key: r => r.at(0))
          .map(((line, answer, text)) => ([#line], answer, text))
          .flatten(),
        table.hline(stroke: 0.5pt),
      ),
    )
  },
  kind: image,
  placement: none,
  caption: [One analyzer run on a clamp function, as the browser playground
    shows it, with the interval domain and the unit context policy. The analysis
    covers every value of `t` at once. The screenshot opens the run in the
    playground. The program is the regression test
    #fixture("24-site-figures/precision/48-clamp_every_answer.vimp").],
) <fig:intro-answers>

== Soundness of existing analyzers <sec:state-of-art>

Most abstract interpreters in practical use have no machine-checked soundness
proof and rely on testing instead. Livshits et al. know of no realistic
whole-program analysis tool that does not purposely make unsound choices, and
they observe that virtually all published whole-program analyses are unsound
@livshits15[p. 44]. Most of these analyzers have a sound core that over-approximates
most language features and models all their possible behaviors. It instead
under-approximates a few features that experts in the area know well, such as
reflection in Java, `eval` in JavaScript, or `setjmp`/`longjmp` in C. The
analysis then pretends that some possible behaviors of these features cannot
happen, for instance, that `eval` does nothing, so its result can miss
executions. The authors call such analyses _soundy_. They treat this as an
engineering choice for precision and scalability, and they ask the authors of
such analyses to state explicitly
the nature and extent of the unsoundness @livshits15[p. 45]. Goblint
documents such assumptions. It assumes that pointer arithmetic
does not overflow and, by default, that array reads stay in bounds, and calls this list likely incomplete @goblint-assumptions.

A documented assumption tells the user where a soundness claim ends. Within
that boundary, however, the claim still rests on an implementation that no one
has proved correct. Even the analyzers in practical use that are designed to be
sound are tested rather than proved (@sec:rel-practice), and testing an
analyzer is incomplete in the same way as testing any other program
(@sec:intro-static). Since its first
participation in SV-COMP in 2021, a competition on benchmark programs with
known verdicts, Goblint has never produced a false negative on the
competition's benchmark suite @seidl26, although its unsoundness issues were
opened during the same years.

A proof about single operations, on paper or in a proof assistant, however, protects the
user only if a theorem connects these operations to the tool the user runs. Between the operations and the
reported verdict, the analyzer compiles the program, assigns calling contexts,
and solves equations. Each step must preserve the concrete executions that
the reported verdict is meant to cover.

Goblint defines its analyses independently of the solvers that compute their
results, and Voblint follows this architecture @vojdani16 @seidl26. The
interface between the two is a side-effecting constraint system @seidl03
@apinis12 @seidl26. Such a system relates unknown abstract states by
inequalities, and the inequality of one unknown may also contribute to other
unknowns. Because this architecture is modular, it also suits a proof. The
soundness argument about programs needs only one fact about the solver, namely
that its result satisfies the inequalities. The argument therefore holds for
every solver that guarantees this fact. Side effects let an analysis keep
flow-insensitive information, such as the values of global variables, in one
unknown to which every program point contributes. They also serve calling
contexts. Under some context policies, a callee's contexts become known only
while the system is solved, so each call contributes its entry state to the
callee instead of the callee listing its callers in advance (@sec:side-effects). For the solver itself, a proof already exists. The top-down (TD)
solver algorithm, including an extension to side effects, has been formalized
and proved partially correct in Isabelle/HOL @stade24 @tilscher26. When it
terminates, it returns values that satisfy the inequalities of the queried
local unknown and of every local unknown it transitively reads
(#isaconst("part_post_solution", thy: "Basics_side")). Whether the equation
system describes the program, and whether the verdicts computed from its solution hold, lies outside that theorem.

To establish this connection, every abstract state must be compared with the
concrete stores it describes. Calling contexts make this comparison hardest,
since the per-context abstract states of an analyzer have no counterpart in an
ordinary concrete semantics.
Suppose `main` calls `bump(5)` and `bump(4)`, and `bump` returns its argument
plus one. An analysis whose contexts record the argument at entry claims the
result $6$ in the first context and $5$ in the second. The collecting semantics,
the set of stores that executions reach at each program point, holds both
results at the point where `bump` returns. It forgets how each store
was reached, so it does not say which store belongs to which context, and the
claim for one context cannot be checked against it. To state such claims, the
concrete semantics must be strengthened so that it records the contexts of every
activation (@sec:intro-static).
Voblint's activation traces record each activation together with the activation
that called it, and a context policy reads the contexts off this chain. With
such a semantics, every step from source executions to the verdicts becomes an
inclusion between sets of concrete stores, and a proof can check each of them.

== Contributions <sec:contributions>

The soundness proof of Voblint closes the gaps of @sec:state-of-art with a
chain of inclusions at every program point. The chain leads from source
executions to the verdicts of the _report_ that the analysis function returns
(@fig:intro-nest). Each step may add stores that no execution reaches, which
costs precision, but it must not lose a reachable store. A compiler that drops
an edge or a return to the wrong caller would lose such a store, and the proof
excludes both errors. The Isabelle/HOL formalization and its proof are available at
#link(
  "https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis",
)[`github.com/ManuelLerchner/Voblint-Verification-Master-Thesis`]
and archived on Zenodo @voblint.

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
      [stores in which every definite verdict at $v$ holds (#isaconst("verdict_stores"), @ch:results)],
      ring(
        vb.accent,
        [Report],
        [stores the states #isaconst("report_states_at") lists at $v$ describe,
          which cover the collecting semantics because the solver's result
          satisfies the inequalities of the constraint system (@ch:equations to @ch:results)],
        ring(
          vb.cong,
          [Collecting semantics],
          [#isaconst("node_collect"): stores of valid traces ending at $v$, which
            equals the same stores split by context,
            #box[$union.big_c$ #isaconst("activation_collect")], when every trace
            carries a context
            (#isathm("node_collect_eq_Union_activation_of_has_context"), @ch:traces)],
          ring(
            vb.called,
            [Graph executions],
            [stores that #isaconst("cstep") executions of the compiled graph hold at $v$
              (@ch:program-model)],
            ring(
              vb.neutral,
              [Source executions],
              [stores that #isaconst("pstep") executions reach (@ch:program-model)],
              none,
            ),
          ),
        ),
      ),
    )
  },
  kind: image,
  placement: none,
  caption: [Soundness at a program point $v$ as nested sets. An activation trace
    records, besides the stores of a graph execution, which call created each
    activation, and every graph execution is represented by one. Splitting the node
    collecting semantics by context loses no store. The end-to-end soundness
    theorem chains these inclusions for every report the analyzer returns
    (#isathm("run_voblint_source_sound"), @ch:results).],
) <fig:intro-nest>

The chain combines existing ideas, some of them already formalized and others
so far only described on paper or implemented. Voblint follows Goblint's
architecture, and it formalizes neither Goblint's implementation nor C
(@sec:rel-goblint). To the author's knowledge, no prior mechanized analyzer
connects the semantics of source programs, through an activation collecting semantics indexed
by context, to a side-effecting constraint system and its verified solver
(@sec:rel-summary). The formalization makes five contributions.

- _End-to-end soundness._ The theorem connects the obligations of single
  operations to the tool the user runs. Whenever the analysis function
  #isaconst("run_voblint") returns a report, its definite verdicts
  (#verdict("PROVED") and #verdict("REFUTED")) hold for every source execution
  from an initial store with zeroed globals that reaches the corresponding
  program point, under every analysis configuration the function offers
  (#isathm("run_voblint_source_sound"), @sec:headline). Companion theorems
  justify #verdict("DEAD") and the absence of arithmetic warnings
  (@ch:results).
- _A concrete semantics of calling contexts._ Activation traces give the
  per-context states of an analysis a concrete counterpart, because the chain of
  calling activations determines the contexts of a call. Splitting the concrete
  stores by context loses no execution (@sec:contract), and every report covers
  each context separately (#isathm("run_voblint_context_covers")). One call may
  have several contexts, which lets an analysis split it into cases.
- _Separately verified components._ Each component discharges local soundness
  obligations, and generic theorems compose them into the end-to-end guarantee
  for every configuration. Domains prove their primitive operations sound,
  context policies prove that their contexts agree with the concrete
  semantics, cooperating analyses prove conditions on the answers they
  exchange (@ch:cooperation), and the solver enters the proof only through
  proved facts about its result (@sec:certificate).
- _An executable analyzer._ The command-line tool and the playground run code
  generated @haftmann10 from #isaconst("run_voblint"), the same constant the
  soundness theorem is about. The playground also draws the control-flow graph
  and replays the solver's steps.
- _Needed assumptions and nonempty results._ The kernel cannot tell whether a
  theorem assumes too much or concludes too little. Further theorems therefore
  show that the analyzer gives definite verdicts on concrete programs
  (@sec:nonvacuity). The obligation #oblig("TOTAL") requires
  that every call gets at least one calling context. Dropping it admits answers
  that concrete executions contradict (@sec:contract), and one
  domain obligation rejects a defect that occurred in Goblint
  (@sec:eval-1161). Concrete programs show what each mechanism gains
  (@sec:eval-precision).

== Scope of the soundness theorem <sec:intro-scope>

_End-to-end_ means that the proof reaches from source executions under
#isaconst("pstep") to the result of the analysis function (@fig:intro-trust).
The list after the figure collects the limits of the theorem.

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
        )[Source semantics: #isaconst("pstep") and its operators]),
        align(center, text(fill: vb.neutral)[#sym.arrow.b]),
        zone(vb.proved, [proved in Isabelle/HOL])[
          #p[CFG compiler] #arrow #p[equations] #arrow #p[solver] #arrow #p[result, verdicts]
        ],
      ),
      arrow,
      grid.cell(align: bottom, zone(vb.unproved, [unverified output], dash: "dashed")[
        #u[handwritten OCaml, \ state printing]
      ]),
      grid.cell(colspan: 5, zone(vb.trusted, [trusted foundation])[
        Isabelle kernel · code generator and target mappings · OCaml and WebAssembly
        toolchains · Zarith · browser
      ]),
    )
  },
  placement: none,
  caption: [Where the proof starts and stops, for well-formed programs whose solve
    terminates. The adequacy of #isaconst("pstep") is
    argued (@sec:vimp-vs-c).],
) <fig:intro-trust>


- _Language and properties._ VIMP has no pointers, heap, or threads. Its
  integers are unbounded, division by zero is defined, and a callee's locals
  start at 0. Therefore, a verdict
  does not always hold for a C program with the same text (@sec:vimp-vs-c).
  Voblint covers checks (`__voblint_check`) and division by zero, while Goblint also checks
  overflows, data races, memory
  safety, memory leaks, and program termination @saan26phd[§3.3].
- _Adequacy and trusted components._ The adequacy of #isaconst("pstep") is
  argued in @sec:vimp-vs-c. The parser, the handwritten OCaml for printing, the
  code generator, and the target toolchains lie outside the proof
  (@fig:intro-trust).
- _Partial correctness._ The theorem covers every report the analyzer returns.
  Termination of the solve is not proved for every program (@sec:certificate).
- _Precision and cost._ No completeness or general precision ordering is
  proved (@sec:eval-precision). The executable uses the same data
  representations as the proofs and was not optimized beyond one fixed
  performance defect (@sec:codegen). Running time is measured only to show
  that the analyzer finishes in acceptable time on the regression corpus
  (@sec:eval-runtime).
- _Goblint and evidence._ The correspondence to Goblint is architectural, and
  no theorem transfers to Goblint's implementation (@sec:rel-goblint). The
  regression corpus is small and was written or adapted for this work
  (@sec:eval-corpus).

== Structure of the proof <sec:roadmap>

@fig:intro-nest states what the end-to-end soundness theorem claims, and
@fig:metro draws how its proof is assembled. Each line of the map is one layer
of the development, such as the compiler and its simulation proof, and where
lines meet, a theorem combines their results. The compiler line places every
source execution at a node of the graph. The framework line shows that the
stores reaching a node in a context lie in the analyzer's state for that node
and context, once for policies that choose contexts without reading abstract
states and once for entry-state policies. The solver line contributes that a
returned solve is a post-solution, meaning that its values satisfy the system's
inequalities. Together, these results establish the
verdict guarantees of @sec:intro-static
(#isathm("run_voblint_source_sound"), @ch:results).

#figure(
  image("/shared/generated/svg/metro.svg", width: 100%),
  placement: none,
  caption: [A map of the proof with its interior definitions omitted. The
    #link(
      site("index.html#proof-map"),
    )[project site]
    shows it interactively, with every station linked to its theory. Each line
    groups the results of one layer: #metro-line(metro.sem)[Semantics], the
    source and trace semantics (@ch:program-model and @ch:traces), #metro-line(metro.comp)[Compiler], the compiler and its
    simulation (@ch:program-model),
    #metro-line(metro.dom)[Domain], what a domain proves and how the analyses
    cooperate (@ch:domains to @ch:cooperation and the
    order analysis of @ch:instances), #metro-line(metro.fw)[Framework], the
    analysis contract, routing and coverage (@ch:traces, @ch:analysis-interface
    and @ch:equations), #metro-line(metro.sol)[Solver], the verified TD solver
    (@ch:solving), and #metro-line(metro.res)[Result],
    from the solved equations to the verdicts (@ch:equations and @ch:results).],
) <fig:metro>

The proof map selects the results that connect the semantic layers.
@fig:intro-corpus shows the surrounding formal development as a treemap of
exported Isabelle entities. It groups the declarations by session and theory,
including facts generated by Isabelle's definition packages. The area of a
block therefore measures its share of the exported corpus, not the difficulty
of its proofs. The interactive view links each declaration to its documentation.

#figure(
  link(site("proof-map.html?view=treemap"), image("/assets/proof-map-treemap.png", width: 90%)),
  placement: none,
  caption: [The formalization's exported declarations, captured from the
    #link(site("proof-map.html?view=treemap"))[interactive treemap].
    Blocks group sessions and theories; their areas follow entity counts.
    Colors identify session dependency layers. Gold diamonds mark thesis
    citations, and red stars mark selected source-level soundness results.
    This is a corpus overview; it does not depict proof dependencies.],
) <fig:intro-corpus>

The thesis is organized along the soundness chain, from source executions to
the reported verdicts. #partref(<part:problem>) introduces the problem and
recalls abstract interpretation, constraint systems, and the verified TD
solver, on which the chain relies (@ch:background).

#partref(<part:over-approx>) fixes the concrete side of the chain. It defines
source programs and their graphs (@ch:program-model), then activation traces
and the coverage contract (@ch:traces). The next two parts establish this
contract. #partref(<part:analyses>) states what domains (@ch:domains),
analyses (@ch:analysis-interface), and their cooperation (@ch:cooperation)
must prove. #partref(<part:verdicts>) combines these obligations. It builds
the equations (@ch:equations), solves them (@ch:solving), and derives sound
source-level verdicts (@ch:results).

#partref(<part:instances>) turns the framework into a working analyzer. It
presents the analysis instances (@ch:instances), the executable and its trust
boundary (@ch:executable), and the evaluation (@ch:evaluation).

#partref(<part:assessment>) discusses related work (@ch:related) and concludes
(@ch:conclusion). @sec:isabelle explains the Isabelle listings, @app:notation
collects the notation, and @sec:voblint-repo describes the repository and tooling.
