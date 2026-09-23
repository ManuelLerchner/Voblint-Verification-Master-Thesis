#import "../lib/code.typ": fixture, isaconst, isathm, listing, oblig
#import "../lib/figures.typ": check-row
#import "../lib/sources.typ": proved
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb

= Introduction <ch:intro>

A static analyzer answers questions about every execution of a program at once:
whether a divisor can be zero at some point, or whether a check always holds,
and its users act on these answers without running the program. The analyzer
is itself a program, and an error in a transfer operation, in the
treatment of a call, or in the reading of the computed state produces a
confident answer that real executions contradict. Goblint #link("https://github.com/goblint/analyzer/issues/1156")[issue 1156] reports
that Goblint claimed `c % 2 == 1` for $c in {-5, -7}$ @goblint1156, although
the truncating remainder of C11 @iso-c11[§6.5.5p6] gives $-1$. #link("https://github.com/goblint/analyzer/pull/1161")[Pull request
  1161] fixed the congruence domain, which had ignored the sign of the dividend
@goblint1161.
@ch:evaluation replays the case.
This thesis asks under which assumptions the answers produced by an executable analyzer are sound for every execution of the analyzed program.

Formal verification states such a claim as a proposition over explicit
definitions, and a proof assistant checks its proof @nipkow14. Isabelle/HOL
follows the LCF approach: every theorem is constructed through a small trusted
inference kernel @paulson19. Because the kernel checks each step, a proof
found by an automated tool or an AI system passes the same check as one
written by an expert, which has made proof assistants a target for AI. AlphaProof, for example, solved three problems of
the 2024 International Mathematical Olympiad in Lean, on problem statements
that experts had formalized by hand @hubert25alphaproof. For Isabelle,
#cite(<kappelmann26>, form: "prose") study agents that draft and generalize
formalizations from human hints, and
#cite(<bryant26munkres>, form: "prose") report LLM coding agents that
produced over 85,000 lines of Isabelle/HOL covering Munkres' general topology,
with all 806 results proved. This thesis was developed with AI assistance as
well (see #link(<ai-use>)[Use of Generative AI]), and the same argument
applies to it.

A checked proof settles that the formal statement follows from the
definitions. It does not settle whether the definitions model the intended
objects or whether the statement expresses the intended claim. A manual review of the Munkres
formalization found definitions logically weaker than the textbook's, harmless
for the proved theorems only because each theorem assumes the missing
constraints again @bryant26munkres[§8.1]. OpenAI's proposed Lean proof of
finite-time blowup for the three-dimensional Navier–Stokes equations (September
2026, review self-assessed) states alternative (C) of the Clay problem
@openai26ns @openai26nspaper @openai26nslean. Whether that statement matches
the intended problem is a question the kernel cannot answer. Software verification makes this
boundary explicit. The seL4 proof relates the kernel's C implementation to an
abstract specification in Isabelle/HOL and names as assumptions the compiler,
assembly code, boot code, cache management and hardware @klein09.

These distinctions fix the division of labor in this thesis. Isabelle
establishes that Voblint's theorems hold. The thesis explains what they state,
why that is the statement one wants about an analyzer, and why the definitions
take their form. The main theorem starts from executions of the source
language, so graph and trace semantics are connected to it by proof. The
source semantics is VIMP's own small-step semantics. Its adequacy is argued
(@sec:vimp-vs-c): which fragment of C it models, where it departs from C11,
and why no existing verified semantics such as IMP2 @lammich19imp2 serves as
the anchor.

== From executions to static guarantees

Testing observes only finitely many executions of a program @rival20[§1.4.1]. A
static analysis instead computes a description of possible behavior, for instance an interval that contains every
value a variable takes whenever execution reaches a program point. The
description may include values that never occur, but soundness requires it to
include those that do. This asymmetry decides what an
analysis can prove. Every execution lies inside the description, so if the
description contains no state that violates a check, no execution violates it,
including executions that no test ever tried
(@fig:intro-runs). The converse does not hold. The
description can contain violating states that no execution reaches, because
abstraction adds states. The analysis then cannot decide the check, even when
every execution satisfies it.

Suppose, for instance, that the analysis computes $x in [43, infinity)$ at a program point. Every execution that reaches the
point then has $x >= 43$ there, so `x > 0` holds and division by `x` is safe whenever execution reaches that point. If the analysis knows only $x in [0, 100]$, the description
contains $x = 0$, so it can prove neither claim, although every real execution
may still have $x >= 43$, for reasons an interval cannot express, such as a
relation to another variable.

#figure(
  image("/shared/generated/svg/runs.svg", width: 100%),
  placement: auto,
  caption: [Testing and static analysis, schematically. Each curve is one
    execution, and the vertical axis stands for the program state over time.
    Left: tests observe only the runs they execute, and a run on an input nobody
    tried (dashed) stays unknown. Right: a sound analysis result (shaded)
    contains every run, tried or not, and may also contain states that no run
    reaches. Because it does not overlap the bad states, no execution can reach
    them.],
) <fig:intro-runs>


This incompleteness cannot be avoided. By Rice's theorem, no algorithm decides
a nontrivial semantic property for every program of a Turing-complete language
@rice53 @rival20[§1.3.3]. A sound over-approximating analysis therefore permits false alarms or undecided checks, but not false proofs. It remains useful as long as it
decides the checks of interest often enough @rival20[§1.3.5], which may need only
coarse information such as the bound on $x$ above.

Voblint answers per check and per arithmetic operation (@fig:intro-answers).
A check is `PROVED` when its condition holds whenever a run reaches it, and
`REFUTED` when the condition fails whenever a run reaches it. Neither asserts
that a run reaches the check (@sec:verdicts shows a `PROVED` check that no run
reaches), and `REFUTED` is not a verified counterexample.
A check is `DEAD` when no run reaches it, and `UNKNOWN` claims nothing. An arithmetic
operation gets a `WARNING` when a zero divisor cannot be excluded, and without
one, no execution reaching it divides by zero.

#let _ans-warn = check-row("intro-answers", cond: "WARNING")
#let _ans-proved = check-row("intro-answers", cond: "0 <= p && p <= 100")
#let _ans-refuted = check-row("intro-answers", cond: "p > 100")
#let _ans-unknown = check-row("intro-answers", cond: "p == 50")
#let _ans-dead = check-row("intro-answers", cond: "p == 0")
// The playground's verdict colours (pages/style.css), so the table matches the
// screenshot beside it.
#let _pg = (
  proved: rgb("#28734b"),
  refuted: rgb("#ad422c"),
  unknown: rgb("#a76924"),
  warning: rgb("#8a4fbf"),
)
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
    set text(size: 8.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let tag(color, body) = box(
      inset: (x: 3pt, y: 2pt),
      radius: 2pt,
      stroke: 0.6pt + color,
      fill: color.lighten(90%),
      text(size: 7.5pt, weight: "bold", fill: color, body),
    )
    grid(
      columns: (52%, 1fr),
      column-gutter: 8pt,
      align: horizon,
      link(_ans-run.url, image("/shared/generated/playground/" + _ans-run.image, width: 100%)),
      table(
        columns: (auto, auto, 1fr),
        align: (right + horizon, left + horizon, left + horizon),
        stroke: none,
        inset: (x: 3pt, y: 3.5pt),
        table.hline(stroke: 0.5pt),
        [*Line*], [*Answer*], [*What it guarantees*],
        table.hline(stroke: 0.4pt),
        [#_line("check(0 <= p && p <= 100)")], tag(_pg.proved, raw(_ans-proved.verdict)),
        [the condition holds whenever a run reaches it
          (#isathm("run_voblint_check_sound"))],
        [#_line("check(p > 100)")], tag(_pg.refuted, raw(_ans-refuted.verdict)),
        [the condition fails whenever a run reaches it; not a counterexample],
        [#_line("check(p == 50)")], tag(_pg.unknown, raw(_ans-unknown.verdict)), [nothing],
        [#_line("check(p == 0)")], tag(vb.neutral, raw(_ans-dead.verdict)),
        [no run reaches the check (#isathm("run_voblint_dead_check_unreached"))],
        [#_line("1000 / p;")], tag(_pg.warning, raw(_ans-warn.cond)),
        [a zero divisor could not be excluded; no run is shown to divide by zero],
        [#_line("1000 / (p + 1)")], tag(vb.muted, [none]),
        [no run reaching it divides by zero (#isathm("run_voblint_arithmetic_safe"))],
        table.hline(stroke: 0.5pt),
      ),
    )
  },
  kind: image,
  placement: auto,
  caption: [One analyzer run on a clamp function, as the browser playground
    shows it (Interval, no contexts; claim `intro-answers`, fixture
    #fixture("24-site-figures/precision/48-clamp_every_answer.vimp")). A unit
    test of `clamp` would try a few inputs; the analysis covers every value of
    `t` at once. Each guarantee assumes that the solve terminates, which this
    run did. The screenshot opens the run in the playground, as does the
    #box[`VIMP ↗`] tag on every later VIMP listing.],
) <fig:intro-answers>

A soundness proof must connect objects of different kinds. The analyzer
compiles the program to a control-flow graph, solves equations over abstract
states and reports a verdict per check, and each change of representation could
lose concrete behavior. The argument therefore follows one store that an
execution reaches through every representation (@fig:intro-nest). The compiler
simulation places it at a graph node $v$, the reached graph state is covered by a valid activation-local trace, and under the totality condition that trace falls
into a context bucket whose solved value admits the store. A `PROVED` check at
$v$ holds for every admitted store. The renderer pairs report rows with source
lines outside the proof (@sec:trust-boundary).
// TODO(check-labels): once checks carry parser-assigned labels, state that the
// report row is identified by its label and drop the renderer caveat.
Precision may be lost at every inclusion, but a store reached by an execution
must not be lost.

#figure(
  {
    set text(size: 9pt)
    set par(first-line-indent: 0pt, justify: false)
    let ring(color, title, body, inner) = block(
      width: 100%,
      inset: (x: 8pt, top: 6pt, bottom: 8pt),
      radius: 6pt,
      fill: color.lighten(95%),
      stroke: 0.8pt + color,
    )[
      #text(weight: "bold", fill: color, title) #h(0.5em) #text(fill: vb.neutral, body)
      #if inner != none {
        v(2pt)
        inner
      }
    ]
    ring(
      vb.proved,
      [`PROVED` check],
      [#isaconst("checks_sound_at"): stores satisfying the condition of a `PROVED`
        check at $v$ (@ch:results)],
      ring(
        vb.accent,
        [Abstract result],
        [#isaconst("analysis_result_covers"): stores the solved values admit at $v$
          (@ch:results)],
        ring(
          vb.cong,
          [Context buckets],
          [#isaconst("activation_collect"): stores of valid traces at $v$, per context
            (@ch:traces)],
          ring(
            vb.locale,
            [Trace collection],
            [#isaconst("ltr_collect"): stores of valid traces ending at $v$ (@ch:traces)],
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
      ),
    )
  },
  kind: image,
  placement: auto,
  caption: [Soundness at a program point $v$ as nested sets. Each inclusion is
    proved under the premises of the main theorem (@ch:results).],
) <fig:intro-nest>

== The verified solver and the research questions <sec:rqs>

Goblint is an abstract interpreter for multithreaded C programs @vojdani16
@seidl21. It defines analyses independently of the generic solvers that compute
their results, and the interface between the two is a side-effecting constraint
system @apinis12 @seidl26. A side effect lets the right-hand side of one
unknown contribute to others, for example a call site to the entry state of
its callee (@sec:side-effects). An Isabelle/HOL formalization of Goblint's top-down
solver has been verified, including its extension to side effects @stade24
@tilscher26. When it terminates, the verified solver returns a correct
post-solution of the equation system it receives (@sec:td). Whether that system describes
the program, and whether the verdicts read off its solution hold, is outside
the solver's theorem. Its example analyses supply equations, written by hand or generated
from a program, and no proof relates them to the program's executions. Context sensitivity adds a second difficulty. The
analyzer keeps a separate abstract state per calling context, while the
ordinary concrete semantics has no notion of context. This thesis addresses
four research questions about that gap.

/ RQ1: Can the soundness of a configurable, context-sensitive interprocedural
  analyzer be machine-checked from source executions to its reported verdicts,
  and what remains trusted?
/ RQ2: What concrete set of executions does a calling context denote, so that
  per-context results are sound and together lose no execution?
/ RQ3: Can domain, context policy and solver each be verified on its own, with
  one theorem composing them for every configuration?
/ RQ4: Is the resulting theorem informative: are its key obligations necessary,
  and can non-vacuity and precision differences be proved on concrete programs?

RQ1 is the main question. RQ2 and RQ3 ask what its answer requires, and RQ4
asks how strong that answer is.
Voblint answers them for a Goblint-style analyzer of a small language with
parameters, return values and several context policies. It is not a verification of Goblint itself. It isolates the parts of Goblint's architecture that the proof is about (recursive procedures, calling contexts, side-effecting constraint systems, configurable domains and the top-down solver) in a language small enough to mechanize every semantic connection. The thesis shows that such an analyzer can be connected by
machine-checked proofs from a source semantics, through context-sensitive
equations and a verified solver, to the verdicts of its executable analysis
function. Here, _end to end_ means from source executions to the result the analysis function returns. Voblint provides the semantic connections on both sides of the solver and depends on it only through its post-solution guarantee (@ch:solving). @fig:intro-trust places each stage of the analyzer relative to the proof.

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
      zone(vb.unproved, [unverified output], dash: "dashed")[#u[adapter, \ rendering]],
      grid.cell(colspan: 5, zone(vb.trusted, [trusted foundation])[
        Isabelle kernel · code generator and target mappings · OCaml and WebAssembly
        toolchains · Zarith · browser
      ]),
    )
  },
  placement: auto,
  caption: [Where the proof starts and stops, for accepted programs whose solve
    terminates. The adequacy of #isaconst("pstep") is argued (@sec:vimp-vs-c),
    and @sec:trust-boundary gives the exact boundary.],
) <fig:intro-trust>

== State of the art <sec:state-of-art>

CompCert is the precedent for a theorem about a delivered tool: it proves in
Coq that its compiled code behaves as the source semantics specifies and lists
the components that remain trusted @leroy09. Verasco
builds a verified abstract interpreter for most of C99 on it, excluding
recursion and dynamic allocation @jourdan15, and the value analysis of
#cite(<blazy13>, form: "prose") checks the output of an unverified fixpoint
iterator instead of verifying it. In Isabelle/HOL, seL4 verifies the C
implementation of an operating-system kernel @klein09, and code generated from a
proof has replaced the SSA construction of the CompCertSSA compiler
@buchwald16.

Nipkow and Klein develop abstract interpretation in Isabelle/HOL over annotated
commands of the While language IMP, intraprocedurally @nipkow12 @nipkow14, and
#cite(<cachera05>, form: "prose") extract a context-insensitive,
constraint-based analyser for Java Card bytecode from a Coq proof. Isabelle
formalizations of interprocedural conflict analysis and slicing have no context
abstraction @lammich07afp @wasserrab09afp. Verified
solvers, RLD in Coq @hofmann10 and Goblint's top-down solver with side effects
in Isabelle/HOL @stade24 @tilscher26, prove the results of a terminating solve
correct for the equation system they receive, independently of what the
equations describe. On Goblint's side,
side-effecting constraint systems separate analyses from solvers @apinis12
@seidl26, and local traces give each thread a concrete semantics from which
thread-modular analyses are derived, on paper @schwarz21 @schwarz23. Concrete
semantics that carry contexts exist in Coq, with the context of a callee
computed by a function @dabrowski09, and trace partitioning indexes sets of
traces by control history, overlapping indices included @rival07.

The analyzers above build their iteration into the analysis or check its result, and the verified solvers stop at the equations they receive. To our knowledge, no prior mechanized analyzer is proved sound across the interface to a generic, verified solver. Nor, to our knowledge, does any prior mechanized analyzer connect a side-effecting, mixed flow-sensitive constraint system to a source semantics. In Voblint, every call publishes its callee's entry state as a side effect to a flow-insensitive unknown (@sec:eq-seed), and the end-to-end theorem covers this for every program. The contributions below fill this gap: the
end-to-end theorem (K1) needs a mechanized concrete meaning for contexts
admitted by a relation (K2), a composition of separately verified domain,
context policy and solver (K3). K4 adds counterexample theorems showing that
several obligations cannot be weakened and that the results are non-vacuous. @ch:related gives the detailed
comparisons.

== Contributions <sec:contributions>

The contribution is the Isabelle/HOL formalization of Voblint and its
machine-checked soundness proof. This document explains the definitions and
proof ideas, and the linked theories contain the complete proofs. We claim one
contribution per research question.

/ K1 (RQ1): _End-to-end soundness of the exported analysis function._ For every
  configuration of #isaconst("run_voblint") and every accepted program: if the
  solve terminates and returns a result, every store a finite source execution
  reaches is covered at a graph node that simulates the source configuration,
  and every definite verdict at that node holds for it
  (#isathm("run_voblint_certified_source_sound"), @sec:headline). Companion
  theorems justify `DEAD` (#isathm("run_voblint_dead_check_unreached")) and the
  absence of zero divisors where no arithmetic diagnostic is reported
  (#isathm("run_voblint_arithmetic_safe")). The command-line tool and the
  browser #link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html")[playground]
  run this function's generated code. Parsing, code generation, compilation and
  presentation are trusted (@sec:trust-boundary). The solver and its partial
  correctness are inherited @tilscher26. To our knowledge, no prior mechanized
  abstract interpreter proves an exported analysis function sound for a
  language with recursive procedures under configurable context sensitivity.
  The closest one, Verasco, reanalyzes a function at every call site up to a
  fuel bound and raises an alarm on possible recursion @jourdan15.

/ K2 (RQ2): _A concrete semantics of calling contexts._ A context policy is a
  relation that reads contexts off activation-local traces
  (#isaconst("valid_ltr"), #isaconst("trace_context"), @sec:contexts), so one
  call may be admitted at several contexts, as Goblint's `enter` requires.
  Under the totality condition #isaconst("call_context_total_on"), the context
  buckets jointly recover the context-free collection
  (#isathm("ltr_collect_eq_Union_activation_collect")). Schwarz et al. define
  local traces for threads without mechanizing them @schwarz21, and Dabrowski
  and Pichardie mechanize context-instrumented semantics with contexts computed
  by a function @dabrowski09. Relational admission, totality and bucket
  recovery are new. To our knowledge, no prior work mechanizes a local-trace
  semantics.

/ K3 (RQ3): _Compositional soundness._ A domain proves transfer soundness
  without contexts or solver, a context policy proves its obligations without a
  domain, and the solver enters only through its certificate
  #isaconst("part_post_solution"). One theorem composes them for all policies
  and domains (#isathm("activation_collect_dg_sound"), @sec:eq-discharge), so
  K1 covers all five domains, three context modes and four update rules. A
  relational carrier meets the same contract without framework changes
  (#isaconst("rel_order_spec"), @sec:relational). Consuming a solver through
  its fixpoint guarantee follows CompCert @compcertKildall. Our addition is its
  use for side-effecting, context-indexed equation systems.

/ K4 (RQ4): _Necessity and non-vacuity as theorems._ Counterexample theorems
  show that several obligations are necessary. Reading the callee's result in
  the caller's context declares a reachable call unreachable
  (#isathm("return_at_caller_context_unsound")), dropping #oblig("TOTAL")
  leaves a reached store uncovered (#isathm("total_dropped_unsound")),
  unpaired entry coverage loses a return value
  (#isathm("unpaired_entry_cover_unsound")), and Goblint's congruence remainder
  before #link("https://github.com/goblint/analyzer/pull/1161")[pull request 1161]
  violates the domain obligation (#isathm("prefix_congruence_mod_unsound")).
  Evaluation inside Isabelle, trusting the code generator, discharges the
  termination premise for named programs, and the main theorem certifies their
  `PROVED` verdicts (#isathm("certificate_demo_full_certificate"),
  #isathm("nv_source_certified")). On one program, call strings of length 2
  are strictly more precise than length 1
  (#isathm("sign_k2_strictly_more_precise_than_k1_at_g")). Prior
  mechanizations prove general completeness or optimality results for
  particular analyses @lammich07afp @tilscher26. To our knowledge, none proves
  strict precision separations between configurations of one analyzer.

The main theorem states partial correctness. Solver termination is a
per-program premise, which evaluation discharges for given programs
(@sec:termination).

We do not claim the top-down solver and its update rules @tilscher26
@stemmler25, side-effecting constraint systems @apinis12, local traces
@schwarz21, Goblint's local/global architecture, widening, narrowing or the
reduced product @cousot77 @cousot79. The command-line tool, the playground and
the regression suite are engineering work. The novelty statements rest on a
web and OpenAlex search with full-text reads of the closest papers, not on a
systematic literature review. @ch:related gives the comparisons.

== Scope and outline

Voblint analyzes VIMP, a scalar imperative language with recursive
procedures. The thesis claims no verified C frontend, heap analysis,
completeness, universal solver termination, general precision ordering
between configurations, or correctness of Goblint's implementation. VIMP
integers are unbounded, and VIMP defines operations that C11 leaves undefined
@iso-c11[§6.5.5p5]: division by zero yields zero and remainder by zero the
dividend. A `PROVED` verdict may depend on these conventions. Only the absence
of an arithmetic diagnostic at a node excludes a zero divisor there
(@sec:verdicts). A verdict about a VIMP program therefore does not transfer to
a C program with the same text (@sec:vimp-vs-c).

@ch:background introduces the order-theoretic and Isabelle background. Part II
fixes what an analysis must over-approximate. @ch:program-model defines source
execution and compilation and proves the simulation on which the source end of
RQ1 rests. @ch:traces answers RQ2 with activation-local traces, the context
relation and the coverage contract, and proves the first necessity
counterexample of RQ4. Part III builds the analyzer from ingredients that
discharge their obligations separately (RQ3): abstract domains
(@ch:domains), the analysis interface (@ch:analysis-interface), the equations,
whose routing also links computed contexts to admitted ones (@ch:equations),
and the solver (@ch:solving). @ch:results composes the chain into the
source-level theorem of RQ1 and fixes the meaning of each verdict. Part IV
instantiates the contract for five domains and a relational witness
(@ch:instances) and follows #isaconst("run_voblint") to the delivered tools,
where the trust boundary of RQ1 lies (@ch:executable). @ch:evaluation assesses
the evidence for each question, including the counterexample, non-vacuity and
precision witnesses of RQ4, and @sec:revealed collects the design constraints
the mechanization exposed. @ch:related compares each contribution with prior
work, and @ch:conclusion answers the four questions.
