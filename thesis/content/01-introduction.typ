#import "../lib/code.typ": fixture, isaconst, isalocale, isathm, isatype, listing, oblig
#import "../lib/figures.typ": check-row, partref
#import "../lib/sources.typ": proved
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb

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
@goblint1161, and @ch:evaluation replays the case.
This thesis asks under which assumptions the answers produced by an executable analyzer are sound for every execution of the analyzed program.

Formal verification states such a claim as a proposition over explicit
definitions, and a proof assistant checks its proof @nipkow14. Isabelle/HOL
follows the LCF approach: every theorem is constructed through a small trusted
inference kernel @paulson19. Because the kernel checks each step, a proof
found by an automated tool or an AI system passes the same check as one
written by an expert. Proof assistants have therefore become a target for AI
systems. AlphaProof, for example, solved three problems of
the 2024 International Mathematical Olympiad in Lean, on problem statements
that experts had formalized by hand @hubert25alphaproof. For Isabelle,
#cite(<kappelmann26>, form: "prose") study agents that draft and generalize
formalizations from human hints, and
#cite(<bryant26munkres>, form: "prose") report LLM coding agents that
produced over 85,000 lines of Isabelle/HOL covering Munkres' general topology,
with all 806 results proved. This thesis was developed with AI assistance as
well (see #link(<ai-use>)[Use of Generative AI]), and the same argument
applies to it.

The kernel checks that the formal statement follows from the definitions.
Whether the definitions model the intended objects, and whether the statement
expresses the intended claim, remains for human review. A manual review of parts of the
Munkres formalization found definitions logically weaker than the textbook's.
The authors judge them harmless for the proved theorems, because each theorem
assumes the missing constraints again @bryant26munkres[§8.1]. OpenAI's proposed Lean proof of
finite-time blowup for the three-dimensional Navier–Stokes equations (September
2026, with a self-assessed review) states alternatives (C) and (D) of the Clay problem
@openai26ns @openai26nspaper @openai26nslean. Whether that statement matches
the intended problem is a question the kernel cannot answer. The seL4 proof makes this boundary
explicit. It relates the kernel's C implementation to an
abstract specification in Isabelle/HOL and names as assumptions the compiler,
assembly code, boot code, cache management and hardware @klein09.

For Voblint, Isabelle checks that the theorems hold, and this thesis explains what they state,
why that is the statement one wants about an analyzer, and why the definitions
take their form. The main theorem starts from executions of the source
language, so graph and trace semantics are connected to it by proof. The
source semantics is VIMP's own small-step semantics #isaconst("pstep"). Its adequacy is argued
(@sec:vimp-vs-c): which fragment of C it models, where it departs from C11,
and why no existing verified semantics such as IMP2 @lammich19imp2 serves as
the anchor.

== From executions to static guarantees

Testing observes only finitely many executions of a program @rival20[§1.4.1]. A
static analysis instead computes a description of possible behavior, for instance an interval that contains every
value a variable takes whenever execution reaches a program point. Soundness
requires the description to contain every value that occurs, and it may
contain more. This asymmetry decides what an
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

Voblint gives an answer per check and a warning per program point where it
cannot exclude a zero divisor. @fig:intro-answers lists what each answer
guarantees. Only `DEAD` makes a claim about reachability: @sec:verdicts shows a
`PROVED` check that no run reaches, and `REFUTED` is not a verified
counterexample.

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
        [no run reaching this point divides by zero (#isathm("run_voblint_arithmetic_safe"))],
        table.hline(stroke: 0.5pt),
      ),
    )
  },
  kind: image,
  placement: auto,
  caption: [One analyzer run on a clamp function, as the browser playground
    shows it (Interval, `warrow` globals, no contexts; claim `intro-answers`, fixture
    #fixture("24-site-figures/precision/48-clamp_every_answer.vimp")). A unit
    test of `clamp` would try a few inputs. The analysis covers every value of
    `t` at once. Each guarantee assumes that the solve terminates, which this
    run did. The screenshot opens the run in the playground, as does the
    #box[`VIMP ↗`] tag on every later VIMP listing.],
) <fig:intro-answers>

A soundness proof must connect objects of different kinds. The analyzer
compiles the program to a control-flow graph, solves equations over abstract
states and reports a verdict per check, and each change of representation could
lose concrete behavior. The argument therefore follows one store that an
execution reaches through every representation (@fig:intro-nest). The compiler
simulation places it at a graph node $v$, the reached graph state is covered by a valid
activation-local trace (#isaconst("valid_ltr"), #isathm("source_reaches_ltr_collect")), and under the totality condition that trace falls
into a context bucket whose solved value admits the store. A `PROVED` check at
$v$ holds for every admitted store. Each check row of the result carries its source position, which
the unverified parser writes (@sec:trust-boundary).
Each outer set in @fig:intro-nest may add stores that no execution reaches,
which costs precision. Soundness needs only that it contains the set inside it.

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

== The verified solver and the open questions <sec:rqs>

Goblint is an abstract interpreter for multithreaded C programs @vojdani16 @seidl26. It defines analyses independently of the generic solvers that compute
their results, and the interface between the two is a side-effecting constraint
system @apinis12 @seidl26. A side effect lets the right-hand side of one
unknown contribute to others (@sec:side-effects). An Isabelle/HOL formalization of Goblint's top-down
solver has been verified, including its extension to side effects @stade24
@tilscher26. When it terminates, the verified solver returns a partial
post-solution (#isaconst("part_post_solution")) of the equation system it receives: a valuation that bounds the
right-hand side and side contributions of every unknown it has solved (@sec:td). Whether that system describes
the program, and whether the verdicts read off its solution hold, is outside
the solver's theorem. Its example analyses supply equations, written by hand or generated
from a program, and no proof relates them to the program's executions. Context sensitivity adds a second difficulty. The
analyzer keeps a separate abstract state per calling context, while the
ordinary concrete semantics has no notion of context. The thesis asks
whether this gap can be closed by machine-checked proof:

- whether the soundness of a configurable, context-sensitive interprocedural
  analyzer can be machine-checked from source executions to its reported
  verdicts, and what then remains trusted;
- which concrete executions a calling context denotes, so that per-context
  results are sound and together lose no execution;
- whether domain, context policy and solver can each be verified on its own,
  with one theorem composing them for every configuration;
- how strong the theorem is: which key obligations can be shown necessary,
  and whether non-vacuity and precision differences can be proved on concrete
  programs.

Voblint answers these questions for a Goblint-style analyzer with several context
policies, over a small language with parameters, return values and recursive
procedures. It is not a verification of Goblint itself. It isolates the parts of Goblint's architecture that the proof is about (calling contexts, side-effecting constraint systems, configurable domains and the top-down solver) in a language small enough to mechanize every semantic connection. Here, _end to end_ means from source executions to the result the analysis function returns. Voblint provides the semantic connections on both sides of the solver and depends on it only through its post-solution guarantee (@ch:solving). @fig:intro-trust places each stage of the analyzer relative to the proof.

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

Most production abstract interpreters have no machine-checked soundness proof. Astrée analyzes
safety-critical C programs of up to 132,000 lines and reanalyzes each call in
place, which works because those programs do not recurse @blanchet03.
#cite(<livshits15>, form: "prose") know of no realistic whole-program analysis
tool that does not purposely make unsound choices. Testing finds defects
without proving their absence: random programs exposed fifty bugs in Frama-C
@cuoq12, and interrogation
testing found 16 soundness issues in seven of eight analyzers, among them the abstract interpreter MOPSA @kaindlstorfer24.

CompCert provides a precedent for a theorem about a delivered tool: it proves
that its compiled code behaves as the source semantics specifies and lists the
components that remain trusted @leroy09. On Goblint's side, local traces give each thread a concrete semantics from which
thread-modular analyses are derived, on paper @schwarz21 @schwarz23, and trace
partitioning indexes sets of traces by control history @rival07.

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
      [*Voblint*], [Isabelle], [VIMP], [covered], [relation], [TD solver], [yes],
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
Voblint. For _recursion_, Verasco raises an alarm where a recursive call can
occur, and Lammich and Müller-Olm interpret calls and returns exactly. The
soundness theorems of Blazy et al., Cachera et al., Dabrowski and Pichardie and
Voblint quantify over all programs, recursive ones included, and the analysis of Blazy et al. stays
intraprocedural by forgetting the result variable of a call. Three works analyze languages without procedures.
For _contexts_, Verasco reanalyzes a function at every call site, Dabrowski and
Pichardie compute object-sensitive contexts by a function, Lammich and
Müller-Olm use per-procedure summaries, and Voblint admits contexts through a
relation that may admit several per call. For the _fixpoint_, three analyzers
iterate over the program's syntax ("structural"), Nipkow and Klein iterate over
the whole annotated program, Blazy et al. check the result of an untrusted
iterator, Cachera et al. use a verified solver of ordinary
inequations, and two works only specify constraints and prove every solution
sound. Nipkow and Klein run their analyzer inside Isabelle.

To our knowledge, no prior mechanized analyzer connects a source semantics to
a side-effecting constraint system, in which right-hand sides contribute to
shared unknowns, or is proved sound through a verified solver for such
systems. In Voblint, every call publishes its callee's entry state as a side
effect to a shared unknown (@sec:eq-seed), and the
end-to-end theorem covers this for every accepted program whose solve
terminates. The contributions below address this gap.

== Contributions <sec:contributions>

The contribution is the Isabelle/HOL formalization of Voblint and its
machine-checked soundness proof. Each claim
answers one of the questions of @sec:rqs.

- _End-to-end soundness._ The definite verdicts returned by the analysis
  function #isaconst("run_voblint") are correct for every source execution
  from an initial store with zeroed globals (#isaconst("cinit_stores")) that
  reaches the corresponding program point, in every configuration it offers,
  provided the solve terminates (#isaconst("config_terminates"))
  (#isathm("run_voblint_certified_source_sound"), @sec:headline). Companion
  theorems justify `DEAD` and the absence of arithmetic warnings.
- _A concrete semantics of calling contexts._ A context policy is a relation
  between calls and callee contexts (#isatype("call_context_rel")), which
  determines the contexts an activation-local trace carries. Under the
  coverage contract (#isalocale("ltr_coverage")), whose totality condition
  admits every call the claim covers at some context, the per-context
  collections together equal the context-free collection
  (#isathm("ltr_collect_eq_Union_activation_collect"), @sec:consequences).
- _Compositional soundness._ Domain, context policy and solver are verified
  separately. One theorem discharges the coverage contract for every policy
  that proves its routing adequacy and totality, in every domain
  (#isathm("activation_collect_dg_sound"), @sec:eq-discharge), and the
  source-level theorem covers every configuration.
- _Necessity and non-vacuity as theorems._ Counterexample theorems show that
  dropping or weakening several obligations in the exhibited ways admits
  unsound results (#isathm("total_dropped_unsound")), and theorems proved by
  evaluation give non-vacuous verdicts (#isathm("nv_check_proved_sound")) and
  a strict precision separation on a concrete program
  (#isathm("sign_k2_strictly_more_precise_than_k1_at_g"), @sec:eval-rq4).

The solver, side-effecting constraint systems, local traces and Goblint's
analysis architecture come from prior work. @sec:where-voblint-sits lists what
is new and compares each claim with the closest existing result. The thesis
claims no verified C frontend, heap analysis, completeness, general termination
of the solve, or general precision ordering between configurations. VIMP's integers are unbounded and division by
zero is defined, so a verdict about a VIMP program does not automatically
transfer to a corresponding C program (@sec:vimp-vs-c).

== Outline

@ch:background gives the order-theoretic and Isabelle background. #partref(<part:over-approx>) fixes
what an analysis must over-approximate: source execution and its compilation
to a graph (@ch:program-model), and activation-local traces with contexts and
the coverage contract (@ch:traces). #partref(<part:analyzer>) builds the analyzer from
separately verified ingredients: domains (@ch:domains), the analysis
interface (@ch:analysis-interface), the equations (@ch:equations) and the
solver (@ch:solving), and @ch:results composes
them into the source-level theorem. #partref(<part:instances>) instantiates it for five domains
(@ch:instances), follows #isaconst("run_voblint") to the delivered tools and the
trust boundary (@ch:executable), and assesses the evidence for each question
(@ch:evaluation). #partref(<part:assessment>) compares the work with prior systems (@ch:related)
and answers the questions (@ch:conclusion). @fig:intro-nest names the chapter
that defines each set of the soundness chain.
