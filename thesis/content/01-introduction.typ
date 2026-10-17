#import "../lib/code.typ": fixture, isaconst, isalocale, isathm, isatype, listing, oblig
#import "../lib/figures.typ": check-row, partref, verdict
#import "../lib/sources.typ": proved
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/claims.typ": claim-ref

= Introduction <ch:intro>

A static analyzer answers questions about every execution of a program at once:
whether a divisor can be zero at some point, whether a program point is
reachable at all, or whether a check always holds. Users act on these answers
without running the program, so the answers have to be right. The analyzer,
however, is itself a program, and its errors produce confident answers that
real executions contradict. In Goblint
#link("https://github.com/goblint/analyzer/issues/1156")[issue 1156], Goblint
claimed that `c % 2 == 1` holds for $c in {-5, -7}$ @goblint1156, although the
truncating remainder of C11 @iso-c11[§6.5.5p6] gives $-1$ for both values. The
congruence domain had ignored the sign of the dividend, and
#link("https://github.com/goblint/analyzer/pull/1161")[pull request 1161] fixed
it @goblint1161. An error of this kind is worse than imprecision. An imprecise
answer leaves the check undecided, whereas a wrong answer gives a user who
trusts it no reason to look for the error.

Fixing one such bug does not rule out the next. Ruling out all of them requires
a proof that the analyzer's answers hold for every execution of every program,
and that proof must itself be checked. Formal verification states such a claim
as a proposition over explicit definitions, and a proof assistant checks its
proof @nipkow14. Isabelle/HOL constructs every theorem through a small trusted
inference kernel, following the LCF approach @paulson19. Trusting a proof
therefore means trusting this kernel and the system it runs on, not the tactics
that produced the proof.

The kernel, however, checks a proof only against the definitions it is given.
Whether those definitions model the intended objects, and whether the theorem
expresses the intended claim, is left to human review. A review of parts of an
Isabelle/HOL formalization of Munkres' general topology found
definitions that are logically weaker than the textbook's. They are harmless
only because each theorem assumes the missing constraints again
@bryant26munkres[§8.1]. Verification projects therefore state
explicitly what lies outside the proof. The seL4 proof, for example, relates
the kernel's C implementation to an abstract specification in Isabelle/HOL and
names the compiler, assembly code, boot code, cache management, and hardware as
assumptions. It also assumes that its formal model of C reflects the C standard
@klein09.

In this thesis, we build Voblint, an executable analyzer whose answers are
proved to hold for every execution of the analyzed program, and we state
exactly under which assumptions this proof holds. Voblint draws its boundary at
the source language. Its main theorem starts from _source executions_, the
executions of a program under the small-step semantics #isaconst("pstep") of
Voblint's input language VIMP. Every later representation, from the
control-flow graph to the solver's result, is connected to source executions by
proof. Of the semantics, only #isaconst("pstep") therefore needs an adequacy
argument instead of a proof. That argument states which fragment of C it models, where it departs
from C11 (@sec:vimp-vs-c), and why no existing verified semantics serves as the
anchor.

== From executions to static guarantees <sec:intro-static>

Testing and static analysis make different kinds of claims about a program.
Software is usually checked by testing. A failing test demonstrates a bug, but
a passing test suite has observed only finitely many executions
@rival20[§1.4.1]. A static analysis reasons about all
executions instead. At each program point, it computes an _abstract state_. An
abstract state is a finite representation of a set of program states, for
instance, an interval
that contains every value a variable takes whenever execution reaches the
point. The analysis is _sound_ if the abstract state contains every state that
occurs in a real run, although it may contain more. If a sound abstract state
contains no state that violates a check, no execution violates it, tested or
not (@fig:intro-runs). The converse does not hold.
An abstract state can contain violating states that no execution reaches, and
the analysis then cannot decide the check, even when every execution satisfies
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
therefore raise false alarms and leave checks undecided, but it never makes a
false claim. It is
useful as long as it decides the checks of interest often enough
@rival20[§1.3.5]. Since every sound analysis over-approximates the same
executions, analyses can specialize. One tracks intervals, another parities, and
another relations between variables. If any one of them proves a check, the
check holds in every run that reaches it. An analysis can also separate the
activations of a procedure by their _calling context_, an abstraction of how
the call was reached, such as the call site or the abstract state at entry. It
then keeps one abstract state per program point and context, and it may analyze
one call in several contexts, for instance one per abstract state that reaches
the call. A richer domain or more contexts
can decide more checks, but they also make the analysis more expensive. If there
are
many contexts, the analysis may not finish in practice.

Voblint answers every check that the user writes into the source program as
`__voblint_check(e)`. It also warns at every division and remainder where it cannot
exclude a zero divisor. @fig:intro-answers shows a run in the
#link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html")[browser
  playground] together with what each answer guarantees. #verdict("PROVED") and
#verdict("REFUTED") are the _definite_ verdicts, and #verdict("UNKNOWN") claims
nothing. Only #verdict("DEAD") makes a claim about reachability, and
#verdict("REFUTED") is not a verified counterexample. Voblint offers several abstract domains and context policies
(@ch:instances), and the run shown uses intervals without calling contexts.

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
    shows it, with the interval domain and no calling contexts. The analysis
    covers every value of `t` at once. The screenshot opens the run in the
    playground (claim #claim-ref("intro-answers"), fixture
    #fixture("24-site-figures/precision/48-clamp_every_answer.vimp")).],
) <fig:intro-answers>

== The gap Voblint closes <sec:state-of-art>

Most abstract interpreters in practical use have no machine-checked soundness
proof and rely on testing instead. Livshits et al. know of no realistic
whole-program analysis tool that does not purposely make unsound choices, and
they observe that virtually all published whole-program analyses are unsound
@livshits15[p. 44]. Such an analysis has a sound core that over-approximates
most language features and models all their possible behaviors. It instead
under-approximates a few features that experts in the area know well, such as
reflection in Java, `eval` in JavaScript, or `setjmp`/`longjmp` in C. The
analysis then pretends that some possible behaviors of these features cannot
happen, for instance that `eval` does nothing, so its result can miss
executions. The authors call such analyses _soundy_. They treat this as an
engineering choice for precision and scalability, and they ask authors to state
clearly the nature and extent of the unsoundness @livshits15[p. 45]. Goblint,
for instance, documents such assumptions. It assumes that pointer arithmetic
does not overflow and, by default, that array reads stay in bounds, and it notes
that this list is likely incomplete @goblint-assumptions.

A documented assumption tells the user where a soundness claim ends. Within
that boundary, however, the claim still rests on an implementation that no one
has proved correct. Even the analyzers in practical use that are designed to be
sound have no machine-checked soundness proof (@sec:rel-practice). The analyzers themselves are tested
instead, and these tests share the limit of testing any program
(@sec:intro-static). Since no specification gives the correct answer for an
arbitrary program, they compare an
analyzer's answers on whole programs with independent evidence: the values the
program computes when it runs, the answers of other analyzers, or the known
verdicts of benchmark programs. Cuoq et al. @cuoq12 run C programs generated
by Csmith and compare the results of Frama-C's value analysis with those of
compiled execution, and they report fifty bugs found and fixed in Frama-C.
Differential
testing, which flags answers on which analyzers disagree, has found soundness
issues in most of the analyzers it was applied to (@sec:rel-practice). Since its first participation in SV-COMP in 2021, a
competition on benchmark programs with known verdicts, Goblint has never
produced a false negative on the competition's benchmark suite @seidl26. Still, its
developers report soundness issues that the benchmarks missed
@saan26phd[§3.4.6].
// TODO: check the claim above against Saan's thesis, §3.4.6 (dspace.ut.ee unreachable on 2026-10-17).
Testing finds such an error only when some test program exercises it. The
Goblint defect at the start of this chapter shows only for a negative dividend,
and only in the congruence domain. A proof does not depend on such a program.
Voblint states a soundness obligation for each abstract operation, and its
proof covers every input, so the obligation of the congruence remainder covers
negative dividends as well.

Obligations for single operations, however, protect the user only if a theorem
connects them to the tool the user runs. Between the operations and the
reported verdict, the analyzer compiles the program, assigns calling contexts,
and solves equations, and each of these steps could lose executions. CompCert
shows that such a theorem is possible for a realistic tool. It proves that its
compiled code behaves as the source semantics specifies, and it lists the
components that remain trusted @leroy09. Verasco carries the approach to a
static analyzer for C @jourdan15, and several other abstract interpreters have
machine-checked soundness proofs as well. None of the works we compare, however,
combines recursive procedures, calling contexts that may split one call, and a
verified solver (@sec:rel-mechanized). Goblint's architecture uses the first
two and a generic solver, whose top-down algorithm has since been verified. It
analyzes recursive programs and keeps one abstract state per program point and
calling context.

Goblint defines its analyses independently of the solvers that compute their
results, and Voblint follows this architecture @vojdani16 @seidl26. The
interface between the two is a side-effecting constraint system @seidl03
@apinis12 @seidl26. Such a system relates unknown abstract values by
inequalities, and the inequality of one unknown may also contribute to other
unknowns. For the last step of the chain, a proof already exists. The top-down
solver that Goblint uses, including its extension to side effects, has been formalized
and proved partially correct in Isabelle/HOL @stade24 @tilscher26. When it
terminates, it returns values that satisfy the inequalities of the queried
unknown and of every unknown it transitively reads
(#isaconst("part_post_solution", thy: "Basics_side")). Whether the constraint
system describes the program, and whether the verdicts read off its solution
hold, lies outside that theorem.

Calling contexts make this gap hardest to close, since the per-context abstract
states of an analyzer have no counterpart in an ordinary concrete semantics.
Suppose `main` calls `bump(5)` and `bump(4)`, and `bump` returns its argument
plus one. An analysis whose contexts record the argument at entry claims the
result $6$ in the first context and $5$ in the second. The collecting semantics,
the set of stores that executions reach at each program point, holds both
results at the point where `bump` returns. It forgets how each store
was reached, so it does not say which store belongs to which context. To state
these claims, the concrete semantics must let us recover the contexts of every
_activation_, one execution of a procedure from its call to its return.
Voblint's activation traces record each activation together with the activation
that called it, and a context policy reads the contexts off this chain.

Voblint closes these gaps by combining existing ideas, some of them already
formalized and others so far only described on paper or implemented. Its
overall design mirrors Goblint's architecture inside Isabelle/HOL, without
formalizing Goblint's implementation or C (@sec:rel-goblint). It reuses the
verified top-down solver of Tilscher et al. @tilscher26 and builds on
established abstract-interpretation techniques. The
resulting theorem starts from source executions and holds for the executable
analyzer, which Isabelle's code generator @haftmann10 exports to OCaml. To our
knowledge, no prior mechanized analyzer connects a source semantics to a
side-effecting constraint system and its verified solver (@sec:rel-summary).

== Contributions <sec:contributions>

The contribution of this thesis is the Isabelle/HOL formalization of Voblint and
its machine-checked soundness proof, available at
#link(
  "https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis",
)[`github.com/ManuelLerchner/Voblint-Verification-Master-Thesis`]
and archived on Zenodo @voblint. The proof closes the gaps of
@sec:state-of-art with a chain of inclusions at every program point, from
source executions to the reported verdicts (@fig:intro-nest). Each step may add
states that no execution reaches, which costs precision, but must not lose a
reachable state. Errors such as a compiler that drops an edge or a return to
the wrong caller would lose such a state, and the proof excludes them.

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
          which cover the collecting semantics because the solver's result is a
          post-solution of the equations (@ch:equations to @ch:results)],
        ring(
          vb.cong,
          [Collecting semantics],
          [#isaconst("node_collect"): stores of valid traces ending at $v$, which
            under the coverage contract equals the same stores split by context,
            #box[$union.big_c$ #isaconst("activation_collect")]
            (#isathm("node_collect_eq_Union_activation_collect"), @ch:traces)],
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

The formalization makes five contributions. The first two close the gaps named
in @sec:state-of-art, and the third keeps the proof obligations of each
component local. The fourth turns the verified definitions into a tool that
runs, and the fifth addresses what the proof kernel cannot check.

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
  per-context states of an analysis their concrete counterpart. Each trace
  follows one procedure activation and records which activation called it, so
  the contexts of a call can be read off the concrete execution, and one call
  may receive several contexts. Splitting the concrete states by context then
  loses no execution (@sec:contract).
- _Separately verified components._ Each component discharges local soundness
  obligations, and generic theorems compose them into the end-to-end guarantee
  for every configuration. Domains prove their primitive operations sound,
  context policies prove that their contexts agree with the concrete
  semantics, cooperating analyses prove conditions on the answers they
  exchange (@ch:cooperation), and the solver enters the proof only through
  proved facts about its result (@sec:certificate).
- _An executable analyzer._ Isabelle's code generator exports
  #isaconst("run_voblint"), the constant the soundness theorem is about, to
  OCaml. A command-line tool and a browser playground run it on VIMP programs.
  The playground draws the control-flow graph, places the verdicts and
  arithmetic diagnostics in the editor, and can replay the solver's steps. @fig:intro-trust shows which parts stay outside the proof.
- _Needed assumptions and nonempty results._ The kernel cannot tell whether a
  theorem assumes too much or concludes too little. Further theorems therefore
  show that several conditions of the proof cannot be dropped, since dropping
  them admits answers that concrete executions contradict (@sec:eval-1161).
  Others show that the analyzer gives definite verdicts on concrete programs
  (@sec:nonvacuity) and that one context policy is strictly more precise than
  another on one program (@sec:eval-precision).

== Scope and limitations <sec:intro-scope>

Voblint is a Goblint-style analyzer with several context policies, over a
small language with parameters, return values, and recursive procedures. It
isolates the parts of Goblint's architecture that the proof is about: calling
contexts, side-effecting constraint systems, configurable domains, analyses that
answer one another's queries, and the top-down solver. It is not a verification
of Goblint itself. _End-to-end_ means that the proof reaches from source
executions to the result that the analysis function returns.  @fig:intro-trust places each
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
        )[Source semantics: #isaconst("pstep") and its operators]),
        align(center, text(fill: vb.neutral)[#sym.arrow.b]),
        zone(vb.proved, [proved in Isabelle/HOL])[
          #p[CFG compiler] #arrow #p[equations] #arrow #p[solver] #arrow #p[result, verdicts]
        ],
      ),
      arrow,
      grid.cell(align: bottom, zone(vb.unproved, [unverified output], dash: "dashed")[
        #u[adapters, \ state printing]
      ]),
      grid.cell(colspan: 5, zone(vb.trusted, [trusted foundation])[
        Isabelle kernel · code generator and target mappings · OCaml and WebAssembly
        toolchains · Zarith · browser
      ]),
    )
  },
  placement: none,
  caption: [Where the proof starts and stops, for accepted programs whose solve
    terminates. The adequacy of #isaconst("pstep") is argued
    (@sec:vimp-vs-c). Zarith is OCaml's arbitrary-precision integer
    library, and @sec:trust-boundary gives the exact boundary.],
) <fig:intro-trust>

The theorem has the following limits (@sec:limitations).

- _Language and properties._ VIMP has no pointers, heap, or threads. Its
  integers are unbounded, division by zero is defined, and a callee's locals
  start at 0. Therefore, a verdict
  does not always hold for a C program with the same text (@sec:vimp-vs-c).
  Voblint checks assertions and division by zero, while Goblint also checks
  overflows, data races, memory
  safety, memory leaks, and program termination @saan26phd[§3.3].
- _Adequacy and trusted components._ We argue, but do not prove, that #isaconst("pstep") models the intended language (@sec:vimp-vs-c). The parser, the code generator, and the target
  toolchains lie outside the proof (@sec:trust-boundary).
- _Partial correctness._ The theorem covers every report the analyzer returns.
  Termination of the solve is not proved for every program (@sec:termination).
- _Precision and cost._ No completeness or general precision ordering is
  proved (@sec:eval-precision). The executable uses the same data
  representations as the proofs, and we report no time or memory measurements
  (@sec:limitations).
- _Goblint and evidence._ The correspondence to Goblint is architectural, and
  no theorem transfers to Goblint's implementation (@sec:rel-goblint). The
  regression corpus is small and was written or adapted for this work
  (@sec:eval-corpus).

== Outline

#partref(<part:problem>) consists of this introduction and @ch:background,
which recalls what the later chapters build on: the collecting semantics,
lattices and fixpoints, abstract interpretation, constraint systems with
widening and narrowing, side-effecting constraint systems and the verified
top-down solver, and the Isabelle/HOL mechanisms the development uses. The
remaining parts follow the nested sets of @fig:intro-nest from the inside out.

#partref(<part:over-approx>) fixes what an analysis must
over-approximate: VIMP and its compilation to a control-flow graph
(@ch:program-model), and activation traces indexed by calling context with the
coverage contract that analyses must meet (@ch:traces).

#partref(<part:analyses>)
develops what each analysis
contributes, without contexts or a solver: the abstract domains
(@ch:domains), the interface through which an analysis supplies its transfer
functions (@ch:analysis-interface), and the combination of analyses that query
one another (@ch:cooperation).

#partref(<part:verdicts>) turns any analysis that meets this interface into a
sound result. @ch:equations generates the equations of a program, @ch:solving
computes their solution with the verified solver, and @ch:results composes
these parts into the source-level theorem.

#partref(<part:instances>) puts the
theorem to use. @ch:instances instantiates it for five numeric domains and a relational order analysis. @ch:executable follows #isaconst("run_voblint") to the delivered tools and their trust boundary. @ch:evaluation tests the premises and
obligations, the precision, and the unverified code, and @ch:tooling describes
the tooling.

#partref(<part:assessment>) compares Voblint with prior work
(@ch:related) and closes with limitations and future work (@ch:conclusion).
