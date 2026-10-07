#import "../lib/code.typ": fixture, isaconst, isalocale, isathm, isatype, listing, oblig
#import "../lib/figures.typ": check-row, partref
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
@goblint1161. An unsound answer of this kind is worse than an imprecise one:
a user who trusts the answer stops looking for the bug it hides.
This thesis asks under which assumptions the answers produced by an executable analyzer are sound for every execution of the analyzed program.

Formal verification states such a claim as a proposition over explicit
definitions, and a proof assistant checks its proof @nipkow14. Isabelle/HOL
follows the LCF approach: every theorem is constructed through a small trusted
inference kernel @paulson19. Because the kernel checks each step, a proof
found by an automated tool or an AI system passes the same check as one
written by an expert. Proof assistants have therefore become a target for AI
systems. Bryant et al. @bryant26munkres, for example, report LLM coding agents
that produced over 85,000 lines of Isabelle/HOL covering Munkres' general topology,
with all 806 results proved. This thesis was developed with AI assistance as
well (see #link(<ai-use>)[Use of Generative AI]), and the same argument
applies to it.

The kernel guarantees only that the formal statement follows from the
definitions. Whether the definitions model the intended objects, and whether
the statement expresses the intended claim, remains for human review. A manual
review of parts of the Munkres formalization shows that this review matters:
it found definitions logically weaker than the textbook's. The authors judge them harmless for the proved theorems only
because each theorem assumes the missing constraints again
@bryant26munkres[§8.1]. The same review applies to statements. OpenAI's
proposed Lean proof of finite-time blowup for the three-dimensional
Navier–Stokes equations (September 2026)
formalizes alternatives (C) and (D) of the Clay problem @openai26ns
@openai26nspaper @openai26nslean. The kernel checks the proof of that formal
statement, and a reader checks that the statement is the Clay problem.

Verification projects therefore state this boundary explicitly. The seL4 proof
relates the kernel's C implementation to an abstract specification in
Isabelle/HOL and names as assumptions the compiler, assembly code, boot code,
cache management and hardware @klein09. Voblint draws its boundary at the
source language. Its main theorem starts from source executions, so the graph
and trace semantics in between are connected to the source by proof and need
no adequacy argument of their own. Only the source semantics, VIMP's own
small-step semantics #isaconst("pstep"), must be argued adequate: which
fragment of C it models and where it departs from C11 (@sec:vimp-vs-c), and
why no existing verified semantics such as IMP2 @lammich19imp2 serves as the
anchor (@sec:vimp). Isabelle checks the theorems, and this thesis explains what they
state and why they are the statements one wants of an analyzer.

== From executions to static guarantees

Software is usually checked by testing. A unit test runs one function on
chosen inputs and compares the results with the expected ones, and an
integration test does the same for several components working together. A failing test demonstrates a bug. A passing test suite, however, has
observed only finitely many executions @rival20[§1.4.1] and says nothing about
the inputs it did not try. Analyzers themselves are tested in the same way and
share this limit: a test compares an analyzer's answers with the executions of
one program and says nothing about the next program it analyzes. A static
analysis reasons about all executions
instead. At each program point it computes an _abstract state_, a finite
representation of a set of program states, for instance an interval that
contains every value a variable takes whenever execution reaches the point.
Soundness requires the abstract state to contain every value that could occur
in a real program run. Potentially, it contains more. This asymmetry decides what an
analysis can prove. Every execution lies inside the abstract state, so if the
abstract state contains no state that violates a check, no execution violates
it, including executions that no test ever tried (@fig:intro-runs). The
converse does not hold. Because an abstract state represents a set of states
only approximately, it can contain violating states that no execution reaches.
The analysis then cannot decide the check, even when every execution satisfies
it.

Suppose, for instance, that the analysis computes $x in [43, +infinity]$ at a
point that divides by `x`. Every execution that reaches the point has $x >= 43$
there, so the division is safe. If the analysis computes only $x in [0, 100]$,
the abstract state contains $x = 0$ and the analysis cannot prove the division
safe, although every real execution may still have $x >= 43$, for instance
because of a relation to another variable that an interval cannot express.

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

This incompleteness cannot be avoided. By Rice's theorem, no algorithm decides
a nontrivial semantic property for every program of a Turing-complete language
@rice53 @rival20[§1.3.3]. A sound over-approximating analysis therefore permits false alarms or
undecided checks, but no false claims. It remains useful as long as it decides
the checks of interest often enough @rival20[§1.3.5]. Since every sound
analysis over-approximates the same executions, analyses can also specialize:
one tracks intervals, another parities, another relations between variables.
A check that any one of them proves holds in every run. Precision has a price,
however. A richer domain or more calling contexts decide more checks, but they
enlarge the equations the analyzer solves, and with unboundedly many contexts
the solve need not terminate.

Voblint answers every check that the user writes into the source program as a
`check` statement. It also warns at every division and remainder operation where
it cannot exclude a zero divisor. @fig:intro-answers shows the analyzer as it
runs in the
#link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html")[browser
  playground], together with what each answer guarantees. Only `DEAD` makes a
claim about reachability, and `REFUTED` is not a verified counterexample. Each
run fixes an analysis configuration: the abstract domain (Sign, Interval, Parity,
Congruence or the reduced-product domain Int), the context policy, and the
rule that combines contributions to global values. The run shown uses
intervals without calling contexts.

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
        [#_line("check(0 <= p && p <= 100)")], tag(_pg.proved, raw(_ans-proved.verdict)),
        [the condition holds whenever a run reaches it],
        [#_line("check(p > 100)")], tag(_pg.refuted, raw(_ans-refuted.verdict)),
        [the condition fails whenever a run reaches it; not a counterexample],
        [#_line("check(p == 50)")], tag(_pg.unknown, raw(_ans-unknown.verdict)), [nothing],
        [#_line("check(p == 0)")], tag(vb.neutral, raw(_ans-dead.verdict)),
        [no run reaches the check],
        [#_line("1000 / p;")], tag(_pg.warning, raw(_ans-warn.cond)),
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
    shows it (Interval, `warrow` globals, no contexts; claim #claim-ref("intro-answers"), fixture
    #fixture("24-site-figures/precision/48-clamp_every_answer.vimp")). The
    analysis covers every value of `t` at once. The screenshot opens the run in the playground, as does the
    #box[`VIMP ↗`] tag on every later VIMP listing.],
) <fig:intro-answers>

== State of the art <sec:state-of-art>

Most abstract interpreters in use have no machine-checked soundness proof, and
they earn trust by testing. Livshits et al. @livshits15 observe that realistic
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
      [Pulse-X @le22], [C], [bug finding], [summaries], [unrolled], [pure conditions],
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
  placement: bottom,
  caption: [Unverified analyzers and Voblint, as described by each tool's papers
    and documentation. _Stance_ is the tool's own soundness claim. Under
    _calls_, inlining re-analyzes the callee at every call, a summary is
    computed once per procedure, and _per context_ means one unknown per
    program point and context. _Recursion_ says how a recursive call is
    treated, and _covered_ means Voblint's theorem includes recursive calls.
    _Combination_ names how domains exchange facts, and _mechanized_ records
    what a proof assistant has checked. _End to end_ means from source
    executions to the verdicts of the exported function, for every answer it
    returns (partial correctness) and with the trusted components of
    @sec:trust-boundary.],
) <tab:production-analyzers>

@tab:production-analyzers compares Voblint with six analyzers that have no
machine-checked soundness proof. Four of them handle a call by inlining, which
analyzes the callee anew at every call and so never needs a context policy
@blanchet03[§5.3] @eva-manual[§5.3] @journault19[§5.1] @brat14[§3]. Recursion
is where they differ. Astrée, which proves the absence of run-time errors in
safety-critical C programs of up to 132,000 lines @blanchet03, targets programs
without recursion @blanchet03[§5.3]. Eva relies on a user-written contract or
unrolls to a given depth @eva-manual[§6.3.9], MOPSA lists recursion as
unsupported @mopsa-manual[Limitations], and IKOS assumes that a recursive call
may update any value in memory @ikos-readme[Analysis Assumptions]. Goblint,
like Voblint, solves for one unknown per program point and context and
analyzes recursive programs.

Pulse-X, an academic analyzer built from Infer on incorrectness logic, has a soundness theorem proved on paper for a
formal model: reported errors are real within that model @le22[pp. 81:2--81:3],
an under-approximating guarantee.

Testing checks such tools against executions. Cuoq et al. @cuoq12
compare Frama-C's value analysis with compiled execution on programs generated
by Csmith and report fifty bugs found and fixed.
Differential testing runs several analyzers on generated programs and flags
answers on which they disagree. Klinger et al. @klinger19 find soundness or
precision issues in four of six analyzers this way, and Kaindlstorfer et al. @kaindlstorfer24, who
question one analyzer repeatedly about related programs, find 16 soundness
issues in seven of eight, including MOPSA. A test exposes a defect on
one program and cannot show its absence. The Goblint defect at the start of
this chapter is the kind of transfer-function error that a per-operation
soundness obligation excludes inside the proof boundary.

The table also shows the price of the proof. The unverified analyzers accept
C, C++ or Python, and Astrée and IKOS have been applied to safety-critical
control software @blanchet03 @brat14[§3]. Voblint's theorem covers VIMP
(@sec:vimp), which has no pointers, heap or machine integers, and the proof
covers only the definitions it is about. Whether they model the intended
language is the adequacy question of @sec:vimp-vs-c.

CompCert provides a precedent for a theorem about a delivered tool: it proves
that its compiled code behaves as the source semantics specifies and lists the
components that remain trusted @leroy09. Verasco carries the approach to a static
analyzer for C @jourdan15. Local traces give each thread a concrete semantics from which
Goblint's thread-modular analyses are derived on paper @schwarz21 @schwarz23,
and Voblint's activation traces apply the same idea to procedure activations
(@ch:traces).

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
Voblint. For _recursion_, Verasco @jourdan15 raises an alarm where a recursive
call can occur, and Lammich and Müller-Olm @lammich07afp interpret calls and
returns exactly. The soundness theorems of Blazy et al. @blazy13, Cachera et
al. @cachera05, Dabrowski and Pichardie @dabrowski09 and Voblint quantify over
all programs, recursive ones included, and the analysis of Blazy et al. stays
intraprocedural.
A calling context distinguishes the activations of a procedure, for
instance by call site or by the abstract state at entry, and the analyzer
keeps one abstract state per program point and context. For _contexts_, Verasco reanalyzes a function at every call site, Dabrowski and
Pichardie compute object-sensitive contexts by a function, Lammich and
Müller-Olm use per-procedure summaries, and Voblint admits contexts through a
context policy that returns a set of contexts per call, since an entry
operation may split a call into several alternatives (@sec:contexts). For the _fixpoint_, three analyzers iterate over the program's syntax
("structural"), Nipkow and Klein over the whole annotated program, Blazy et
al. check the result of an untrusted iterator, Cachera et al. use a verified
solver of ordinary inequations, and two works only specify constraints.

Voblint's architecture follows Goblint, an abstract interpreter for
multithreaded C programs @vojdani16 @seidl26. Goblint defines analyses independently of the generic solvers that compute
their results, and the interface between the two is a side-effecting constraint
system @apinis12 @seidl26. A side effect lets the right-hand side of one
unknown publish contributions to others (@sec:side-effects). The top-down solver algorithm of
Goblint, including its extension to side effects, has been formalized and
proved partially correct in Isabelle/HOL @stade24 @tilscher26. When it terminates, the verified solver returns a partial
post-solution (#isaconst("part_post_solution", thy: "Basics_side")) of the equation system it receives (@sec:td): a valuation that bounds the
right-hand side and published contributions of every unknown it has solved, and
whose solved set contains every unknown those right-hand sides read. Whether that system describes
the program, and whether the verdicts read off its solution hold, is outside
the solver's theorem. No proof relates the equations of its example analyses to a program's
executions, and the per-context abstract states of an analyzer have no
counterpart in an ordinary concrete semantics: a run has a call stack, but nothing in it says
which context the analyzer assigned to an activation.

To our knowledge, no prior mechanized analyzer connects a source semantics to
a side-effecting constraint system, in which right-hand sides publish contributions to global unknowns, or is proved sound through a verified solver for such
systems. Voblint goes further than the analyzers above in two respects. Its
theorem covers context-sensitive analysis of recursive procedures, which
Astrée, MOPSA and Verasco exclude, and among the executable analyzers of
@tab:state-of-art it is the only one whose verified fixpoint solver handles
context-sensitive, side-effecting constraint systems. Its guarantee is stated
over source executions of the analyzed language, whereas that of Verasco
concerns C\#minor, an intermediate language of CompCert. It claims no better precision than any of them, and its language is far
smaller than the C dialects they analyze. The contributions
below address this gap.

== Contributions <sec:contributions>

The contribution is the Isabelle/HOL formalization of Voblint and its
machine-checked soundness proof, available at
#link("https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis")[`github.com/ManuelLerchner/Voblint-Verification-Master-Thesis`].
Such a proof must follow every execution through each representation the
analyzer uses: the source program, its control-flow graph, the equations over
abstract states and the reported verdicts. Each change of representation may
add states that no execution reaches, which costs precision, but it must not
lose a state that some execution reaches. A compiler that drops an edge, a
return to the wrong caller, a solver that stops before its equations hold, or
a verdict read at the wrong program point would each lose an execution, and
the analyzer would report a guarantee that some run violates. @fig:intro-nest
shows the resulting chain of inclusions at one program point.

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
      [#isaconst("verdict_stores"): stores in which every definite verdict at $v$
        holds (@ch:results)],
      ring(
        vb.accent,
        [Report],
        [#isaconst("report_sem"): stores the report's states at $v$ describe
          (@ch:results)],
        ring(
          vb.cong,
          [Activation collection],
          [$union.big_c$ #isaconst("activation_collect"): stores of valid traces at $v$
            in context $c$ (@ch:traces)],
          ring(
            vb.locale,
            [Node collection],
            [#isaconst("node_collect"): stores of valid traces ending at $v$ (@ch:traces)],
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
  placement: none,
  caption: [Soundness at a program point $v$ as nested sets. The source-level
    theorem chains these inclusions for every report the analyzer returns
    (#isathm("run_voblint_source_sound"), @ch:results).],
) <fig:intro-nest>

The list below details its four parts and names the closest prior work for
each.

- _End-to-end soundness._ The definite verdicts returned by the analysis
  function #isaconst("run_voblint") are correct for every source execution
  from an initial store with zeroed globals (#isaconst("cinit_stores")) that
  reaches the corresponding program point, for all analysis settings it offers,
  whenever it returns a report (#isathm("run_voblint_source_sound"),
  @sec:headline). Companion theorems justify `DEAD`
  (#isathm("run_voblint_dead_check_unreached")) and the absence of arithmetic
  warnings (#isathm("run_voblint_arithmetic_safe")). No mechanized analyzer we found proves
  this for recursive procedures under configurable context sensitivity
  (@tab:state-of-art).
- _A concrete semantics of calling contexts._ An analyzer keeps one abstract
  state per calling context, but ordinary executions carry no contexts. A context policy (#isatype("context_policy")) therefore maps each concrete
  call to the set of callee contexts it admits, and from these sets each
  activation trace gets the contexts it may carry
  (#isaconst("activation_context_rel")). Provided a claim meets the coverage
  contract (#isalocale("activation_coverage")), which admits every covered call
  at some context,
  the stores collected per context together equal the stores of the
  context-free semantics (#isathm("node_collect_eq_Union_activation_collect"),
  @sec:contract). Where the context function of Dabrowski and Pichardie
  picks exactly one context per call @dabrowski09, Voblint's context policy may admit
  several, as one trace can belong to several partitions in the coverings of
  trace partitioning @rival07[Rem. 3.2.4].
- _Separately verified components._ Domains, context policies, analyses and
  the solver are each verified against their own interface, and generic
  theorems compose them for all analysis settings the analyzer offers. A numeric
  domain proves only its primitive operations sound, and the transfer
  functions derived from them are proved sound once
  (#isalocale("sound_nonrelational_ops")). A context policy proves only that
  its contexts agree with the concrete semantics and that every call gets one
  (#isalocale("routed_context")), from which #isathm("activation_collect_dg_sound")
  derives coverage (@sec:eq-discharge). Analyses that
  exchange facts through Goblint-style queries compose, provided there is at least one component and each component's operations
  preserve the others' concretizations (#isathm("mcp_combine_sound"),
  @ch:cooperation). As with CompCert's solver interface @compcertKildall, the
  proof uses only proved facts about the solver's result (@sec:cert-param). Darais et al. @darais15 compose
  analyzers from parts, one per kind of sensitivity, with proofs on paper.
- _Needed assumptions and non-empty results._ For several proof obligations, a
  theorem exhibits a claim or abstract operation that meets the remaining
  conditions but misses a store some run reaches (e.g.
  #isathm("total_dropped_unsound"), @sec:falsification), so none of
  them can simply be dropped. A soundness theorem
  would also hold for an analyzer that answers `UNKNOWN` everywhere. Theorems
  proved by evaluation rule this out: the analyzer gives definite verdicts on
  a concrete program (#isathm("nv_check_proved_sound")), and one context policy
  is strictly more precise than another on a concrete program
  (#isathm("sign_k2_strictly_more_precise_than_k1_at_g"), @sec:eval-precision).

== Scope and limitations <sec:intro-scope>

Voblint is a Goblint-style analyzer with several context policies, over a
small language with parameters, return values and recursive procedures. It is
not a verification of Goblint itself. It isolates the parts of Goblint's
architecture that the proof is about: calling contexts, side-effecting
constraint systems, configurable domains, analyses that answer one another's
queries, and the top-down solver. The language is small enough to mechanize
every semantic connection. Here, _end to end_ means from source executions to
the result the analysis function returns. Voblint provides the semantic
connections on both sides of the solver and depends on it only through its
post-solution guarantee and two side facts (@sec:cert-param). @fig:intro-trust places each stage of
the analyzer relative to the proof.

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
    terminates. The adequacy of #isaconst("pstep") is argued (@sec:vimp-vs-c),
    and @sec:trust-boundary gives the exact boundary.],
) <fig:intro-trust>

Voblint builds on prior work. The solver and the soundness proofs of its update
rules come from Tilscher et al. @tilscher26, the rules from
Stemmler et al. @stemmler25, side-effecting constraint systems from
Apinis et al. @apinis12, and the local/global analysis architecture
from Goblint. Widening, narrowing and the reduced product are well studied
@cousot77 @cousot79. The derivation of transfer functions from sound value operations follows
Nipkow and Klein
@nipkow14[Sects. 13.5, 13.7]. The activation traces adapt the local traces of
Schwarz et al. @schwarz21 to procedure activations. Isabelle's code generator
@haftmann10 produces the OCaml code the tools run.

The theorem has the following limits. @sec:limitations discusses each of them.

- _Language._ VIMP has no pointers, heap or threads, its integers are unbounded and
  division by zero is defined, so a verdict need not transfer to a C program
  with the same text (@sec:vimp-vs-c).
- _Adequacy._ That #isaconst("pstep") models the intended language is argued,
  not proved (@sec:vimp-vs-c).
- _Partial correctness._ The theorem covers every answer the analyzer returns.
  Termination of the solve is not proved for every program
  (@sec:termination).
- _Trusted components._ The parser, the code generator and the target
  toolchains lie outside the proof (@sec:trust-boundary).
- _Precision._ No completeness or general precision ordering between
  analysis settings is proved. Each precision result concerns one program
  (@sec:eval-precision).
- _Goblint._ The correspondence with Goblint is architectural. No theorem
  transfers to its OCaml implementation (@sec:eval-goblint).
- _Direction._ The simulation from source runs to graph runs and the
  representation of graph runs by traces are proved in the forward direction
  only, the direction soundness needs (@sec:csim).
- _Executable cost._ The executable keeps the data representations of the
  proofs, such as lists for finite sets, and no time or memory measurement is
  reported (@sec:limitations).
- _Evidence beyond the theorem._ Each counterexample theorem weakens one
  condition on one program (@sec:falsification), and the regression corpus is
  small and written for this work (@sec:eval-corpus).

== Outline

After the background of @ch:background, the thesis follows the nested sets of
@fig:intro-nest from the inside out.

#partref(<part:over-approx>) fixes what an analysis must over-approximate.
@ch:program-model defines VIMP, its source semantics and its compilation to a
control-flow graph. @ch:traces turns graph runs into activation traces,
indexes them by calling context, and states the coverage contract that an
analysis must meet.

#partref(<part:analyses>) develops what each analysis contributes, without
contexts or a solver. @ch:domains develops the abstract domains,
@ch:analysis-interface the interface through which an analysis supplies its
transfer functions, and @ch:cooperation the combination of analyses that query
one another.

#partref(<part:verdicts>) turns any analysis that meets this interface into a
sound result. @ch:equations generates the equations of a program, @ch:solving
computes their solution with the verified solver, and @ch:results composes
these parts into the source-level theorem.

#partref(<part:instances>) puts the theorem to use. @ch:instances
instantiates it for five domains and an order analysis, @ch:executable follows
#isaconst("run_voblint") to the delivered tools and their trust boundary,
@ch:evaluation evaluates the theorem's coverage, strength and precision, and @ch:tooling describes the tooling built around the formalization.

#partref(<part:assessment>) closes the thesis. @ch:related compares Voblint's
mechanisms with the closest prior constructions, and @ch:conclusion discusses
the design, collects the limitations and outlines future work.
