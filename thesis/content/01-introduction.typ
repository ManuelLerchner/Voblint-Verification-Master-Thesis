#import "../lib/code.typ": (
  fixture, isaconst, isalocale, isathm, isatype, listing, oblig, rebase, site,
)
#import "../lib/figures.typ": check-row, partref, verdict
#import "../lib/sources.typ": proved
#import "../lib/math.typ": *
#import "../lib/theme.typ": metro, vb
#import "../lib/stats.typ": stat

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

Fixing one such bug does not rule out the next. Guaranteeing correct answers
requires a proof that they hold for every execution of the analyzed program.
Since analyzers are complex programs, a pen-and-paper proof of this property is
too long to check reliably by reading it. Large formalizations are therefore
better left to a proof assistant, which has been shown to scale to complete
systems such as the CompCert C compiler @leroy09 and the seL4
operating-system kernel @klein09. In a proof assistant such as Isabelle/HOL
@nipkow14, definitions and theorems are stated in a formal logic, and a small
trusted kernel checks every inference step of every proof @paulson19. A proof that contains an
error is therefore rejected, and the theorem it claims is not established.

This thesis carries out such a verification for a static analyzer. It presents
Voblint, short for verified Goblint, an analyzer that follows Goblint's
architecture and is formalized in Isabelle/HOL together with a machine-checked
soundness proof. Voblint analyzes VIMP, a small C-like language with integer
variables and recursive procedures, and the proof covers well-formed VIMP
programs whose analysis terminates. The soundness theorem
starts from _source executions_, the executions described by VIMP's rules for
individual computation steps (#isaconst("pstep")). The analyzer itself computes
on a control-flow graph (CFG), whose nodes are program points and whose edges
are possible steps between them. Every later representation is connected to
the source executions by proof, which gives an end-to-end formalization from
the input program to the reported verdicts. Isabelle's code generator then
exports the proved analysis function to OCaml, where it runs in a command-line
tool and in a #link(site("playground.html"))[browser playground], a web page
that analyzes a program the reader enters.

The kernel, however, checks proofs only against the definitions it is given.
Whether the computation rules of VIMP are adequate for the C programs that
Goblint analyzes therefore lies outside the proof and can only be argued in
prose. @sec:vimp-vs-c presents the most relevant differences
between VIMP and C11.

== Static analysis by abstract interpretation <sec:intro-static>

Software is usually checked by testing. A failing test shows a bug, but
a passing test suite has observed only finitely many executions
@rival20[§1.4.1] and makes no claim about the inputs it did not try. A static
analysis reasons about all executions instead. When an execution reaches a
program point, its state there is a _store_, which maps each program variable
to its current value. For most programs, the stores that reach a point are far
too many to enumerate, and with unbounded integers there can be infinitely many.
A value read from input or produced by a random-number function can be any
value of its type, and a loop can run arbitrarily often and produce a new value
in each iteration. At each program point, the analysis therefore computes an
_abstract state_, a finite representation of a set of stores. For instance, an
abstract state can give each variable an interval that contains every value the
variable takes whenever execution reaches the point. The analysis is _sound_ if the abstract state contains every store that
might occur in a real run, although it may contain more. The abstract state is then an _over-approximation_. Soundness lets the analysis prove
_conditions_, properties of the store at a program point such as $x != 0$. If a
sound abstract state contains no store that violates a condition, no execution
violates it, tested or not (@fig:intro-runs). The converse does not hold.
An abstract state can contain violating stores that no execution reaches, and
the analysis then cannot decide the condition, even when every execution satisfies
it.

Suppose the analysis computes $x in [43, +infinity)$ at a point that divides
by `x`. Every execution that reaches this point has $x >= 43$, so the division is
safe. If it computes only $x in [0, 100]$, the abstract state contains $x = 0$,
and the analysis cannot prove the division safe. However, every real execution
may still have
$x >= 43$, for instance, because of a relation to another variable that
cannot be expressed by tracking intervals alone.

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
of a Turing-complete language @rice53 @rival20[§1.3.3]. An analysis that
always terminates must thus give up either soundness or completeness. A sound
analysis keeps soundness and accepts false alarms and undecided questions in
return. It is useful as long as it decides the questions of interest often
enough @rival20[§1.3.5]. Since every sound analysis over-approximates the same
executions, analyses can specialize. One could describe the set of occurring
stores by intervals, by parity information, or by a relation between two
variables. If any one of these descriptions, or their combination, proves a
condition, the condition holds in every run that reaches it.

For languages with procedures, calls add a further modeling choice. Each call
starts an _activation_, one invocation of a procedure including any calls it
makes @aho06[§7.2.1]. An interprocedural analysis can merge all activations of
a procedure, or it can separate them by their _calling context_, an
abstraction of how the call was reached. In the two classical choices, a
context records either the chain of call sites that led to the call or the
abstract state at entry @sharir81. A context-sensitive analysis keeps one
abstract state per program point and context, and it may analyze one call in
several contexts, for instance, one per abstract state that reaches the call.
Finer descriptions of the stores and more contexts can decide more conditions,
but they also raise the cost of the analysis. If there are many contexts, the analysis may not
finish in practice.

Which conditions an analysis should decide is usually up to its user. Static
analyzers typically let the user write _checks_ into the source code,
conditions that the analyzer then attempts to prove or refute. Goblint, for
instance, provides `__goblint_check` for this purpose. Each answer to a check
is only as trustworthy as the soundness of the analyzer that gives it.

== Soundness of existing analyzers <sec:state-of-art>

Most abstract interpreters in practical use have no machine-checked soundness
proof and rely on testing instead. Livshits et al. observe that virtually all published whole-program analyses
are unsound and that every realistic tool makes unsound choices on purpose
@livshits15[p. 44]. Most of these analyzers have a sound core that
over-approximates most language features and models all their possible
behaviors. Around this core, they under-approximate a few features that are hard to model
soundly, such as reflection in Java, `eval` in JavaScript, or
`setjmp`/`longjmp` in C. The analysis then assumes, for instance, that `eval` does
nothing, so its result can miss executions. The authors call such analyses
_soundy_. They treat this as an engineering choice for precision and
scalability, and they ask the authors of such analyses to state explicitly the
nature and extent of the unsoundness @livshits15[p. 45]. Goblint also documents
such assumptions. For example, it assumes that pointer arithmetic does not
overflow and, by default, that array reads stay in bounds, and it calls this
list likely incomplete @goblint-assumptions.

A documented assumption marks where a soundness claim ends. Within
that boundary, however, the claim usually rests on an implementation that is
tested rather than proved. The same holds even for analyzers designed to be sound, apart from a few verified
ones such as Verasco @jourdan15 (@sec:rel-practice). Testing can still suffice in practice. Goblint, for example, has never produced a false negative on the
benchmark suite of SV-COMP, a competition on programs with known verdicts,
since its first participation in 2021 @seidl26. The soundness issues mentioned
above, however, were reported during the same years. A benchmark suite covers
only finitely many programs, so testing an analyzer is
as incomplete as testing any other program (@sec:intro-static). A guarantee for every program requires a proof
instead.

== Modular soundness proofs <sec:intro-modular>

A soundness proof for an analyzer has to follow the analysis from the program
to the reported verdict, and the steps it must follow depend on how the
analyzer is built. Verasco, for example, computes its result by iterating over
the syntax of the program @jourdan15. Goblint, on which Voblint is modeled,
instead compiles the program into a control-flow graph, assigns calling
contexts, and solves a system of equations. Each of these steps must preserve
the concrete executions that the verdict is meant to cover. A proof about
single abstract operations, on paper or in a proof assistant, therefore
protects the user only if a theorem connects these operations to the tool the
user runs.

A monolithic proof of all these steps for one fixed analyzer would be large,
and every change to a component would invalidate it. The proof becomes
manageable if it is split along the components of the analyzer, so that each
component proves a local obligation about its own operations. An abstract
domain then proves that its operations over-approximate the concrete ones. A
policy for calling contexts proves that its contexts agree with the concrete
calls, and a solver proves that its result satisfies the equations it was
given. Generic theorems, proved once, combine these obligations into a
soundness theorem for the whole analyzer. As a result, a new domain or context
policy only has to discharge its own obligation, and a verified solver can be
reused for every analysis. The proof can split only where the analyzer itself
does, since each obligation is stated about the operations of one component. A
modular proof therefore follows the module structure of the implementation it
verifies. Goblint already separates its analyses, its context policies, and its
solver, so a proof can follow this structure.

== The Goblint analyzer <sec:intro-goblint>

Goblint is an abstract interpreter for C programs @vojdani16 @seidl26.
Besides user-written checks, it looks for integer overflows, data races,
memory-safety errors, memory leaks, and nontermination @saan26phd[§3.3].
Despite this range of analyses, its architecture is uniform. Goblint defines
each analysis independently of the solver that computes its results
@vojdani16 @seidl26, and the two meet at a side-effecting constraint system
@seidl03 @apinis12 @seidl26. A side-effecting constraint system relates unknown abstract states by
inequalities, and the inequality of one unknown may also contribute to other
unknowns. These contributions are called side effects. They let an analysis
keep flow-insensitive information, such as the values of global variables, in
one unknown to which every program point contributes. They also serve calling
contexts. Under some context policies, a callee's contexts become known only
while the system is solved, so each call contributes its entry state to the
callee instead of the callee listing its callers in advance
(@sec:side-effects).

For a proof, this interface provides the decomposition of @sec:intro-modular.
The soundness
argument about programs then needs only the fact that the solver's
result satisfies the inequalities. For the solver itself, such a proof
already exists. The top-down (TD) solver algorithm, including an extension to
side effects, has been formalized and proved partially correct in Isabelle/HOL
@stade24 @tilscher26. When it terminates, it returns values that satisfy the
inequalities of the queried local unknown and of every local unknown it
transitively reads (#isaconst("part_post_solution", thy: "Basics_side")).
Whether the equation system describes the program, and whether the verdicts
computed from its solution hold, lies outside that theorem. To establish this connection,
every abstract state must be compared with the
concrete stores it describes. Calling contexts require a stronger concrete
semantics for this comparison than the classical collecting semantics, which
gathers the stores that executions reach at each program point @cousot77[§4]
@mine17[§3.4]. If `main` calls `bump(5)` and `bump(4)`, a context-sensitive
analysis keeps a separate state for each call. The collecting semantics, in
contrast, merges the stores of both calls where `bump` returns and forgets
which call produced which. Comparing per-context states therefore requires a
collecting semantics indexed by program point and context. Defining it requires
knowing, for every reached store, how its activation was called.

== Contributions <sec:contributions>

The main contribution of this thesis is an end-to-end formalization of a
static analyzer with Goblint's
architecture. It starts from the source executions
(#isaconst("pstep")) of a VIMP program, given as an abstract syntax tree, and
ends at the verdicts that the analyzer Voblint reports. The Isabelle/HOL formalization and its proof are available at
#link(
  "https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis",
)[`github.com/ManuelLerchner/Voblint-Verification-Master-Thesis`]
and archived on Zenodo @voblint.

=== Voblint from the user's side <sec:intro-answers>

A user states a check as `__voblint_check(e)`, and Voblint answers it with one
of four verdicts. It reports #verdict("PROVED") if $e$ holds whenever an
execution reaches the check, #verdict("REFUTED") if $e$ fails whenever an
execution reaches it, #verdict("DEAD") if no execution reaches it, and
#verdict("UNKNOWN") if the analysis cannot decide. Voblint also warns at every
division and remainder where it cannot rule out a zero divisor. @fig:intro-answers shows these answers in the playground. The _definite_
verdicts, #verdict("PROVED") and #verdict("REFUTED"), say nothing about whether
the check is reached, and only #verdict("DEAD") makes such a claim. A
#verdict("REFUTED") check is therefore a real error only if some execution
reaches it, which Voblint does not prove.

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
    shows it, with intervals and one calling context for all calls. The analysis
    covers every value of `t` at once. The screenshot opens the run in the
    playground. The program is the regression test
    #fixture("24-site-figures/precision/48-clamp_every_answer.vimp").],
) <fig:intro-answers>

=== The soundness chain <sec:intro-chain>

Each guarantee in @fig:intro-answers follows from a chain of inclusions
between sets of stores at the program point of the check (@fig:intro-nest).
The chain leads from the stores that source executions reach to the stores in
which the verdicts of the analyzer's _report_ hold. Each step may add stores
that no execution reaches, which costs precision, but it must not lose a
reachable store. A compiler that drops an edge would lose such a store, and so
would an analysis that lets a return from a procedure continue at the wrong
caller. The proof excludes both errors.

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
so far only described on paper or implemented as code in existing analyzers.
The formalization makes
five contributions.

- _End-to-end soundness._ The theorem connects the obligations of single
  operations to the tool the user runs. Whenever the analysis function
  #isaconst("run_voblint") returns a report, its definite verdicts
  (#verdict("PROVED") and #verdict("REFUTED")) hold for every source execution
  from an initial store with zeroed globals that reaches the corresponding
  program point, under every analysis configuration the function offers
  (#isathm("run_voblint_source_sound"), @sec:headline). Companion theorems
  justify #verdict("DEAD") and the absence of arithmetic warnings
  (@ch:results).
- _A concrete semantics of calling contexts._ Activation traces record how each activation
  was called. They give the per-context states of an analysis a concrete
  counterpart, because the chain of calling activations determines the
  contexts of a call. Splitting the concrete
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
  soundness theorem is about.
- _Needed assumptions and nonempty results._ The kernel cannot tell whether a
  theorem assumes too much or concludes too little. Further theorems therefore
  show that the analyzer gives definite verdicts on concrete programs
  (@sec:nonvacuity). Beyond these proofs, a regression corpus of
  #stat("corpus.cases") VIMP programs pins the expected verdict of every check,
  and example programs show what each mechanism gains in precision
  (@sec:eval-corpus, @sec:eval-precision).

== Scope of the soundness theorem <sec:intro-scope>

_End-to-end_ means that the proof reaches from source executions under
#isaconst("pstep") to the result of the analysis function. @fig:intro-trust
shows where it starts and where it stops.

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

The proved part begins at the abstract syntax tree and ends at the report that
the analysis function returns. Around it, the command-line tool and the
playground use handwritten code that is tested but not proved. This code only
converts between representations. A lexer and a parser turn the source text
into a syntax tree, and printing code turns the report into text, or into JSON
from which the playground draws the graph and marks the verdicts. The analysis
itself, from the syntax tree to the report, runs in code generated from the
proved function (@sec:ocaml-boundary). The only exception is a hook through
which a traced run records the solver's steps for the replay
(@sec:tracing). A bug in the parser or the printing code can thus misread a program or
misdisplay a verdict, but it cannot change what the analysis computes for the
syntax tree it receives. All components, proved or not, rest on a _trusted
foundation_, which consists of the Isabelle kernel, the code generator with its
target mappings, and the toolchains that compile and run the generated code.
The theorem is a partial-correctness result, since termination of the solve is
a premise for each program (@sec:certificate).

== Structure of the proof <sec:roadmap>

The proof follows the layers of the analyzer, and @fig:metro draws how it is
assembled. Where lines meet, a theorem combines
their results. The semantics and compiler lines relate
source executions to the control-flow graph. The domain and framework lines
show that the analyzer's states cover the stores that reach each node in each
context. The solver line shows that the solver's result satisfies the
equations. The result line combines these facts into the verdict guarantees of
@sec:intro-answers (#isathm("run_voblint_source_sound"), @ch:results).

#figure(
  image("/shared/generated/svg/metro.svg", width: 100%),
  placement: none,
  caption: [A map of the proof without its interior definitions. On the
    #link(site("index.html#proof-map"))[project site], every station links to
    its theory. Each line groups the results of one layer:
    #metro-line(metro.sem)[Semantics] (source and trace semantics),
    #metro-line(metro.comp)[Compiler] (compilation and its simulation),
    #metro-line(metro.dom)[Domain] (domain proofs and cooperating analyses),
    #metro-line(metro.fw)[Framework] (analysis contract, routing, coverage),
    #metro-line(metro.sol)[Solver] (the verified TD solver), and
    #metro-line(metro.res)[Result] (from the solved equations to the verdicts).],
) <fig:metro>

The proof map selects the results that connect the semantic layers.
@fig:intro-corpus shows the surrounding formal development as a treemap of
exported Isabelle entities, grouped by session and theory. The area of a block
measures its share of the exported corpus, not the difficulty of its proofs.

#figure(
  link(site("proof-map.html?view=treemap"), image("/assets/proof-map-treemap.png", width: 75%)),
  placement: none,
  caption: [The formalization's exported declarations, captured from the
    #link(site("proof-map.html?view=treemap"))[interactive treemap].
    Blocks group sessions and theories; their areas follow entity counts.
    Colors identify session dependency layers. The theories of this work span
    #stat("isabelle.lines") lines in #stat("isabelle.theories") files, without
    the vendored TD solver.],
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
