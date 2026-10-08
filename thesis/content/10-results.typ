#import "@preview/cetz:0.5.2"
#import "../lib/code.typ": (
  claim-playground-link, isaconst, isai, isalocale, isathm, isatype, listing, oblig,
  playground-base,
)
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": theorem
#import "../lib/theme.typ": vb
#import "../lib/math.typ": ctor, sem, setcomp
#import "../lib/figures.typ": check-row, snapshot-var, verdict
#import "../lib/claims.typ": claim-ref, claim-snapshot, snapshot-cluster-of, snapshot-verdict

// One check row of a registered CLI claim (shared/claims.toml), so a verdict
// or state drawn in a figure is read from checked output rather than typed.
#let cli-row(name, cond) = {
  let cells = read("/shared/generated/" + name + ".txt")
    .split("\n")
    .map(l => l.trim().split(regex("\s{2,}")))
    .find(c => c.len() == 5 and c.at(2) == cond)
  assert(cells != none, message: "claim " + name + " has no check " + cond)
  cells
}

= What a Report Guarantees <ch:results>

This chapter answers what the analyzer's output guarantees about the
executions of the source program. Solving the equation system of
@ch:equations with the solver of @ch:solving yields an abstract state for
every pair of a CFG node and a context the solver reached, and a value for
every global unknown. These states cover every execution
(@sec:cert-forward). The analyzer turns them into a report. It keeps the
states and uses them to judge every `__voblint_check` and every arithmetic
safety condition, such as a nonzero divisor. The chapter defines the report
and its verdicts, follows the chain of inclusions from a source execution to a
verdict, and states the theorem that composes the chain for the analyzer.

== From solution to report <sec:report>

The constructions of the previous chapters are packaged behind one HOL
function, #isaconst("run_voblint"). It takes an analysis configuration and a
VIMP program. The configuration
(#isatype("analysis_config")) packages the choices of the earlier chapters:
the analyses that run together (@ch:cooperation), the update rule
(@sec:update-rules), the context policy (@sec:eq-routing), and the placement
of program globals (@sec:mixed-flow). The analyzer compiles the program to its
graph #isaconst("prog_cfg") $p$ (@ch:program-model), builds the equation system of the configured analyses and
context policy (@ch:equations), solves it from the exit of `main`
(@ch:solving), and builds a report from the solution.

#thy("run_voblint")

Before it analyzes anything, #isaconst("run_voblint") tests its two inputs.
#isaconst("valid_config") requires a nonempty list of distinct analyses, and
#isaconst("wf_program_compile_input_exec") decides the structural conditions
under which the compilation theorems of @ch:program-model hold. Only inputs
that pass both are compiled and solved. An answer #ctor("Analysed") $"res"$
therefore implies both conditions (#isathm("run_voblint_report_contract")),
and the executable test implies the well-formedness premise of the soundness
proofs (#isathm("wf_program_compile_input_exec_sound"),
#isathm("run_voblint_wf")). The source-level theorem of
@sec:headline consequently needs no premise about the configuration or the
program. An input that fails a test is answered with
#isaconst("Invalid_Activation") or #isaconst("Malformed_Program"), and
#isaconst("No_Answer") represents the case in which the solver produces no
result.

#isaconst("Analysed") carries an #isatype("analysis_report"). Three parts of
the report are relevant to the guarantees of this chapter. The first holds the abstract
states, each filed under the CFG node and the context the solver solved it
for. The second assigns every check of the program a verdict (@sec:verdicts).
The third lists the arithmetic diagnostics (@sec:verdict-meaning). The report
also holds the values of the global unknowns.

The solver may analyze a procedure several times, once for each context
(@sec:eq-routing), so a CFG node can carry several states. A user asks about
the CFG, so the report has to aggregate these states back onto its nodes. The
#link(playground-base)[playground] draws both pictures for the program of
@fig:chain. Its
#link(claim-playground-link("chain-split-entry", graph: "analysis"))[Analysis
  view] shows one node per pair of a program point and a context. Its
#link(claim-playground-link("chain-split-entry"))[Control-flow view] shows
each node of the compiled CFG once and groups the states of its contexts
there. The report states its guarantee in the control-flow picture.
#isai("report_states_at res v") collects the states the report files under
$v$, one per context the solver solved $v$ in. A state $d$ describes the
stores #isai("\<gamma>\<^bsub>res\<^esub> d"): the concretization of the
configured analyses (#isaconst("mcp_gamma_v")), lifted so that the unreachable
state #ctor("Bot") describes none (#isaconst("report_conc")). At $v$ the report
describes the stores that one of its states there describes, a set with a
constant of its own, #isaconst("report_sem"):
$
  #isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>") = union.big_(d in #isai("report_states_at res v")) #isai("\<gamma>\<^bsub>res\<^esub> d").
$

The union forgets the contexts on purpose. A source execution that reaches a
point does not come with a context. Which contexts exist depends on the
context policy the user selects: with call strings, contexts distinguish
bounded call histories; with entry states, distinct abstract entry states;
without contexts, there is a single one. A guarantee about the stores at a CFG node has
the same form whichever policy produced the states, so one theorem covers
every policy (@sec:headline). Each per-context state does over-approximate the
activation collecting semantics of its context (@sec:cert-forward). The
report's guarantees and its verdicts, however, are stated only through the
union #isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"). The per-context
states remain in the report as data, which the Analysis view displays.

== Verdicts <sec:verdicts>

The command-line tool prints the report through its checks: each check at $v$
receives one of four verdicts, #verdict("PROVED"), #verdict("REFUTED"),
#verdict("UNKNOWN") or #verdict("DEAD"). The
#link(playground-base)[browser playground] shows the same verdicts beside the
graph, the state of every node and context, and a replay of the solve
(@sec:ocaml-boundary, @sec:tracing). The text report lists verdicts by source
position: each check carries its position as a label, written by the trusted
parser, and when the labels are distinct, which the text report checks before
printing, every verdict belongs to the check at its position
(#isathm("run_voblint_labelled_check_sound")).

*How a verdict is computed.* Each state $d$ in
#isai("report_states_at res v") gives its own verdict for a check:

#thy("classify_point")

The state #ctor("Bot") gives #verdict("DEAD"). Any other state is classified
by #isaconst("mcp_classify"), which asks every active analysis for the truth
value of the check's condition through the query system of @sec:coop-queries and combines the
answers by meet: an exact $1$ gives #verdict("PROVED"), an exact $0$ gives
#verdict("REFUTED"), and anything else #verdict("UNKNOWN"). A definite answer
holds in every store the state describes (#isathm("mcp_classify_proved"),
#isathm("mcp_classify_refuted")).

The verdict of the CFG node joins the per-context verdicts of its states
(#isaconst("aggregate_verdicts")). If every state other than #ctor("Bot")
gives #verdict("PROVED"), the node is #verdict("PROVED"); if every such state
gives #verdict("REFUTED"), it is #verdict("REFUTED"). If the states disagree,
or one of them gives #verdict("UNKNOWN"), the node is #verdict("UNKNOWN").
States classified #verdict("DEAD"), the #ctor("Bot") states, are neutral in
this aggregation, so a node at which the report holds no state, or only
#ctor("Bot") states, is #verdict("DEAD"). The report holds finitely many
states at each node, those of the finitely many unknowns a terminating solve
stabilizes (#isathm("finite_stabl_solve")).

*What a verdict claims about stores.* The chain of @sec:chain has to end in
what an end user reads: the verdicts, not the states. To state that
the verdicts are correct as an inclusion of sets, we turn the verdicts at $v$
into the set of stores consistent with them, the _verdict set_
#isai("\<V>\<^bsub>res\<^esub> v"). If $v$ carries the check `x > 0` with
verdict #verdict("PROVED"), the verdict set is $setcomp(s, s(x) > 0)$: the verdict
tells the user that $x$ is positive there and nothing else.
#verdict("REFUTED") gives the stores in which the condition fails, and
#verdict("UNKNOWN") every store:

#thy("verdict_holds")

A #verdict("DEAD") check claims only that no store arrives at $v$, a
reachability claim that @sec:verdict-meaning states separately. In this
store-set interpretation it admits every store, the neutral element of the
intersection below:

#thy("check_stores")

A store is consistent with the verdicts at $v$ if it satisfies the claim of
every check there:

#thy("verdict_stores")

By construction of #isaconst("compile"), each check has a node of its own, so
the intersection ranges over at most one check. Stated as an intersection, the
verdict set does not depend on how the compiler places checks.

The verdict set can be much larger than
#isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"), because a verdict keeps only
the truth value of one condition (last row of @fig:chain). Soundness needs
only that every store reaching $v$ lies in it.

If each node verdict is the join of its states' verdicts, the verdicts claim
no more than the states support:
#isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> \<V>\<^bsub>res\<^esub> v")
(#isathm("analysis_report_verdicts_sound")), and every report
#isaconst("run_voblint") returns is built this way
(#isathm("run_voblint_consistent")).

== The chain at one check <sec:chain>

Let $"res"$ be a report #isaconst("run_voblint") returns for a program $p$,
$g$ = #isaconst("prog_cfg") $p$ its compiled graph, $cal(G)$ =
#isaconst("declared_global") $p$ its global-variable classifier, and $S$ =
#isaconst("cinit_stores") $cal(G)$ its initial-store set (@sec:vimp-vs-c,
@ch:traces). The
argument that a verdict is sound places a reached store at a CFG node $v$ and
follows a chain of inclusions between sets of stores there. It ends in the
two sets of the report, #isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>") and
#isai("\<V>\<^bsub>res\<^esub> v"). Each step is a theorem:
// One relation per row, centred over the fact that proves it, so the relations
// line up whatever the length of the fact's name.
#let _step(rel, fact) = stack(dir: ttb, spacing: 2pt, align(center, $#rel$), align(
  center,
  text(size: 7pt, fact),
))
#block(breakable: false, above: 1.6em, below: 1.6em, align(center, grid(
  columns: (auto, auto, auto),
  column-gutter: 10pt,
  row-gutter: 8pt,
  align: (right + horizon, center + horizon, left + horizon),
  [a store $s$ a source run reaches, \ at a node $v$ simulating the run],
  _step(sym.in, isathm("source_reaches_node_collect")),
  isai("\<C>\<^bsub>\<G>,g,S\<^esub> v"),

  [],
  _step($=$, isathm("node_collect_eq_Union_activation_collect")),
  $union.big_c #isai("\<A>\<^bsub>\<G>,adm,c₀,g,S\<^esub> v c")$,

  [],
  _step(sym.subset.eq, isathm("run_voblint_covers")),
  isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"),

  [],
  _step(sym.subset.eq, isathm("analysis_report_verdicts_sound")),
  isai("\<V>\<^bsub>res\<^esub> v"),
)))
The first step places a store that a finite source run reaches: it lies in the
node collecting semantics at some node $v$ that simulates the run's
execution configuration (the node need not be unique, @sec:csim). The second step holds for a policy with a cover that meets all
five obligations of @ch:traces: #isaconst("node_collect") is the
union of #isaconst("activation_collect") over the contexts #isai("adm")
admits, with `main` in #isai("c\<^sub>0") (@sec:contexts). It shows where
contexts enter; the source-level theorem goes from #isai("\<C>") directly to
the report. The third inclusion is the analyzer's soundness result. It bounds
the stores collected at $v$, over all contexts, by the union of the report's
states at $v$, without saying which state covers a given store. The fourth is
the inclusion of @sec:verdicts and depends only on the report and its
consistency.

The program of @fig:chain calls `f` twice. The first call passes $1$; the
second passes an input $x$ with $1 <= x <= 3$, if the input is in that range.
So `m` is $2$, $4$ or $6$ at the checks: `m >= 2` always holds, and `m == 2`
holds at the first call and fails at the second call when $x$ is $2$ or $3$.

#let _snap = claim-snapshot("chain-split-entry")
#let _ctx(node) = snapshot-cluster-of(_snap, node).ctx
#let _range(state) = {
  let m = state.match(regex("\[(-?\d+),(-?\d+)\]"))
  assert(m != none, message: "unexpected state " + state)
  (int(m.captures.at(0)), int(m.captures.at(1)))
}
#let _m1 = snapshot-var("chain-split-entry", "f_pp1_ctx0", "m")
#let _m2 = snapshot-var("chain-split-entry", "f_pp1_ctx1", "m")
#let _v1 = upper(_snap.nodes.at("f_pp2_ctx0").status)
#let _v2 = upper(_snap.nodes.at("f_pp2_ctx1").status)
#let _vnode = snapshot-verdict(_snap, "m == 2")
#let _vge = snapshot-verdict(_snap, "m >= 2")
#let _none = cli-row("chain-split-none", "m == 2")

#figure(
  {
    show raw.where(block: true): set text(size: 6.2pt)
    let code = listing(
      lang: "c",
      claim: "chain-split-entry",
      highlights: ((line: 3, start: 3, end: none, fill: vb.accent, tag: [$v$]),),
      ```
      fun f(n) {
        m = 2 * n;
        __voblint_check(m >= 2);
        __voblint_check(m == 2);
        return m;
      }

      fun main() {
        a = f(1);
        x = __voblint_nondet_int();
        if (0 < x && x < 4) {
          b = f(x);
        }
      }
      ```,
    )
    let chain = cetz.canvas(length: 1cm, {
      import cetz.draw: *
      // m runs along x; one row per set, each contained in the rows below it.
      let (lo, hi, u) = (-1, 8, 0.45)
      let X(m) = (m - lo) * u
      let (r1, r2) = (_range(_m1), _range(_m2))
      let rows = (
        ([#isai("\<A>") $v$ #raw(_ctx("f_pp1_ctx0"))], "dots", (2,), vb.called),
        ([#isai("\<A>") $v$ #raw(_ctx("f_pp1_ctx1"))], "dots", (2, 4, 6), vb.called),
        (
          [$#isai("\<C>") med v = union.big_c #isai("\<A>") med v med c$, reached],
          "dots",
          (2, 4, 6),
          vb.proved,
        ),
        (
          [#isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"), the report],
          "bar",
          (calc.min(r1.at(0), r2.at(0)), calc.max(r1.at(1), r2.at(1))),
          vb.accent,
        ),
        ([#isai("\<V>\<^bsub>res\<^esub> v"), verdict #verdict(_vge)], "from", 2, vb.neutral),
      )
      for (k, (name, kind, vals, col)) in rows.enumerate() {
        let y = -0.75 * k
        content((-0.3, y), text(size: 7.5pt, name), anchor: "east")
        line((X(lo), y), (X(hi), y), stroke: 0.3pt + vb.frame)
        if kind == "dots" {
          for m in vals { circle((X(m), y), radius: 0.09, fill: col, stroke: none) }
        } else if kind == "bar" {
          line((X(vals.at(0)), y), (X(vals.at(1)), y), stroke: 3.2pt + col.lighten(30%))
          for m in range(vals.at(0), vals.at(1) + 1) {
            circle((X(m), y), radius: 0.09, fill: col, stroke: none)
          }
        } else {
          // Every integer m from `vals` upwards; the arrow marks the unbounded rest.
          line((X(vals), y), (X(hi), y), stroke: 3.2pt + col.lighten(60%), mark: (
            end: ">",
            fill: col.lighten(60%),
          ))
          for m in range(vals, hi) { circle((X(m), y), radius: 0.09, fill: col, stroke: none) }
        }
      }
      let ya = -0.75 * rows.len() + 0.2
      for m in range(lo + 1, hi) {
        line((X(m), ya + 0.08), (X(m), ya - 0.04), stroke: 0.4pt + vb.muted)
        content((X(m), ya - 0.22), text(size: 7pt)[$#m$])
      }
      content((X(hi) + 0.2, ya - 0.22), text(size: 7pt)[$m$], anchor: "west")
    })
    grid(
      columns: (38%, 1fr),
      column-gutter: 8pt,
      align: (left + horizon, right + horizon),
      code, chain,
    )
  },
  caption: [Left: the program. Right: the chain at the node $v$ of the check
    `m >= 2` (line 3), projected on $m$, with Interval and entry-state
    contexts. Each row is a set of stores. Both per-context rows lie inside the
    union row, and each later row lies inside the rows below it. The report
    admits $3$ and $5$, which no run reaches, and the verdict set of
    #verdict(_vge) is unbounded. The check `m == 2` (line 4) sees the same
    stores. Report and verdict are analyzer output (claim #claim-ref("chain-split-entry"));
    the first three rows are derived by hand.],
  kind: image,
  placement: none,
) <fig:chain>

`f` is analyzed in two contexts, one per entry state. The check `m >= 2`
holds for every admitted store in both, so its verdict is #verdict(_vge). The
check `m == 2` sees the same sets, but the contexts disagree. The first call
enters with $n = 1$, and the check is #verdict(_v1) there. The second enters
with $n in [1, 3]$; its state #raw(_m2) also admits $3$ and $5$, and the check
is #verdict(_v2), the only sound answer, since the run with $x = 1$ satisfies
it and the runs with $x = 2$ and $x = 3$ violate it.

The report does not say which
context covers a reached store, so the node verdict joins the context
verdicts: #verdict(_v1) and #verdict(_v2) give #verdict(_vnode). Without contexts, both calls feed the one seed of `f`, which
the warrowing update rule widens, and the check is #verdict(_none.at(3)) at
#raw(_none.at(4)) (claim #claim-ref("chain-split-none")). Every inclusion holds under both
policies.

== The source-level theorem <sec:headline>

One theorem states the chain at one store for the exported analyzer. It quantifies over an
arbitrary analysis configuration and program, the arguments of
#isaconst("run_voblint") (@sec:report), so no separate theorem is needed per
analysis or context policy: whenever the analyzer returns a report, every
store a finite source execution reaches is covered by that report and
satisfies its definite verdicts.
#theorem(name: [Source-level soundness of the analyzer], isa: "run_voblint_source_sound")[
  #proved("run_voblint_source_sound")
]

Here $cal(G)$ and $g$ are as in @sec:chain, and #isai("\<Pi>") is the procedure
table #isaconst("prog_table") $p$. The theorem assumes three premises:

#[
  #set enum(numbering: n => "(P" + str(n) + ")")
  + #isai("s0 \<in> cinit_stores \<G>"): the run starts from a store in
    #isaconst("cinit_stores"), the initial stores $S$ of @ch:traces, which zero
    every global and leave the locals unconstrained.
  + #isai("\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"):
    a finite #isaconst("pstep") execution of $p$ runs from the body of `main`
    to a configuration with store $s$. Any stopping point is allowed, so
    nonterminating programs are covered through their prefixes.
  + #isaconst("run_voblint") $"config"$ $p$ $=$ #ctor("Analysed") $"res"$: the
    analyzer returned a report. Input validity and solver termination are
    therefore not separate premises (@sec:report).
]

It concludes that some node $v$ of $g$ and frame stack $"stk"$ exist with:

#[
  #set enum(numbering: n => "(S" + str(n) + ")")
  + the source configuration and the graph configuration $(v, s, "stk")$ are
    related by the simulation #isaconst("csim") of @sec:csim, so $v$ is a node
    at which the compiled program can stand when the source run reaches $s$;
  + #isai("s \<in> \<C>\<^bsub>\<G>,g,S\<^esub> v"): the store is collected at that node;
  + #isai("s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"): some state the report
    holds at $v$, under one of its contexts, describes $s$;
  + #isai("s \<in> \<V>\<^bsub>res\<^esub> v"): every #verdict("PROVED") check listed at $v$
    holds in $s$, and every #verdict("REFUTED") check is false in $s$.
]

The last two conclusions are the chain of @sec:chain read at one store. The
statement mentions no activation and no context. Source executions carry
neither, and the report states its guarantee per CFG node (@sec:report), so
both appear only inside the proof, at the second inclusion of the chain.
#isathm("run_voblint_spine") keeps them visible: it states the chain once for
every context policy, together with the activation trace and the context that
cover the reached store, and each shipped policy discharges its two
assumptions.

== What a verdict says about executions <sec:verdict-meaning>

*What the four verdicts mean.* The report's states may describe stores that
no execution reaches, so a verdict claims only what holds for every store that
reaches the check. Each meaning holds for a report that
#isaconst("run_voblint") returned, (P3). The verdicts speak about _covered
executions_: finite source executions of `main` from an initial store in
#isaconst("cinit_stores"), stopped at any point.
- #verdict("PROVED"): whenever a covered execution reaches the check, the condition
  holds (#isathm("run_voblint_check_sound")).
- #verdict("REFUTED"): whenever a covered execution reaches the check, the condition
  fails (#isathm("run_voblint_check_sound")). It is not a verified
  counterexample: it establishes no reaching execution.
- #verdict("UNKNOWN"): the analysis decides neither.
- #verdict("DEAD"): no covered execution reaches the check: nothing is
  collected at its node (#isathm("run_voblint_dead_check_unreached")), and a
  reaching execution never finds #verdict("DEAD") (#isathm("run_voblint_check_sound")).
#verdict("PROVED") and #verdict("REFUTED") hold vacuously when no execution
reaches the check, and only #verdict("DEAD") claims anything about
reachability. The corresponding theorem for #verdict("PROVED") and #verdict("REFUTED") is:

#[
  #show raw.where(block: true): set text(size: 6.5pt)
  #proved("run_voblint_check_sound")
]

#let _pu = check-row("verdicts-proved-unreachable", cond: "x > 0")
#let _pu-int = check-row("verdicts-proved-unreachable-int", cond: "x > 0")

*Truth and reachability are separate.* In the program below, $x = 3n$ is
never $1$ or $2$, so no run reaches the check. Interval cannot see this. It
keeps #raw(_pu.state) there, where `x > 0` holds, and reports
#verdict(_pu.verdict). The verdict is sound: it claims `x > 0` only for runs
that reach the check. Int also tracks
$x equiv 0 med (mod 3)$, finds the state empty, and reports
#verdict(_pu-int.verdict).

#[
  #show raw.where(block: true): set text(size: 6.5pt)
  #listing(lang: "c", claim: "verdicts-proved-unreachable", ```
  fun main() {
    n = __voblint_nondet_int();
    x = 3 * n;
    if (0 < x && x < 3) {
      __voblint_check(x > 0);
    }
  }
  ```)
]

So an unreached check need not be #verdict("DEAD"). The analyzer reports
#verdict("DEAD") only where its emptiness test recognizes every state at the
node as describing no store. The test is sound
(#isathm("sound_emptiness_DEAD")) but not exact: two analyses can each admit
stores while no store satisfies both (#isathm("mcp_empty_v_not_exact"),
#isathm("DEAD_not_exact"), the latter on a constructed report).
An unreached check can thus miss #verdict("DEAD") for two reasons. Its state
may describe stores that no run reaches, as Interval's state above does, or it
may describe no store without the test recognizing this. Either way the state
is classified like any other, and the verdict is sound.

*Arithmetic diagnostics.* Division by zero needs no check in the program.
The analyzer treats the condition that a divisor is nonzero as an implicit
check at every division and remainder and classifies it with the same queries.
Where that condition is #verdict("PROVED") or the node #verdict("DEAD"), it
prints nothing. Otherwise it prints an error for #verdict("REFUTED") and a
warning for #verdict("UNKNOWN"). The guarantee concerns the silent nodes: at a
node without a diagnostic, every collected store has nonzero divisors
(#isathm("run_voblint_arithmetic_safe")). An error carries the dual
guarantee: whenever a covered execution reaches its node, the divisor is zero.

#proved("run_voblint_arithmetic_refuted")

A warning means only that the analysis could not exclude a zero divisor.
Neither an error nor a warning establishes that the node is reached.

The theorems constrain only definite verdicts and silent nodes, so they say
nothing about precision: an analyzer that answered #verdict("UNKNOWN") at every
check would satisfy them (#isathm("unknown_everywhere_sound")). How often the
analyzer does better is measured in @ch:evaluation, and @sec:falsification
shows that the theorems do reject an analyzer that claims too much.

The theorems are partial-correctness results: every report the analyzer
returns is sound, while termination is not guaranteed for every program
(@sec:termination). #isathm("certificate_demo_source_certified") discharges all
three premises for one concrete program, the third by evaluation, which relies
on code generation. The theorem is thus non-vacuous for an executable run.
