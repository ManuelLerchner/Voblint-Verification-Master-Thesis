#import "@preview/cetz:0.5.2"
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/sources.typ": proved
#import "../lib/theme.typ": vb
#import "../lib/math.typ": ctor, sem
#import "../lib/figures.typ": check-row, snapshot-var
#import "../lib/claims.typ": claim-snapshot, snapshot-cluster-of, snapshot-verdict

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

= The Source-Level Soundness Theorem <ch:results>

This chapter answers what the analyzer's output guarantees about the
executions of the source program. The solver of @ch:solving returns a valuation
of the unknowns it solved, each a pair of a CFG node and a context, and the
previous chapters show that this valuation covers every execution: the compiler
simulation, the trace semantics, equation soundness and the solver certificate,
on a set of solved unknowns that contains every unknown an execution visits
(@sec:cert-forward). The
client reads neither the valuation nor its contexts. It reads the report the
analyzer returns: one state per node and context, and one verdict per check.
A verdict needs a precise meaning, since a check that no execution reaches
makes every condition true there. @sec:chain assembles the pieces at one check,
@sec:headline states the theorem about the exported analyzer
#isaconst("run_voblint") that they must yield, and @sec:verdicts relates the
report and its verdicts to the solver's valuation.

== The chain at one check <sec:chain>

The argument that a verdict is sound places a reached store at a CFG node $v$,
follows a chain of inclusions between sets of stores there, and ends in one
implication. Each step is a theorem:
// One relation per row, centred over the fact that proves it, so the relations
// line up whatever the length of the fact's name.
#let _step(rel, fact) = stack(dir: ttb, spacing: 2pt, align(center, $#rel$), align(
  center,
  text(size: 7pt, fact),
))
#align(center, grid(
  columns: (auto, auto, auto),
  column-gutter: 8pt,
  row-gutter: 6pt,
  align: (right + horizon, center + horizon, left + horizon),
  [a store $s$ a source run reaches \ #text(size: 8pt)[at some $v$ simulating the run]],
  _step(sym.in, isathm("source_reaches_node_collect")),
  isai("\<C>\<^bsub>\<G>,g,S\<^esub> v"),

  [],
  _step($=$, isathm("node_collect_eq_Union_activation_collect")),
  $union.big_c #isai("\<A>\<^bsub>\<G>,R,c₀,g,S\<^esub> v c")$,

  [],
  _step(sym.subset.eq, isathm("run_voblint_covers")),
  isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"),

  [],
  _step(sym.subset.eq, isathm("analysis_report_verdicts_sound")),
  isai("\<V>\<^bsub>res\<^esub> v"),
))
The first step places a store that a finite source run reaches: it lies in the
node collecting semantics at some node $v$ that simulates the run's
execution configuration. The node is existential because the simulation is structural,
not a function: the same residual command may match several compiled nodes, for
instance in an uncalled procedure with the same body, and membership in
#isai("\<C>\<^bsub>\<G>,g,S\<^esub> v") selects a node the run reaches. The node
collecting semantics #isaconst("node_collect") splits into the activation
collecting semantics #isaconst("activation_collect") of the contexts the
policy's relation $R$ admits, with `main` in the initial context
#isai("c\<^sub>0") (@sec:contexts). The report $"res"$ holds one state at $v$
for every context the solver reached $v$ in, and
#isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>") (#isaconst("report_sem")) is the
set of stores these states describe, $sem(dot)$ of each, empty for the
unreachable state #ctor("Bot"). #isai("\<V>\<^bsub>res\<^esub> v")
(#isaconst("verdict_stores")) is the set of stores in which every definite
verdict the report gives at $v$ holds. The third step needs the run that built
the report and bounds each context separately, $c$ by $c$; the fourth follows
from the report alone, whose verdicts combine its per-context states
(@sec:verdicts). Each later set may contain stores that no execution reaches.
Soundness requires only that it contains the set before it.

The program below calls `f` twice. The first call passes $1$; the second
passes an input $x$ with $1 <= x <= 3$, if the input is in that range. So `m` is
$2$, $4$ or $6$ at the checks: `m >= 2` holds in every run, and `m == 2` holds
in some runs and fails in others.

#listing(lang: "c", claim: "chain-split-entry", ```
fun f(n) {
  m = 2 * n;
  __voblint_check(m >= 2);
  __voblint_check(m == 2);
  return m;
}

fun main() {
  a = f(1);
  x = __voblint_nondet_int();
  if (0 < x) {
    if (x < 4) {
      b = f(x);
    }
  }
}
```)

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
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    // m runs along x; one row per set, each contained in the rows below it.
    let (lo, hi, u) = (-1, 8, 0.72)
    let X(m) = (m - lo) * u
    let (r1, r2) = (_range(_m1), _range(_m2))
    let rows = (
      ([#isai("\<A>") $v$ #raw(_ctx("f_pp1_ctx0"))], "dots", (2,), vb.called),
      ([#isai("\<A>") $v$ #raw(_ctx("f_pp1_ctx1"))], "dots", (2, 4, 6), vb.called),
      ([$#isai("\<C>") v = union.big_c #isai("\<A>") v c$, reached], "dots", (2, 4, 6), vb.proved),
      (
        [#isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"), the report],
        "bar",
        (calc.min(r1.at(0), r2.at(0)), calc.max(r1.at(1), r2.at(1))),
        vb.accent,
      ),
      ([#isai("\<V>\<^bsub>res\<^esub> v"), verdict #raw(_vge)], "from", 2, vb.neutral),
    )
    for (k, (name, kind, vals, col)) in rows.enumerate() {
      let y = -0.55 * k
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
        // Every m from `vals` upwards: the set is unbounded.
        line((X(vals), y), (X(hi), y), stroke: 3.2pt + col.lighten(60%), mark: (
          end: ">",
          fill: col.lighten(60%),
        ))
        circle((X(vals), y), radius: 0.09, fill: col, stroke: none)
      }
    }
    let ya = -0.55 * rows.len() + 0.05
    for m in range(lo + 1, hi) {
      line((X(m), ya + 0.08), (X(m), ya - 0.04), stroke: 0.4pt + vb.muted)
      content((X(m), ya - 0.22), text(size: 7pt)[$#m$])
    }
    content((X(hi) + 0.2, ya - 0.22), text(size: 7pt)[$m$], anchor: "west")
  }),
  caption: [The chain at the check `m >= 2` of the program above, projected on
    the value of $m$, with Interval and entry-state contexts. Each row is a set
    of stores and lies inside the rows below it. Runs reach $m in {2, 4, 6}$,
    in two overlapping contexts. The report admits every $m$ in $[2, 6]$, also
    $3$ and $5$, which no run has. The verdict #raw(_vge) holds exactly of the
    stores with $m >= 2$, an unbounded set. The report and verdict are analyzer
    output (claim `chain-split-entry`); the first three rows are derived by
    hand.],
  kind: image,
  placement: none,
) <fig:chain>

@fig:chain draws the chain at the check `m >= 2`. `f` is analyzed in two
contexts, one per entry state, and in both the check holds for every admitted
store, so the verdict is #raw(_vge). The check `m == 2` on the next line sees
the same sets, but there the contexts disagree. The first call enters with
$n = 1$, and in its context the check holds for every admitted store:
#raw(_v1). The second call enters with
$n in {1, 2, 3}$, abstracted to the interval $[1, 3]$. Its state
#raw(_m2) admits the odd values $3$ and $5$, which no run has, and the check is
#raw(_v2) there, as it must be, since the runs with $x = 2$ and $x = 3$ violate
it. The store with $m = 2$ lies in both contexts' sets, so the sets cover the
node collecting semantics without partitioning it. The theorem only says that
each reached store is covered in some context, so the node verdict may claim
only what both contexts claim: #raw(_vnode). Without contexts the one entry of
`f` widens, and the check is #raw(_none.at(3)) at #raw(_none.at(4)) (claim
`chain-split-none`). Precision differs between the policies; every inclusion
holds under both.

The first link is the compiler simulation of @ch:program-model composed with
the trace construction of @ch:traces. The split of the node collecting semantics by
context rests on #oblig("TOTAL"): every covered call reaches some context.
Equation soundness (@ch:equations) bounds the activation collecting semantics
of each context by the solver's valuation, given the certificate of
@ch:solving, and the report lists that valuation's states. What the chain
should deliver to a client is this: every store a finite source run reaches is
described by the report at a node that simulates the run, in some context, and
every definite verdict listed there holds of the store.

== The source-level theorem <sec:headline>

One theorem establishes this for the exported analyzer. Its parameters are
the analysis configuration and the program, the arguments of #isaconst("run_voblint")
(@sec:codegen). An analysis configuration #isatype("analysis_config") bundles four
choices:
- $"as"$, a list of #isatype("analysis_domain") values, the analyses that run
  together as the combined component of @ch:cooperation, for example
  [#ctor("Interval_Analysis")] or [#ctor("Interval_Analysis"), #ctor("Order_Analysis")];
- $"rule"$, a #isatype("globals_rule"), the update rule for the solver's global
  unknowns, for example #ctor("Globals_Warrow")\;
- $"ctx"$, a #isatype("context_mode"), the context policy: #ctor("Ctx_None"),
  #ctor("Ctx_EntryState") or #ctor("Ctx_CallString") $k$;
- $"pg"$, a #isatype("program_globals"), the placement of program globals: in
  the flow-sensitive local state (#ctor("Program_Globals_Flow_Sensitive")) or
  each at a flow-insensitive global unknown of its own
  (#ctor("Program_Globals_Flow_Insensitive"), @sec:mixed-flow);
and the program $p$ is an #isatype("imp_prog"). The run of @fig:chain is
#isaconst("run_voblint") (#ctor("Analysis_Config") [#ctor("Interval_Analysis")]
#ctor("Globals_Warrow") #ctor("Ctx_EntryState") #ctor("Program_Globals_Flow_Sensitive")) $p$. The variables are
universally quantified, so the theorem holds for every analysis configuration, without a
separate theorem per analysis or policy.
#proved("run_voblint_source_sound", note: [Source-level soundness of the
  analyzer.])

Here $cal(G)$ is the global-variable classifier #isaconst("declared_global") $p$,
#isai("\<Pi>") the procedure table #isaconst("prog_table") $p$, and $g$ the
compiled graph #isaconst("prog_cfg") $p$. The theorem assumes three premises:

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
    analyzer returned a report. It returns one only for a valid analysis configuration
    and a well-formed program, and only where its executable solver returned,
    so neither well-formedness nor termination is a separate premise.
]

From all three together, not from any one of them, it concludes that some node
$v$ of $g$ and some frame stack exist such that:

#[
  #set enum(numbering: n => "(S" + str(n) + ")")
  + the source configuration and the graph configuration $(v, s, "stk")$ are
    related by the simulation #isaconst("csim") of @sec:csim, so $v$ is the
    node at which the compiled program stands when the source run reaches $s$;
  + #isai("s \<in> \<C>\<^bsub>\<G>,g,S\<^esub> v"): the store is collected at that node;
  + #isai("s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"): some state the report
    holds at $v$, under one of its contexts, describes $s$;
  + #isai("s \<in> \<V>\<^bsub>res\<^esub> v"): every `PROVED` check listed at $v$
    holds in $s$, and every `REFUTED` check is false in $s$.
]

The last two conclusions are the chain of @sec:chain read at one store. The
chain itself is a theorem too, stated once for every context policy
(#isathm("run_voblint_spine")): a source run is represented by a valid activation
trace $t$ ending at $v$, the policy assigns $t$ a context $c$, and
$
  s in #isai("\<A>") (v, c) subset.eq union.big_(c') #isai("\<A>") (v, c') =
  #isai("\<C>") v subset.eq #isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>")
  subset.eq #isai("\<V>\<^bsub>res\<^esub> v").
$
It keeps the trace and its context rather than picking some bucket that
contains $s$. A policy supplies only two facts: every valid trace carries some
context, and the buckets together are the collecting semantics. The unit,
entry-state and call-string policies discharge them in one theorem each.

An analysed answer also fixes what kind of object the report is
(#isathm("run_voblint_report_contract")). It answers a valid analysis configuration
(#isaconst("valid_config")) and a well-formed program
(#isaconst("wf_program_compile_input_exec")), and it is the report for exactly
that analysis configuration and the program's compiled graph. Structurally it is well formed
(#isaconst("well_formed_report")): its context indices are in range, a
point has one row per context, and each row's checks and arithmetic obligations
are exactly those of its point, each with the verdict of the row's own state.
Semantically it is sound (#isaconst("sound_report")): its check verdicts agree
with its states (#isaconst("consistent_report")), its states cover the
collecting semantics, its diagnostics name every point where a divisor may be
zero, and its check column lists every check of the compiled program. The
theorems of this chapter are consequences of the second half; a renderer relies
on the first.

== Verdicts <sec:verdicts>

The analyzer prints one word per check: `PROVED`, `REFUTED`, `UNKNOWN` or
`DEAD`. The chain of @sec:chain guarantees less than a word might suggest. It
places each reached store in the report's states at its node, in _some_
context, and those states may admit stores that no run reaches. This section
states what each word may claim under that guarantee, and how the analyzer
computes it.

*What the four verdicts mean.* Each meaning holds for a report that
#isaconst("run_voblint") returned, (P3). The verdicts speak about _covered
executions_: finite source executions of `main` from an initial store in
#isaconst("cinit_stores"), stopped at any point.
- `PROVED`: whenever a covered execution reaches the check, the condition
  holds (#isathm("run_voblint_check_sound")).
- `REFUTED`: whenever a covered execution reaches the check, the condition
  fails (#isathm("run_voblint_check_sound")). This is not a verified
  counterexample. The state admits stores no run has, so a condition that
  fails at every admitted store does not show that any store is reached.
- `UNKNOWN`: the analysis decides neither.
- `DEAD`: no covered execution reaches the check's node
  (#isathm("run_voblint_dead_check_unreached")).
The first three constrain each store at the node and hold vacuously when there
is none. Only `DEAD` makes a claim about reachability.

*How a verdict is computed.* At each node the report holds one state per
context the solver solved there. A pair the solver never solved has no row,
which loses no execution (@sec:cert-forward). Each state gives its own verdict.
The state #ctor("Bot") describes no store and gives `DEAD`. Any other state
asks every active analysis for the truth value of the condition
(@sec:coop-examples): an exact $1$ gives `PROVED`, an exact $0$ gives
`REFUTED`, and anything else `UNKNOWN`. A definite answer holds in every store
the state describes. The node's verdict joins the verdicts of its contexts:
equal verdicts stay, different ones become `UNKNOWN`, and `DEAD` changes
nothing. The join is forced by the chain, which does not say which context
covers a reached store. In @fig:chain the store with $m = 4$ lies only in the
second context's set, so the first context's #raw(_v1) cannot speak for it, and
#raw(_v1) and #raw(_v2) join to #raw(_vnode). A node is therefore `DEAD`
exactly when every state the report holds there is #ctor("Bot").

In Isabelle, #isaconst("report_of") builds the report from the table of solved
unknowns, one row per context solved at a node
(#isathm("report_rows_report_of")), and each entry describes the same stores as
the solver's valuation (#isathm("gamma_reader_eq_lookup")).
#isaconst("classify_point") classifies each row, and #isaconst("answer_check")
reads the meet of the analyses' answers; #isathm("mcp_classify_proved") and
#isathm("mcp_classify_refuted") show the definite verdicts sound.
#isaconst("aggregate_verdicts") joins the rows in the order of
#isatype("contextual_verdict"), #isatype("check_result") lifted by #ctor("Dead")
as bottom, flat with #ctor("Check_Unknown") on top
(#isathm("well_formed_check_verdict")). The join ranges over finitely many
contexts, because a terminating solve returns finitely many unknowns
(#isathm("finite_stabl_solve"), @sec:cert-param).

#let _pu = check-row("verdicts-proved-unreachable", cond: "x > 0")
#let _pu-int = check-row("verdicts-proved-unreachable-int", cond: "x > 0")

*Truth and reachability are separate.* In the program below, $x = 3n$ is
never $1$ or $2$, so no run reaches the check. Interval cannot see this. It
keeps #raw(_pu.state) there, where `x > 0` holds, and reports
#raw(_pu.verdict). The verdict is sound, since it only claims that `x > 0`
holds whenever a run reaches the check. Int also tracks
$x equiv 0 med (mod 3)$, finds the state empty, and reports
#raw(_pu-int.verdict).

#listing(lang: "c", claim: "verdicts-proved-unreachable", ```
fun main() {
  n = __voblint_nondet_int();
  x = 3 * n;
  if (x > 0) {
    if (x < 3) {
      __voblint_check(x > 0);
    }
  }
}
```)

So an unreached check need not be `DEAD`. `DEAD` rests on an emptiness test,
which is _sound_ if every state it accepts describes no store and _exact_ if
it accepts exactly those states. The test on a single analysis's state is
exact (#isathm("exact_emptiness_is_empty_state")). On the combined state of
several analyses it is only sound: Interval may hold $x = 2$ and Parity $x$
odd, neither of them empty, while no store satisfies both
(#isathm("mcp_empty_v_not_exact")). `DEAD` on report points is therefore sound
and not exact (#isathm("sound_emptiness_DEAD"), #isathm("DEAD_not_exact"); the
second is shown on a constructed report, not on one a run is proved to return).
Conditions are evaluated in the VIMP semantics, so a verdict can also depend on
its convention for division by zero (@sec:vimp-vs-c).

*From check rows to source positions.* The theorems speak about the checks the
report lists, each at a CFG node. For a source run about to execute a check,
#isathm("run_voblint_check_sound") finds a listed check with the same label and
condition at a node where the store is collected, and that check's verdict
holds of the store. The label is the check's source position, written by the
trusted parser. #isathm("run_voblint_labelled_check_sound") additionally
assumes that the labels of a report are distinct. The command-line tool checks
this condition and refuses to print a result when it fails. Under this
assumption, every row carrying a source label belongs to the check written at
that position. Because the listed check is found existentially, the statement
cannot be read backwards to show that a `DEAD` node is unreached.
#isathm("run_voblint_dead_check_unreached") proves that conclusion directly: a
store collected at the node would satisfy the node's claim, and a `DEAD` claim
admits none.

*Arithmetic diagnostics.* Diagnostics are stated per node as well. By
#isathm("run_voblint_arithmetic_safe"), a node without a diagnostic has nonzero
divisors in every collected store. A warning means only that the analysis
could not exclude a zero divisor.

Three features of the theorem are forced. The node is existential because a
source configuration does not determine its CFG node (@ch:traces), the context
because a store is covered in some context only, and coverage of the solved
unknowns is absent because it is derived (@sec:cert-forward). Termination is not
a premise: #isaconst("run_voblint") returns a report only where its executable
solver returned, and where the solve diverges there is no report and no claim.
Termination is not proved for every program (@sec:termination), so the theorem
is a partial-correctness result, and the analyzed program need not terminate. #isathm("certificate_demo_source_certified") discharges every
premise by evaluation for one program and analysis configuration, a non-vacuity witness.
@ch:instances compares what the shipped domains can prove under the theorem,
and @ch:executable draws the boundary between #isaconst("run_voblint") and the
delivered tool.
