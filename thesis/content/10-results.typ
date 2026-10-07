#import "@preview/cetz:0.5.2"
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/sources.typ": proved
#import "../lib/theorems.typ": theorem
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

= What a Report Guarantees <ch:results>

This chapter answers what the analyzer's output guarantees about the
executions of the source program. The previous chapters show that the solver's
valuation, indexed by pairs of a CFG node and a context, covers every
execution (@sec:cert-forward). The
client reads neither the valuation nor its contexts. It reads the report the
analyzer returns: one state per node and context the solver solved, and one
verdict per check. What a verdict claims needs care: a claim about every store
that reaches a check is vacuously true at a check that no execution reaches,
whatever its condition.

== The chain at one check <sec:chain>

Let $"res"$ be the report #isaconst("run_voblint") returns for a program $p$,
$g$ = #isaconst("prog_cfg") $p$ its compiled graph, $cal(G)$ =
#isaconst("declared_global") $p$ its global-variable classifier, and $S$ =
#isaconst("cinit_stores") $cal(G)$ its initial stores (@ch:traces). The
argument that a verdict is sound places a reached store at a CFG node $v$ and
follows a chain of inclusions between sets of stores there. The chain ends
in two sets the report determines. #isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>")
is the set of stores the report's states at $v$ describe, and
#isai("\<V>\<^bsub>res\<^esub> v") is the set of stores in which every definite
verdict the report gives at $v$ holds. Each step is a theorem:
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
  $union.big_c #isai("\<A>\<^bsub>\<G>,adm,c₀,g,S\<^esub> v c")$,

  [],
  _step(sym.subset.eq, isathm("run_voblint_covers")),
  isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"),

  [],
  _step(sym.subset.eq, isathm("analysis_report_verdicts_sound")),
  isai("\<V>\<^bsub>res\<^esub> v"),
))
The first step places a store that a finite source run reaches: it lies in the
node collecting semantics at some node $v$ that simulates the run's
execution configuration (the node need not be unique, @sec:csim). The second step holds for a policy that meets the coverage
contract (#oblig("TOTAL") in particular): #isaconst("node_collect") is the
union of #isaconst("activation_collect") over the contexts $italic("adm")$
admits, with `main` in #isai("c\<^sub>0") (@sec:contexts). It shows where
contexts enter; the source-level theorem goes from #isai("\<C>") directly to
the report. The report $"res"$ holds one state at $v$
for every context the solver solved $v$ in, so
#isai("\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>") (#isaconst("report_sem")) is the
union of $sem(dot)$ over these states, and the unreachable state #ctor("Bot")
contributes nothing. #isai("\<V>\<^bsub>res\<^esub> v") is
#isaconst("verdict_stores"). The third inclusion is the analyzer's
soundness result. It bounds the stores collected at $v$, over all contexts, by
the union of the report's states at $v$, without saying which state covers a
given store. The fourth depends only on the report, whose
verdict at $v$ holds for every store any of its states there describes
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
#raw(_m2) also admits the odd values $3$ and $5$, which no run has. The check
is #raw(_v2) there, and a sound analysis can give nothing else in this
context: the run with $x = 1$ satisfies the check, and the runs with $x = 2$
and $x = 3$ violate it. Contexts need not partition the executions, and their sets may overlap:
the store with $m = 2$ lies in both. The theorem only says that
each reached store is covered in some context, so the node verdict may claim
only what both contexts claim: #raw(_vnode). Without contexts both calls contribute to the
one seed of `f`, which the warrowing update rule widens, and the check is #raw(_none.at(3)) at #raw(_none.at(4)) (claim
`chain-split-none`). Precision differs between the two policies, but every
inclusion holds under both.

Read at one store, the chain says that every store a finite source run reaches
is described by the report at a node simulating the run, and that every
definite verdict there holds of it.

== The source-level theorem <sec:headline>

One theorem establishes this for the exported analyzer. It quantifies over an
arbitrary analysis configuration and program, the arguments of
#isaconst("run_voblint") (@sec:codegen): whenever the analyzer returns a
report, every store a finite source execution reaches is covered by that
report and satisfies its definite verdicts.
#theorem(name: [Source-level soundness of the analyzer], isa: "run_voblint_source_sound")[
  #proved("run_voblint_source_sound")
]

The configuration (#isatype("analysis_config")) packages the choices of the
earlier chapters: the analyses that run together (@ch:cooperation), the update
rule (@sec:update-rules), the context policy (@sec:eq-routing), and the
placement of program globals (@sec:mixed-flow). No
separate theorem is needed for each analysis, context policy or other
configuration choice.

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
    analyzer returned a report. It returns one only for a valid configuration and a
    well-formed program, and only if its solver terminates, so neither is a
    separate premise.
]

From these premises it concludes that some node $v$ of $g$ and some frame
stack exist such that:

#[
  #set enum(numbering: n => "(S" + str(n) + ")")
  + the source configuration and the graph configuration $(v, s, "stk")$ are
    related by the simulation #isaconst("csim") of @sec:csim, so $v$ is a node
    at which the compiled program can stand when the source run reaches $s$;
  + #isai("s \<in> \<C>\<^bsub>\<G>,g,S\<^esub> v"): the store is collected at that node;
  + #isai("s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"): some state the report
    holds at $v$, under one of its contexts, describes $s$;
  + #isai("s \<in> \<V>\<^bsub>res\<^esub> v"): every `PROVED` check listed at $v$
    holds in $s$, and every `REFUTED` check is false in $s$.
]

The last two conclusions are the chain of @sec:chain read at one store.
#isathm("run_voblint_spine") states the chain once for every context policy,
and each shipped policy discharges its two assumptions.

== Verdicts <sec:verdicts>

The analyzer prints one word per check: `PROVED`, `REFUTED`, `UNKNOWN` or
`DEAD`. Each word has to be read against what the chain of @sec:chain
establishes. The chain bounds the reached stores from above: every store an
execution brings to a check lies in some state of the report there, but those
states may also describe stores that no execution reaches. A verdict computed
from the states can therefore claim only what holds for every store they
describe.

*What the four verdicts mean.* Each meaning holds for a report that
#isaconst("run_voblint") returned, (P3). The verdicts speak about _covered
executions_: finite source executions of `main` from an initial store in
#isaconst("cinit_stores"), stopped at any point.
- `PROVED`: whenever a covered execution reaches the check, the condition
  holds (#isathm("run_voblint_check_sound")).
- `REFUTED`: whenever a covered execution reaches the check, the condition
  fails (#isathm("run_voblint_check_sound")). This is not a verified
  counterexample, since the state may admit stores no run has.
- `UNKNOWN`: the analysis decides neither.
- `DEAD`: no covered execution reaches the check.
  #isathm("run_voblint_dead_check_unreached") shows that nothing is collected
  at its node, and #isathm("run_voblint_check_sound") that the row a reaching
  execution finds is never `DEAD`.
`PROVED` and `REFUTED` are claims about every store that reaches the check and
hold vacuously when none does. `UNKNOWN` makes no claim. Only `DEAD` makes a
claim about reachability. The theorem for
`PROVED` and `REFUTED` reads:

#proved("run_voblint_check_sound", note: [What a reported verdict guarantees.])

*How a verdict is computed.* At each node the report holds one state per
context the solver solved there. A pair the solver never solved has no row,
which loses no execution (@sec:cert-forward). Each state gives its own verdict.
The state #ctor("Bot") describes no store and gives `DEAD`. Any other state
asks every active analysis for the truth value of the condition through the
query system of @sec:coop-queries and combines the answers by meet: an exact $1$ gives `PROVED`, an exact $0$ gives
`REFUTED`, and anything else `UNKNOWN`. A definite answer holds in every store
the state describes. The node's verdict joins the verdicts of its contexts:
equal verdicts stay, different ones become `UNKNOWN`, and `DEAD` changes
nothing. The join is forced by the chain, which does not say which context
covers a reached store. In @fig:chain the store with $m = 4$ lies only in the
second context's set, so the first context's #raw(_v1) cannot speak for it, and
#raw(_v1) and #raw(_v2) join to #raw(_vnode). A node is therefore `DEAD`
exactly when every state the report holds there is #ctor("Bot"), including a
node at which it holds no state.

#isathm("mcp_classify_proved") and #isathm("mcp_classify_refuted") prove that a
definite verdict holds for every store its state describes. The join is finite
because a terminating solve stabilizes finitely many unknowns
(#isathm("finite_stabl_solve")).

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
it accepts exactly those states. The test on the state of a single non-relational analysis is
exact (#isathm("exact_emptiness_is_empty_state")). On the combined state of
several analyses it is only sound: Interval may hold $x = 2$ and Parity $x$
odd, neither of them empty, while no store satisfies both
(#isathm("mcp_empty_v_not_exact")). `DEAD` on report points is therefore sound
and not exact (#isathm("sound_emptiness_DEAD"), #isathm("DEAD_not_exact"); the
second is shown on a constructed report, not on one a run is proved to return).

*From checks to source positions.* The theorems speak about checks at CFG
nodes, while a user reads source positions. Each check carries a label, its
source position, which the trusted parser writes. If the labels of a report
are distinct, which the text
report checks before printing (the JSON output omits positions instead), every
verdict belongs to the check at its position
(#isathm("run_voblint_labelled_check_sound")).

*Arithmetic diagnostics.* Every division and remainder adds the condition that
its divisor is nonzero, and the analyzer classifies it like a check, through
the same queries. The tool prints a diagnostic where that condition is
neither `PROVED` nor `DEAD`: an error for `REFUTED`, a warning for `UNKNOWN`. By #isathm("run_voblint_arithmetic_safe"), a node without a warning
has nonzero divisors in every collected store. A warning means only that the
analysis could not exclude a zero divisor.

The theorems are partial-correctness results: every report the analyzer
returns is sound, while termination is not guaranteed for every program
(@sec:termination). #isathm("certificate_demo_source_certified") discharges all
three premises for one concrete program, the third by evaluation, which
trusts code generation.
