#import "@preview/cetz:0.5.2"
#import "../lib/code.typ": (
  claim-playground-link, isaconst, isai, isalocale, isathm, isatype, listing, oblig, thy-badge,
)
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": definition, theorem
#import "../lib/theme.typ": vb
#import "../lib/math.typ": absval, conc, ctor, sem, setcomp
#import "../lib/figures.typ": check-row, snapshot-var, verdict
#import "../lib/claims.typ": (
  claim-ref, claim-snapshot, claim-text, snapshot-cluster-of, snapshot-verdict,
)

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

= From Post-Solutions to Verdicts <ch:results>

@ch:solving ended with abstract states that describe every store an execution
brings to a node in a context (@sec:certificate). A user, however, is typically not
interested in abstract states. They want to know whether the checks they wrote
hold, whether a check can be reached at all, and whether an arithmetic
operation, such as a division by zero, can fail. This chapter defines how the analyzer derives these answers from the
abstract states, as verdicts and diagnostics in a report, and proves them
correct.

== The analyzer function and its report #thy-badge("Voblint_CLI", "Analysis_Run") <sec:report>

The analyzer is one HOL function, #isaconst("run_voblint"), that runs the
constructions of the previous chapters in order. It takes a VIMP program and a
configuration (#isatype("analysis_config")), which fixes the analyses that run
together (@ch:cooperation), the update rule
(@sec:update-rules), the context policy (@sec:eq-routing), and the placement of
program globals (@sec:mixed-flow). It compiles the program to its graph
(@ch:program-model), generates the equations (@ch:equations), solves them from
the exit of `main` (@ch:solving), and collects the solution into a report.

#thy("run_voblint")

The analyzer returns a report only for inputs that the proofs cover. Before
compiling, it
checks that the configuration selects a nonempty list of distinct analyses and
that the program is well formed in the sense of @ch:program-model. Invalid
inputs, and a solve that produces no result, receive an error instead of a
report (#isathm("run_voblint_report_contract"), #isathm("run_voblint_wf")). The
end-to-end theorem therefore needs no separate premise about its inputs.

The report (#isatype("analysis_report")) holds the solver's states with their
nodes and contexts, the values of the global unknowns, a verdict for every
check, and the arithmetic diagnostics. A user, however, asks what holds at a
point of the source program, whichever call led there, and a source execution
carries no context. The report therefore merges the contexts and returns to the
single control-flow graph of the program. At a node $v$, it describes every
store that one of its states at $v$ describes (#isaconst("report_sem")):
$
  cal(R)_("res")(v) = union.big_(d in #isaconst("report_states_at") ("res",v)) conc_("res")(d),
$
where #isaconst("report_states_at") collects the states at $v$ over all
contexts and $conc_("res")$ is the concretization of the configured analyses,
with $conc_("res")(ctor("Bot"))=emptyset$. The report still keeps
the states per context, because the coverage contract bounds each context
separately (@sec:contract).

== Check verdicts from the report <sec:verdicts>

Each check receives one of four verdicts, #verdict("PROVED"),
#verdict("REFUTED"), #verdict("UNKNOWN"), or #verdict("DEAD"), shown at the
check's source position.

The analyzer computes them as it computed the report's stores, first per
context and then folded back into the node of the program's control-flow
graph. For each context $c$ solved at $v$, it decides the check from the state
at $(v, c)$ (#isaconst("classify_point")). The state #ctor("Bot") describes no
store and gives #verdict("DEAD"). For any other state, the analyzer evaluates the
check's condition abstractly and asks the selected analyses which values it can
take there (@sec:coop-queries). A condition evaluates to $1$ when it holds and to
$0$ when it fails. If the only possible value is $1$, the check is
#verdict("PROVED"). If the only possible value is $0$, it is
#verdict("REFUTED"). Otherwise it is #verdict("UNKNOWN").

The node's verdict then combines the verdicts of its contexts
(#isaconst("aggregate_verdicts")). Contexts with #verdict("DEAD") are ignored.
If all other contexts give #verdict("PROVED"), or all give #verdict("REFUTED"),
the node gets that verdict, and otherwise #verdict("UNKNOWN"). If one context
proves `x > 0` and another refutes it, the stores reaching $v$ in the first
satisfy the condition and those in the second violate it, so
#verdict("UNKNOWN") is the only sound choice. If no context at $v$ is
reachable, the node is #verdict("DEAD"), and no execution reaches the check
(#isathm("run_voblint_dead_check_unreached")).

A verdict is a claim about the stores at its node. #verdict("PROVED") for a
check `x > 0` claims that $x$ is positive whenever an execution reaches $v$. The verdict is
therefore given a meaning as the set of stores in which its claim is true. This set plays the role that the concretization $conc$
plays for a state. The verdict is then sound exactly when every store reaching
$v$ lies in its set, and the chain of inclusions can continue from the report's
stores $cal(R)_("res")(v)$ to the verdicts. #verdict("PROVED") admits
the stores in which the condition holds, and #verdict("REFUTED") those in which
it fails (#isaconst("verdict_holds")). #verdict("UNKNOWN")
claims nothing and admits every store. #verdict("DEAD") claims that no store
arrives at $v$. The chain already covers this reachability claim through
$cal(R)_("res")(v)$, so as a set of stores it also admits every store:

#definition(name: [Stores admitted by a check verdict], isa: "check_stores", cmd: "definition")[
  For a reported check $c$ with expression $e_c$,
  $
    #isaconst("check_stores") (c) = cases(
      {s | sem(e_c)_e s != 0} & #[if the verdict is #verdict("PROVED")],
      {s | sem(e_c)_e s = 0} & #[if the verdict is #verdict("REFUTED")],
      Sigma & #[if the verdict is #verdict("UNKNOWN") or #verdict("DEAD")].
    )
  $
  where $Sigma$ is the set of all stores.
]

A node can carry several checks, and a store is consistent with the node only
if it is consistent with each of them. The verdict set therefore intersects
their sets:

#definition(
  name: [Stores admitted by all verdicts at a node],
  isa: "verdict_stores",
  cmd: "definition",
)[
  For a node $v$,
  $
    cal(V)_("res")(v) = inter.big_(c in #isaconst("report_checks_at") ("res",v)) #isaconst("check_stores") (c).
  $
]

The verdicts are sound if $cal(R)_("res")(v) subset.eq cal(V)_("res")(v)$,
that is, if every store the states describe satisfies every definite verdict, #verdict("PROVED") or
#verdict("REFUTED"), at $v$. Since the verdicts are computed from these states, the inclusion holds
(#isathm("analysis_report_verdicts_sound")) for every report that
#isaconst("run_voblint") returns (#isathm("run_voblint_consistent")). The
verdict set can be much larger than $cal(R)_("res")(v)$, because a verdict
keeps only the truth value of one condition (last row of @fig:chain).

Consider the example below (@fig:chain), whose program calls `f` twice. The first call passes $1$. The second passes the input $x$ if $1 <= x <= 3$.
So `m` is $2$, $4$, or $6$ at the checks: `m >= 2` always holds, and `m == 2`
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
#let _vge = snapshot-verdict(_snap, "m >= 2")

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
        ([$cal(A)(v,$ #raw(_ctx("f_pp1_ctx0"))$)$], "dots", (2,), vb.called),
        ([$cal(A)(v,$ #raw(_ctx("f_pp1_ctx1"))$)$], "dots", (2, 4, 6), vb.called),
        (
          [$cal(C)(v) = union.big_c cal(A)(v,c)$, reached],
          "dots",
          (2, 4, 6),
          vb.proved,
        ),
        (
          [$cal(R)_("res")(v)$, the report],
          "bar",
          (calc.min(r1.at(0), r2.at(0)), calc.max(r1.at(1), r2.at(1))),
          vb.accent,
        ),
        ([$cal(V)_("res")(v)$, verdict #verdict(_vge)], "from", 2, vb.neutral),
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
  caption: {
    let (r1, r2) = (_range(_m1), _range(_m2))
    let (lo, hi) = (calc.min(r1.at(0), r2.at(0)), calc.max(r1.at(1), r2.at(1)))
    [The sets of stores at the check `m >= 2` (line 3), projected on $m$, under
      Interval with entry-state contexts:
      $cal(A)(v, #raw(_ctx("f_pp1_ctx0"))) = {2}$,
      $cal(A)(v, #raw(_ctx("f_pp1_ctx1"))) = {2, 4, 6}$,
      $cal(C)(v) = {2, 4, 6}$, $cal(R)_("res")(v) = {#lo, dots, #hi}$, and
      $cal(V)_("res")(v) = {m | m >= 2}$. $cal(R)_("res")$ and $cal(V)_("res")$ are analyzer output (claim
      #claim-ref("chain-split-entry")), the rest is derived by hand.]
  },
  kind: image,
  placement: none,
) <fig:chain>

`f` is analyzed in two contexts, one per entry state. The check `m >= 2`
holds for every admitted store in both, so its verdict is #verdict(_vge). The
check `m == 2` sees the same sets, but the contexts disagree. The first call
enters with $n = 1$, and the check is #verdict(_v1) there. The second enters
with $n in [1, 3]$. Its state #absval(raw(_m2)) also admits $3$ and $5$, and the check
is #verdict(_v2), the only sound verdict, since the run with $x = 1$ satisfies
it and the runs with $x = 2$ and $x = 3$ violate it.

== The soundness chain at a program point <sec:chain>

A verdict at a node $v$ is sound if every store that an execution brings to
$v$ satisfies it, that is, if every such store lies in the verdict set
$cal(V)_("res")(v)$. All previous chapters build toward this inclusion, one step at a time. Each
step is an inclusion between two sets of stores at $v$. @ch:program-model and
@ch:traces place the reached stores in the collecting semantics and split it by
context. @ch:equations and @ch:solving place the stores of each context inside
the stores that the report's states describe, and @sec:verdicts places those
inside the verdict set. Chaining the steps gives the goal. Each step may add
stores that no execution reaches, which costs precision, but none loses a
reached store.

To state the steps, fix a report $"res"$ that #isaconst("run_voblint") returns
for a program $p$. The program determines its procedure table $Pi$
(#isaconst("prog_table")), its global-variable classifier $cal(G)$, and its
initial stores $S$ (#isaconst("cinit_stores")). The sets $cal(C)(v)$ and
$cal(A)(v,c)$ are the collecting sets of @ch:traces for its graph. A store $s$
is _reached_ if a source execution from a store $s_0 in S$ arrives at it,
$(#isaconst("main_body") thin Pi, s_0, []) ->_p^* (r,s,F)$. Let $v$ be a node at
which the run is observed, $p, s_0 tack.r (r,s,F) gt.closed v$ (@sec:at-node).
Each step of the chain is a theorem:
// One relation per row, centred over the fact that proves it, so the relations
// line up whatever the length of the fact's name.
#let _step(rel, fact) = stack(dir: ttb, spacing: 2pt, align(center, $#rel$), align(
  center,
  text(size: 7pt, fact),
))
#block(breakable: false, above: 1.6em, below: 1.6em, align(center, grid(
  columns: (1fr, auto, 1fr),
  column-gutter: 10pt,
  row-gutter: 8pt,
  align: (right + horizon, center + horizon, left + horizon),
  [$s$], _step(sym.in, isathm("source_reaches_node_collect")), $cal(C)(v)$,

  [],
  _step($=$, isathm("node_collect_eq_Union_activation_of_has_context")),
  $union.big_c cal(A)(v,c)$,

  [], _step(sym.subset.eq, isathm("run_voblint_covers")), $cal(R)_("res")(v)$,

  [], _step(sym.subset.eq, isathm("analysis_report_verdicts_sound")), $cal(V)_("res")(v)$,
)))
The first step places a store that a finite source execution reaches in the node
collecting semantics, at a node $v$ that the simulation relates to the run. On the annotated copy of the program, this is every node at which the run is observed
(#isathm("csim_point_compile_prog"), @sec:at-node). The second step splits
$cal(C)(v)$ into the sets $cal(A)(v,c)$ of the contexts that the policy
$"adm"$ admits, with `main` in $c_0$ (@sec:contexts). It only requires that every valid trace carries some context.
Functional policies meet this for every trace, and the entry-state policy
meets it through #oblig("TOTAL") on the solution (@sec:contract). The third
inclusion is the analyzer's soundness result. Its proof combines the second
step with the per-context bound of @ch:equations, which places the activation
collecting semantics of each context inside the state solved for it
(#isathm("activation_collect_dg_sound")).
The fourth inclusion is that of @sec:verdicts and depends only on the
report and its consistency.

== The end-to-end soundness theorem #thy-badge("Voblint_CLI", "Analysis_Certified") <sec:headline>

Composing the four steps of @sec:chain gives a theorem about
#isaconst("run_voblint"), the constant exported to the command-line tool and
playground, subject to the trusted code generator and target toolchains
(@sec:codegen, @fig:intro-trust).
#theorem(name: [End-to-end soundness of the analyzer], isa: "run_voblint_source_sound")[
  Fix a program $p$ and an analysis configuration, and suppose the analyzer
  returns $ctor("Analysed")("res")$. Let a finite source execution start from
  the main body with a store $s_0 in S$ and an empty frame stack and reach
  $(r,s,F)$. Then the reached configuration is observed at some node
  (#isaconst("at_node")), and for every node $v$,
  $
    p, s_0 tack.r (r,s,F) gt.closed v quad arrow.r.double quad
    s in cal(C)(v) inter cal(R)_("res")(v) inter cal(V)_("res")(v).
  $
  The graph, procedure table, global classifier, and initial stores are those of
  @sec:chain, with $cal(C)$ from @sec:collecting, $cal(R)_("res")$ from
  @sec:report, and $cal(V)_("res")$ from @sec:verdicts.
]

The theorem speaks about the _analyzed executions_, the finite source
executions of the analyzed program from an initial store in $S$, observed at
any point during the run. Each such point corresponds to a node $v$ of the graph
(#box($p, s_0 tack.r (r,s,F) gt.closed v$)), so no execution falls outside the analysis. At every such node, the execution's store
lies in the collecting semantics ($s in cal(C)(v)$), so the graph accounts for
it. The report's
states at the node describe the store ($s in cal(R)_("res")(v)$), so the
analysis has not missed it. The
store also satisfies every definite verdict at the node
($s in cal(V)_("res")(v)$), so no
#verdict("PROVED") or #verdict("REFUTED") answer contradicts it. A user relies
on this property of the verdicts. Whatever the analyzer reports as
#verdict("PROVED") or #verdict("REFUTED") holds in every execution that reaches
the check. Both hold vacuously at unreached checks, so a
#verdict("REFUTED") verdict is not a verified counterexample.

The theorem makes few assumptions about the run. The run starts from a store
that sets every global to $0$ and leaves the locals of `main` unconstrained
(#isaconst("cinit_stores")). It may be observed at any point, so the theorem
also covers programs that never terminate, through every finite prefix of
their runs. Valid inputs and a terminating solve are not separate premises,
because the analyzer returns a report only when both hold (@sec:report). The
result is still one of partial correctness. If the solve does not terminate,
the analyzer returns no report, and the theorem says nothing about that program
(@sec:certificate).

== Arithmetic diagnostics #thy-badge("Voblint_CLI", "Analysis_Certified") <sec:verdict-meaning>

Besides the checks, a user wants to know whether a division or remainder can
fail. VIMP defines division by zero, whereas C leaves it undefined
(@sec:vimp-vs-c), so the analyzer reports every place where the divisor may be
zero. At each division and remainder, it asks the selected
analyses which values the divisor can take (@sec:coop-queries). It reports
#verdict("ERROR") if the divisor is zero whenever an analyzed execution reaches
the node (#isathm("run_voblint_arithmetic_refuted")), #verdict("WARNING") if the
analyses cannot exclude zero, and nothing otherwise.

A missing diagnostic is itself a safety guarantee. If the analyzer returned a
report and no diagnostic names node $v$, then for every store $s in cal(C)(v)$,
every local edge $(v,a,w)$, every expression $e$ evaluated by $a$, and every
divisor $d$ in $e$,
$ sem(d)_e s != 0 $
(#isathm("run_voblint_arithmetic_intra_safe")). A companion theorem extends
this to the divisors in call arguments (#isathm("run_voblint_arithmetic_safe")).

// The severities come from the claim; the guarded division must stay free of
// diagnostics, or the sentence about line 5 no longer holds.
#let _diag(loc) = check-row("arith-diagnostics", loc: loc).cond
#assert(
  not claim-text("arith-diagnostics").contains("\n5:"),
  message: "arith-diagnostics now reports the guarded division",
)
The program below divides by a constant zero, by an unconstrained input, and by
the same input behind a guard:

#listing(lang: "c", claim: "arith-diagnostics", ```
fun main() {
  x = __voblint_nondet_int();
  a = 10 / 0;
  b = 10 / x;
  if (x > 0) { c = 10 / x; }
}
```)

Under Interval, the analyzer reports #verdict(_diag("3:3")) for line 3, whose
divisor is zero in every execution, and #verdict(_diag("4:3")) for line 4,
where $x$ may be zero. On line 5, the guard
`x > 0` excludes zero from the divisor, so the third division gets no
diagnostic and is safe in every execution that reaches it (claim
#claim-ref("arith-diagnostics")).

These guarantees complete the soundness chain of @fig:intro-nest, whose
inclusions the end-to-end theorem of @sec:headline composes.
