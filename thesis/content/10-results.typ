#import "@preview/cetz:0.5.2"
#import "../lib/code.typ": (
  claim-playground-link, isaconst, isai, isalocale, isathm, isatype, listing, oblig,
  playground-base, thy-badge,
)
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": definition, theorem
#import "../lib/theme.typ": vb
#import "../lib/math.typ": absval, conc, ctor, sem, setcomp
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

= From Post-Solutions to Verdicts <ch:results>

The solution of @ch:solving describes every execution (@sec:certificate).
The analyzer turns it into a report with a verdict for every `__voblint_check`
and diagnostics wherever division may fail. This chapter proves that every
store a finite source execution reaches at a check satisfies the report's
definite verdicts.

== The analyzer function and its report #thy-badge("Voblint_CLI", "Analysis_Run") <sec:report>

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

Before it compiles anything, the analyzer checks its two inputs, so that a
report exists only where the soundness proofs apply. The configuration must
select a nonempty list of distinct analyses, and the program must satisfy the
structural conditions that the compilation theorems of @ch:program-model
assume. An invalid input, and a solve that produces no result, receive an
error answer instead of a report. Every answer #ctor("Analysed") $"res"$ thus
comes from inputs that pass both tests, and the executable test implies the
well-formedness premise of the proofs (#isathm("run_voblint_report_contract"),
#isathm("run_voblint_wf")). The end-to-end soundness theorem therefore needs no
premise about the configuration or the program.

The report that #ctor("Analysed") carries (#isatype("analysis_report")) keeps
the solver's states under their node and context, the values of the global
unknowns, a verdict for every check, and the arithmetic diagnostics. A node that the solver solved in several
contexts carries several states. At a node $v$, the report describes every
store that one of them describes (#isaconst("report_sem")):
$
  cal(R)_("res")(v) = union.big_(d in #isaconst("report_states_at") ("res",v)) conc_("res")(d),
$
where #isaconst("report_states_at") gives the reported states at $v$ and
$conc_("res")$ is the concretization of the
configured analyses, lifted so that $conc_("res")(ctor("Bot"))=emptyset$.
The union drops the contexts, since a source execution
carries no context to compare with, and a user asks what holds at a program
point, whichever call led there. The proof, however, needs the contexts, since
the coverage contract bounds the stores of each context separately
(@sec:contract). The report therefore keeps them, and each state names its
context. The states at $v$ in context $c$ describe the set
$cal(R)_("res")(v,c)$ (#isaconst("report_context_sem")), a subset
of $cal(R)_("res")(v)$.

== Check verdicts from the report <sec:verdicts>

The command-line tool prints the report through its checks. Each check at $v$
receives one of four verdicts, #verdict("PROVED"), #verdict("REFUTED"),
#verdict("UNKNOWN"), or #verdict("DEAD"), printed at the source position of
the check. The #link(playground-base)[browser playground] shows the same
verdicts inline in the editor and beside the graph.

The analyzer first computes one verdict per state. Each state $d$ in
$#isaconst("report_states_at") ("res",v)$ gives its own verdict for a check:

#definition(name: [Check verdict of an abstract state], isa: "classify_point", cmd: "fun")[
  For a check expression $e$ and a lifted state $d$,
  $
    #isaconst("classify_point") (e,d) = cases(
      ctor("Dead") & "if" d = ctor("Bot"),
      ctor("Decided")(italic("classify")(e,x)) & "if" d = ctor("Lifted")(x).
    )
  $
  Here $italic("classify")$ is the analysis's check classifier, a parameter of
  #isaconst("classify_point"). The constructors preserve
  the distinction between an unreachable state and a decided check result.
]

The state #ctor("Bot") gives #verdict("DEAD"). For any other state, the
classifier asks every selected analysis for the truth value of the check's
condition through the queries of @sec:coop-queries and takes the meet of the
answers (#isaconst("mcp_classify")). An exact $1$ gives #verdict("PROVED"), an
exact $0$ gives #verdict("REFUTED"), and any other answer gives
#verdict("UNKNOWN"). A definite answer
holds in every store the state describes (#isathm("mcp_classify_proved"),
#isathm("mcp_classify_refuted")).

The analyzer then joins the per-context verdicts of a node's states into one
verdict for the node (#isaconst("aggregate_verdicts")). If every state other than #ctor("Bot")
gives #verdict("PROVED"), the node is #verdict("PROVED"). If every such state
gives #verdict("REFUTED"), it is #verdict("REFUTED"). If the states disagree,
or one of them gives #verdict("UNKNOWN"), the node is #verdict("UNKNOWN").
For disagreeing states, #verdict("UNKNOWN") is the only sound choice. If one context proves `x > 0` and
another refutes it, the stores reaching $v$ in the first satisfy the condition
and those in the second violate it, so no single definite verdict holds for
every store at the node.
States classified #verdict("DEAD"), the #ctor("Bot") states, are neutral in
this aggregation, so a node at which the report holds no state, or only
#ctor("Bot") states, is #verdict("DEAD").

To state the verdicts' correctness as an inclusion of sets of stores,
like that of the states (@sec:contract),
the verdicts at $v$ are turned into the stores consistent with them, the
_verdict set_
$cal(V)_("res")(v)$. If $v$ carries the check `x > 0` with
verdict #verdict("PROVED"), the verdict set is $setcomp(s, s(x) > 0)$: the verdict
tells the user that $x$ is positive there and nothing else.
#verdict("REFUTED") gives the stores in which the condition fails, and #verdict("UNKNOWN") gives every store
(#isaconst("verdict_holds")).
A #verdict("DEAD") check says nothing about the values in a store. It claims
that no store arrives at $v$, which is a statement about reachability. As a
set of stores, it therefore admits
every store and leaves the claims of the other checks at $v$ untouched:

#definition(name: [Stores admitted by a check verdict], isa: "check_stores", cmd: "definition")[
  For a reported check $c$ with expression $e_c$,
  $
    #isaconst("check_stores") (c) = cases(
      {s | sem(e_c)_e s != 0} & "if the verdict is PROVED",
      {s | sem(e_c)_e s = 0} & "if the verdict is REFUTED",
      Sigma & "if the verdict is UNKNOWN or DEAD".
    )
  $
  Here $Sigma$ is the set of all stores.
]

A store is consistent with what the user reads at $v$ only if no verdict there
contradicts it, so the verdict set keeps exactly the stores that satisfy every
check at $v$:

#definition(
  name: [Stores admitted by all verdicts at a node],
  isa: "verdict_stores",
  cmd: "definition",
)[
  The verdict set intersects the stores admitted by all checks reported at
  node $v$:
  $
    cal(V)_("res")(v) = inter.big_(c in #isaconst("report_checks_at") ("res",v)) #isaconst("check_stores") (c).
  $
  The intersection over no checks is the set of all stores.
]

The intersection states this for any number of checks at a node. In a compiled
program, each check has a node of its own, and the verdict set is then the set
of that single check.

The verdict set can be much larger than
$cal(R)_("res")(v)$, because a verdict keeps only
the truth value of one condition (last row of @fig:chain). Soundness only
requires that every store reaching $v$ lies in it.

Since the verdicts at $v$ are computed from the states at $v$, every store that
one of these states describes satisfies every definite verdict there. Thus
$cal(R)_("res")(v) subset.eq cal(V)_("res")(v)$
(#isathm("analysis_report_verdicts_sound")) for every report that
#isaconst("run_voblint") returns (#isathm("run_voblint_consistent")).

== The soundness chain at a program point <sec:chain>

Let $"res"$ be a report #isaconst("run_voblint") returns for a program $p$,
$g$ = #isaconst("prog_cfg") $p$ its compiled graph, $Pi$ =
#isaconst("prog_table") $p$ its procedure table, $cal(G)$ =
#isaconst("declared_global") $p$ its global-variable classifier, and $S$ =
#isaconst("cinit_stores") $cal(G)$ its initial-store set (@sec:vimp-vs-c,
@ch:traces). With these parameters fixed, write $cal(C)(v)$ and $cal(A)(v,c)$ for the
collecting sets of @ch:traces. A store is _reached_ if some finite source execution, started from a
store in $S$, arrives at it. The argument that a verdict is sound places a
reached store at a CFG node $v$ and follows a chain of inclusions between sets
of stores there. It ends in the
two sets of the report, $cal(R)_("res")(v)$ and
$cal(V)_("res")(v)$. Let $s$ be a store that a source execution reaches,
$(#isaconst("main_body") thin Pi, s_0, []) ->_p^* (r,s,F)$, and let $v$ be a
node at which the run is observed, $p, s_0 tack.r (r,s,F) gt.closed v$
(@sec:at-node). Each step of the chain is a theorem:
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
(#isathm("activation_collect_dg_sound")). The same bound holds for the report
itself, context by context. For the policy $"adm"$ and root context $c_0$ of
the run, every node $v$ and every context $c$ satisfy
$
  cal(A)(v,c) subset.eq cal(R)_("res")(v,c)
$
(#isathm("run_voblint_context_covers")).
The fourth inclusion is that of @sec:verdicts and depends only on the
report and its consistency.

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
  caption: [The chain of inclusions at the check `m >= 2` (line 3), projected
    on $m$, under Interval with entry-state contexts. Each row is a set of
    stores and lies inside the rows below it. Report and verdict are analyzer
    output (claim #claim-ref("chain-split-entry")), and the first three rows
    are derived by hand.],
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

== The end-to-end soundness theorem #thy-badge("Voblint_CLI", "Analysis_Certified") <sec:headline>

Composing the four steps of @sec:chain gives a theorem about
#isaconst("run_voblint"), the constant exported to the command-line tool and
playground, subject to the trusted code generator and target toolchains
(@sec:codegen, @fig:intro-trust).
#theorem(name: [End-to-end soundness of the analyzer], isa: "run_voblint_source_sound")[
  Fix a program $p$ and an analysis configuration. Suppose the analyzer returns
  $ctor("Analysed")("res")$, and a finite source execution starts from
  the main body with store $s_0 in S$ and an empty frame stack, and reaches
  $(r,s,F)$. Write $O$ for the nodes where this reached
  configuration is observed by the source-to-graph relation
  (#isaconst("at_node")). Then
  $
    O != emptyset quad and quad
    forall v in O. s in cal(C)(v) inter cal(R)_("res")(v) inter cal(V)_("res")(v).
  $
  The graph, procedure table, global classifier, and initial stores are those
  determined by $p$, as fixed in @sec:chain. The report set $cal(R)_("res")(v)$
  contains stores described by a reported state at $v$; $cal(C)$ is the node
  collector and $cal(V)_("res")$ the verdict set.
]

The initial stores zero every global and leave
the locals unconstrained (#isaconst("cinit_stores")). Any stopping point of
the source execution is allowed, so nonterminating programs are included
through their finite prefixes. Input validity and solver termination are not
separate premises, since the analyzer returned a report (@sec:report). The
theorem remains a partial-correctness result (@sec:certificate).

As in @sec:at-node, the run determines the observed nodes: a residual command
may occur at several places, so its source configuration alone cannot identify
one.

== Meaning of verdicts and diagnostics #thy-badge("Voblint_CLI", "Analysis_Certified") <sec:verdict-meaning>

By the theorem of @sec:headline, the four verdicts make the following
statements about _analyzed executions_, the finite source executions from an
initial store in $S$, stopped at any point:
- #verdict("PROVED"): whenever an analyzed execution reaches the check, the condition
  holds.
- #verdict("REFUTED"): whenever an analyzed execution reaches the check, the condition
  fails. It is not a verified
  counterexample, since it establishes no reaching execution.
- #verdict("UNKNOWN"): the analysis decides neither.
- #verdict("DEAD"): no analyzed execution reaches the check, because nothing is
  collected at its node (#isathm("run_voblint_dead_check_unreached")).
  Conversely, a check that an execution reaches is never #verdict("DEAD").
#verdict("PROVED") and #verdict("REFUTED") hold vacuously when no execution
reaches the check, and only #verdict("DEAD") claims anything about
reachability. For a run whose next command is the check of $e$ with label $l$,
the report contains a check with label $l$ and expression $e$. Its node
collects the reached store, its verdict is not #verdict("DEAD"), and a
#verdict("PROVED") or #verdict("REFUTED") verdict implies that $e$ is true or
false in that store (#isathm("run_voblint_check_sound")).

At every division and remainder, the analyzer asks the queries of
@sec:coop-queries whether the divisor can be zero. It reports an error if the
divisor is zero whenever an analyzed execution reaches its node
(#isathm("run_voblint_arithmetic_refuted")), a warning if the analyses cannot
exclude zero, and nothing otherwise. If the analyzer returned a report, no
diagnostic has node $v$, and $s in cal(C)(v)$, then for every local edge
$(v,a,w)$, every expression $e$ evaluated by $a$, and every divisor $d$ in $e$,
$ sem(d)_e s != 0. $
This is the intraprocedural guarantee
(#isathm("run_voblint_arithmetic_intra_safe")); the extended result also
applies to call arguments (#isathm("run_voblint_arithmetic_safe")).

These guarantees complete the soundness chain of @fig:intro-nest. The report's states at a
node describe every store that executions bring there. Every store these
states describe satisfies the definite verdicts at that node. The end-to-end theorem of @sec:headline composes all inclusions,
from source executions to verdicts.
