#import "@preview/cetz:0.5.2"
#import "../lib/code.typ": (
  claim-playground-link, isaconst, isai, isalocale, isathm, isatype, listing, oblig,
  playground-base, thy-badge,
)
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": theorem
#import "../lib/theme.typ": vb
#import "../lib/math.typ": absval, ctor, sem, setcomp
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

= From Solutions to Verdicts <ch:results>

This chapter derives the guarantees of the analyzer's report for the
executions of the source program. Solving the equations of @ch:equations
(@ch:solving) gives an abstract state for each CFG node and context the solver
reached, as well as a value for each global unknown. By @sec:certificate, these states cover every
execution. A user, however, reads neither the states nor the contexts. The user reads
a report with one verdict for every `__voblint_check` and a diagnostic wherever
a division may fail. The chapter shows how the analyzer derives this report
from the solution and why every verdict in it is sound.

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

Before it compiles anything, #isaconst("run_voblint") checks its two inputs,
so that a report exists only where the soundness proofs apply.
#isaconst("valid_config") requires a nonempty list of distinct analyses, and
#isaconst("wf_program_compile_input_exec") decides the structural conditions
that the compilation theorems of @ch:program-model assume. An input that fails
is answered with #isaconst("Invalid_Activation") or
#isaconst("Malformed_Program"), and #isaconst("No_Answer") stands for a solve
that produces no result. Every answer #ctor("Analysed") $"res"$ thus comes
from inputs that pass both tests (#isathm("run_voblint_report_contract")), and
the executable test implies the well-formedness premise of the proofs
(#isathm("wf_program_compile_input_exec_sound"), #isathm("run_voblint_wf")).
The end-to-end soundness theorem of @sec:headline therefore needs no premise about the
configuration or the program.

The report that #ctor("Analysed") carries (#isatype("analysis_report")) keeps
the solver's states under their node and context, the values of the global
unknowns, a verdict for every check (@sec:verdicts), and the arithmetic
diagnostics (@sec:verdict-meaning). A node that the solver solved in several
contexts carries several states. At a node $v$, the report describes every
store that one of them describes (#isaconst("report_states_at"),
#isaconst("report_sem")):
$
  #isai("\<R>\<^bsub>res\<^esub> v") = union.big_(#isai("d \<in> report_states_at res v")) #isai("\<gamma>\<^bsub>res\<^esub> d"),
$
where #isai("\<gamma>\<^bsub>res\<^esub>") is the concretization of the
configured analyses. The union drops the contexts, since a source execution
carries no context to compare with, and a user asks what holds at a program
point, whichever call led there. The proof, however, needs the contexts, since
the coverage contract bounds the stores of each context separately
(@sec:contract). The report therefore keeps them, and each state names its
context. The states at $v$ in context $c$ describe the set
#isai("report_context_sem res v c") (#isaconst("report_context_sem")), a subset
of #isai("\<R>\<^bsub>res\<^esub> v"). @sec:chain shows that this set contains every
store that an activation in context $c$ reaches at $v$.

== Computing check verdicts from the report <sec:verdicts>

The command-line tool prints the report through its checks: each check at $v$
receives one of four verdicts, #verdict("PROVED"), #verdict("REFUTED"),
#verdict("UNKNOWN"), or #verdict("DEAD"). The
#link(playground-base)[browser playground] shows the same verdicts inline in
the editor and beside the graph, together with the state of every node and context, and a replay of the solve (@sec:ocaml-boundary, @sec:tracing). Each
verdict is printed at the source position of its check, and the text report checks that these positions are unique (#isathm("run_voblint_labelled_check_sound")).

The analyzer first computes one verdict per state. Each state $d$ in
#isai("report_states_at res v") gives its own verdict for a check:

#thy("classify_point")

The state #ctor("Bot") gives #verdict("DEAD"). Any other state is classified
by #isaconst("mcp_classify"), which asks every selected analysis for the truth
value of the check's condition through the queries of @sec:coop-queries and takes the meet of the
answers: an exact $1$ gives #verdict("PROVED"), an exact $0$ gives
#verdict("REFUTED"), and any other answer gives #verdict("UNKNOWN"). A definite answer
holds in every store the state describes (#isathm("mcp_classify_proved"),
#isathm("mcp_classify_refuted")).

The verdict of the CFG node soundly joins the per-context verdicts of its states
(#isaconst("aggregate_verdicts")). If every state other than #ctor("Bot")
gives #verdict("PROVED"), the node is #verdict("PROVED"). If every such state
gives #verdict("REFUTED"), it is #verdict("REFUTED"). If the states disagree,
or one of them gives #verdict("UNKNOWN"), the node is #verdict("UNKNOWN").
Disagreement cannot be resolved otherwise. If one context proves `x > 0` and
another refutes it, the stores reaching $v$ in the first satisfy the condition
and those in the second violate it, so no single definite verdict holds for
every store at the node.
States classified #verdict("DEAD"), the #ctor("Bot") states, are neutral in
this aggregation, so a node at which the report holds no state, or only
#ctor("Bot") states, is #verdict("DEAD").

The chain of @sec:chain has to end in
something an end user reads, and an end user reads the verdicts rather than
the states. To state that
the verdicts are correct as an inclusion of sets, the verdicts at $v$ are turned
into the set of stores consistent with them, the _verdict set_
#isai("\<V>\<^bsub>res\<^esub> v"). If $v$ carries the check `x > 0` with
verdict #verdict("PROVED"), the verdict set is $setcomp(s, s(x) > 0)$: the verdict
tells the user that $x$ is positive there and nothing else.
#verdict("REFUTED") gives the stores in which the condition fails, and #verdict("UNKNOWN") gives every store
(#isaconst("verdict_holds")).
A #verdict("DEAD") check says nothing about the values in a store. It claims
that no store arrives at $v$, which is a statement about reachability, and
@sec:verdict-meaning treats it. As a set of stores, it therefore admits
every store and leaves the claims of the other checks at $v$ untouched:

#thy("check_stores")

A store is consistent with what the user reads at $v$ only if no verdict there
contradicts it, so the verdict set keeps exactly the stores that satisfy every
check at $v$:

#thy("verdict_stores")

The intersection states this for any number of checks at a node. In a compiled
program, each check has a node of its own, and the verdict set is then the set
of that single check.

The verdict set can be much larger than
#isai("\<R>\<^bsub>res\<^esub> v"), because a verdict keeps only
the truth value of one condition (last row of @fig:chain). Soundness needs
only that every store reaching $v$ lies in it.

Since the verdicts at $v$ are computed from the states at $v$, every store that
one of these states describes satisfies every definite verdict there. Thus
#isai("\<R>\<^bsub>res\<^esub> v \<subseteq> \<V>\<^bsub>res\<^esub> v")
(#isathm("analysis_report_verdicts_sound")) for every report that
#isaconst("run_voblint") returns (#isathm("run_voblint_consistent")).

== Four inclusions from source execution to verdict <sec:chain>

Let $"res"$ be a report #isaconst("run_voblint") returns for a program $p$,
$g$ = #isaconst("prog_cfg") $p$ its compiled graph, $cal(G)$ =
#isaconst("declared_global") $p$ its global-variable classifier, and $S$ =
#isaconst("cinit_stores") $cal(G)$ its initial-store set (@sec:vimp-vs-c,
@ch:traces). A store is _reached_ if some finite source execution, started from a
store in $S$, arrives at it. The argument that a verdict is sound places a
reached store at a CFG node $v$ and follows a chain of inclusions between sets
of stores there. It ends in the
two sets of the report, #isai("\<R>\<^bsub>res\<^esub> v") and
#isai("\<V>\<^bsub>res\<^esub> v"). Let $s$ be a store that a source execution
reaches,
#isai("\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (r, s, frs)"),
and let $v$ be a node at which the run is observed,
#isai("p, s0 \<turnstile> (r, s, frs) \<rhd> v") (@sec:at-node). Each step
of the chain is a theorem:
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
  [$s$],
  _step(sym.in, isathm("source_reaches_node_collect")),
  isai("\<C>\<^bsub>\<G>,g,S\<^esub> v"),

  [],
  _step($=$, isathm("node_collect_eq_Union_activation_of_has_context")),
  $union.big_c #isai("\<A>\<^bsub>\<G>,adm,c₀,g,S\<^esub> v c")$,

  [], _step(sym.subset.eq, isathm("run_voblint_covers")), isai("\<R>\<^bsub>res\<^esub> v"),

  [],
  _step(sym.subset.eq, isathm("analysis_report_verdicts_sound")),
  isai("\<V>\<^bsub>res\<^esub> v"),
)))
The first step places a store that a finite source execution reaches in the node
collecting semantics, at a node $v$ that the simulation relates to the run. On the elaborated program, this is every node at which the run is observed
(#isathm("csim_point_compile_prog"), @sec:at-node). The second step splits
#isaconst("node_collect") into #isaconst("activation_collect") over the
contexts #isai("adm") admits, with `main` in #isai("c\<^sub>0")
(@sec:contexts). It needs only that every valid trace carries some context.
Functional policies meet this for every trace, and the entry-state policy
meets it through #oblig("TOTAL") on the solution (@sec:contract). The third
inclusion is the analyzer's soundness result. Its proof combines the second
step with the per-context bound of @ch:equations, which places the activation
collecting semantics of each context inside the state solved for it
(#isathm("activation_collect_dg_sound")). The same bound holds for the report
itself, context by context. For the policy #isai("adm") and root context
#isai("c\<^sub>0") of the run, every node $v$ and every context $c$ satisfy
$
  #isai("\<A>\<^bsub>\<G>,adm,c₀,g,S\<^esub> v c") subset.eq #isai("report_context_sem res v c")
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
        ([#isai("\<A>") $v$ #raw(_ctx("f_pp1_ctx0"))], "dots", (2,), vb.called),
        ([#isai("\<A>") $v$ #raw(_ctx("f_pp1_ctx1"))], "dots", (2, 4, 6), vb.called),
        (
          [$#isai("\<C>") med v = union.big_c #isai("\<A>") med v med c$, reached],
          "dots",
          (2, 4, 6),
          vb.proved,
        ),
        (
          [#isai("\<R>\<^bsub>res\<^esub> v"), the report],
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
with $n in [1, 3]$. Its state #absval(raw(_m2)) also admits $3$ and $5$, and the check
is #verdict(_v2), the only sound verdict, since the run with $x = 1$ satisfies
it and the runs with $x = 2$ and $x = 3$ violate it.

== The end-to-end soundness theorem #thy-badge("Voblint_CLI", "Analysis_Certified") <sec:headline>

The chain of @sec:chain argues about one store at one node, and each of its
steps is a separate theorem about an intermediate set of stores. A user of the
analyzer needs a single statement instead, one that holds for every program and every analysis
configuration. The
end-to-end soundness theorem composes the four steps into such a statement. It
quantifies over an arbitrary analysis configuration and program, the arguments
of #isaconst("run_voblint") (@sec:report). Whenever the analyzer returns a
report, every store that a finite source execution reaches is covered by that
report and satisfies its definite verdicts. Of the sets in the chain, its conclusion keeps the node collecting semantics,
#isai("\<R>\<^bsub>res\<^esub> v"), and the verdict set. Its per-context
counterpart is #isathm("run_voblint_context_covers") (@sec:chain).

The theorem is about #isaconst("run_voblint") itself, the constant that code
generation exports. It therefore concerns the analyzer that the command-line
tool and the playground run, up to the trusted code generator and target
toolchains (@sec:codegen, @fig:intro-trust).
#theorem(name: [End-to-end soundness of the analyzer], isa: "run_voblint_source_sound")[
  #proved("run_voblint_source_sound")
]

Here $cal(G)$ and $g$ are as in @sec:chain, and #isai("\<Pi>") is the procedure
table #isaconst("prog_table") $p$. The theorem assumes three premises:

#[
  #set enum(numbering: n => "(P" + str(n) + ")")
  + #isai("s0 \<in> cinit_stores \<G>"): the run starts from a store in
    #isaconst("cinit_stores"), the initial stores $S$ of @ch:traces, which zero
    every global, as C does for objects with static storage duration, and leave
    the locals unconstrained.
  + #isai("\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"):
    a finite #isaconst("pstep") execution of $p$ runs from the body of `main`
    to a configuration with store $s$. Any stopping point is allowed, so
    nonterminating programs are covered through their prefixes.
  + #isaconst("run_voblint") $"config"$ $p$ $=$ #ctor("Analysed") $"res"$: the
    analyzer returned a report. Input validity and solver termination are
    therefore not separate premises (@sec:report), and the theorem is a
    partial-correctness result: termination is not proved for every program
    (@sec:certificate).
]

The conclusions are stated at graph nodes, but a source configuration names
none, since its residual command can occur at several places in the program.
The node comes from the run, through the relation
$p, s_0 tack.r ("residual", s, "frs") gt.closed v$ of @sec:at-node
(#isaconst("at_node")), which may observe one configuration at several nodes.

The theorem has two halves. The first states that the configuration is
observed at some node. The second states that at every node $v$ where it is
observed

#[
  #set enum(numbering: n => "(S" + str(n) + ")")
  + #isai("s \<in> \<C>\<^bsub>\<G>,g,S\<^esub> v"): the store is collected at that node;
  + #isai("s \<in> \<R>\<^bsub>res\<^esub> v"): some state the report
    holds at $v$, under one of its contexts, describes $s$;
  + #isai("s \<in> \<V>\<^bsub>res\<^esub> v"): every #verdict("PROVED") check listed at $v$
    holds in $s$, and every #verdict("REFUTED") check is false in $s$.
]

== What verdicts and diagnostics guarantee #thy-badge("Voblint_CLI", "Analysis_Certified") <sec:verdict-meaning>

By the theorem of @sec:headline, the four verdicts make the following
statements about _covered executions_, the finite source executions from an
initial store in #isaconst("cinit_stores"), stopped at any point:
- #verdict("PROVED"): whenever a covered execution reaches the check, the condition
  holds (#isathm("run_voblint_check_sound")).
- #verdict("REFUTED"): whenever a covered execution reaches the check, the condition
  fails (#isathm("run_voblint_check_sound")). It is not a verified
  counterexample: it establishes no reaching execution.
- #verdict("UNKNOWN"): the analysis decides neither.
- #verdict("DEAD"): no covered execution reaches the check: nothing is
  collected at its node (#isathm("run_voblint_dead_check_unreached")), and a
  check that an execution reaches is never #verdict("DEAD") (#isathm("run_voblint_check_sound")).
#verdict("PROVED") and #verdict("REFUTED") hold vacuously when no execution
reaches the check, and only #verdict("DEAD") claims anything about
reachability. The corresponding theorem for #verdict("PROVED") and #verdict("REFUTED") is:

#[
  #show raw.where(block: true): set text(size: 6.5pt)
  #proved("run_voblint_check_sound")
]

The report also contains arithmetic diagnostics. At every division and
remainder, the analyzer asks, through the queries of
@sec:coop-queries, whether the divisor can be zero. It reports an error if the analyses
show that it is zero, a warning if they cannot exclude zero, and nothing
otherwise. An error means that the divisor is zero whenever a covered execution reaches
its node (#isathm("run_voblint_arithmetic_refuted")). At a node $v$ without a diagnostic,
every divisor in an expression on an intraprocedural edge leaving $v$ is
nonzero in every store collected at $v$
(#isathm("run_voblint_arithmetic_safe") adds call arguments):

#[
  #show raw.where(block: true): set text(size: 6.5pt)
  #proved("run_voblint_arithmetic_intra_safe")
]

These theorems complete the chain of @fig:intro-nest. Each verdict holds for
every covered execution that reaches its check, in every analysis configuration.
Termination (@sec:certificate) and the components outside the proof
(@fig:intro-trust) are not covered.
