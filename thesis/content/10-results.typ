#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/sources.typ": proved
#import "../lib/theme.typ": vb
#import "../lib/math.typ": ctor, sem
#import "../lib/figures.typ": check-row, int-axis, int-strip, printed-set, snapshot-var
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
closed forward over every unknown an execution visits (@sec:cert-forward). The
client reads neither the valuation nor its contexts. It reads a result table
and one verdict per check, and a verdict needs a precise meaning, since a check
that no execution reaches makes every condition true there. @sec:chain
assembles the pieces at one check, @sec:headline states the theorem about the
exported analyzer #isaconst("run_voblint") that they must yield, and
@sec:verdicts relates the table and the verdicts to the solver's valuation.

== The chain at one check <sec:chain>

At a CFG node $v$, the argument that a verdict is sound is a chain of
inclusions between sets of stores, followed by one implication. Each step is a
theorem:
#let _by(body) = text(size: 7pt, body)
$
  "stores of source runs at" v & underbrace(subset.eq, #_by(isathm("source_reaches_node_collect")))
  #isai("\<C>\<^bsub>\<G>,g,S\<^esub> v") \
  & underbrace(=, #_by(isathm("node_collect_eq_Union_activation_collect")))
  union.big_c #isai("\<A>\<^bsub>\<G>,R,c₀,g,S\<^esub> v c") \
  & underbrace(subset.eq, #_by(isathm("activation_collect_dg_sound")))
  union.big_c sem(#isaconst("lookup_context") thin r thin v thin c) \
  & underbrace(==>, #_by(isathm("run_voblint_sound_at"))) quad "verdict at" v
$
The first set is the stores that finite source runs reach at $v$. The node
collecting semantics #isaconst("node_collect") splits into the activation
collecting semantics #isaconst("activation_collect") of the contexts the
policy's relation $R$ admits, with `main` in the initial context
#isai("c\<^sub>0") (@sec:contexts). #isaconst("lookup_context") $r$ $v$ $c$ is
the state the result table $r$ holds at $v$ in context $c$, and
$sem(dot)$ its set of stores, empty for the unreachable state #ctor("Bot").
The third step bounds each context separately, $c$ by $c$, and the verdict at $v$
combines the per-context results (@sec:verdicts). Each later set may contain
stores that no execution reaches. Soundness requires only that it contains the
set before it.

The program below calls `f` twice. The first call passes $1$; the second
passes an input $x$ with $1 <= x <= 3$, if the input is in that range. So `m` is
$2$, $4$ or $6$ at the check, and `m == 2` holds in some runs and fails in
others.

#listing(lang: "c", claim: "chain-split-entry", ```
fun f(n) {
  m = 2 * n;
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
#let _v1 = upper(_snap.nodes.at("f_pp1_ctx0").status)
#let _v2 = upper(_snap.nodes.at("f_pp1_ctx1").status)
#let _vnode = snapshot-verdict(_snap, "m == 2")
#let _none = cli-row("chain-split-none", "m == 2")

#figure(
  {
    set text(size: 9pt)
    let values = range(0, 8)
    let cell(kind) = box(
      width: 6.2mm,
      height: 4.2mm,
      radius: 1pt,
      stroke: 0.5pt + vb.frame,
      fill: if kind == "run" { vb.proved.lighten(25%) } else if kind == "extra" {
        vb.accent.lighten(72%)
      } else if kind == "cond" { vb.neutral.lighten(55%) } else { none },
    )
    // `runs` are the values some execution has; the rest of `range` is extra.
    // A concrete row fills only `runs`; an abstract row also marks the rest of
    // `range` as admitted.
    let strip(range, runs, kind: "abstract") = values.map(x => {
      let inside = range.at(0) <= x and x <= range.at(1)
      cell(if not inside { "none" } else if kind == "cond" { kind } else if x in runs {
        "run"
      } else if kind == "abstract" { "extra" } else { "none" })
    })
    let label-col(n, body) = align(left + horizon)[#text(fill: vb.muted)[#n] #h(3pt) #body]
    let A(c) = [#isai("\<A>") $v$ #raw(c)]
    table(
      columns: (auto,) + (auto,) * values.len() + (auto,),
      stroke: none,
      inset: (x: 1.2pt, y: 1.5pt),
      align: center + horizon,
      [], ..values.map(x => [$#x$]), [*verdict*],
      label-col(1, [stores of source runs at the check]), ..strip(
        (2, 6),
        (2, 4, 6),
        kind: "concrete",
      ), [],
      label-col(2, [#isai("\<C>") $v$]), ..strip((2, 6), (2, 4, 6), kind: "concrete"), [],
      label-col(3, A(_ctx("f_pp1_ctx0"))), ..strip((2, 2), (2,), kind: "concrete"), [],
      label-col(4, A(_ctx("f_pp1_ctx1"))), ..strip((2, 6), (2, 4, 6), kind: "concrete"), [],
      label-col(5, [$sem(dot)$ in context #raw(_ctx("f_pp1_ctx0")), #raw(_m1)]),
      ..strip(_range(_m1), (2,)),
      raw(_v1),

      label-col(6, [$sem(dot)$ in context #raw(_ctx("f_pp1_ctx1")), #raw(_m2)]),
      ..strip(_range(_m2), (2, 4, 6)),
      raw(_v2),

      table.hline(stroke: 0.4pt + vb.frame),
      label-col([], [stores where `m == 2` holds]), ..strip((2, 2), (), kind: "cond"), [],
    )
  },
  caption: [The soundness chain at the check `m == 2`, projected on $m$, with
    Interval and entry-state contexts. Green: values some run has there; blue:
    values admitted although no run has them. Rows 1 to 4 are derived by hand;
    rows 5 and 6 and the verdicts are analyzer output (claim
    `chain-split-entry`). Each context row lies inside the abstract row of the
    same context. The node verdict joins the two contexts to #raw(_vnode).],
  kind: image,
  placement: auto,
) <fig:chain>

@fig:chain draws the chain. `f` is analyzed in two contexts, one per entry
state. The first call enters with $n = 1$, and in its context the check holds
for every admitted store: #raw(_v1). The second call enters with
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
@ch:solving. What the chain should deliver to a client is this: every store a
finite source run reaches is covered by the result table at a node that
simulates the run, in some context, and every definite verdict listed there
holds of the store.

== The source-level theorem <sec:headline>

One theorem establishes this for the exported analyzer. Its parameters are
the configuration and the program, the four arguments of
#isaconst("run_voblint") (@sec:codegen):
- $"as"$, a list of #isatype("analysis_domain") values, the analyses that run
  together as the combined component of @ch:cooperation, for example
  [#ctor("Interval_Analysis")] or [#ctor("Interval_Analysis"), #ctor("Order_Analysis")];
- $"rule"$, a #isatype("globals_rule"), the update rule for the solver's global
  unknowns, for example #ctor("Globals_Warrow");
- $"ctx"$, a #isatype("context_mode"), the context policy: #ctor("Ctx_None"),
  #ctor("Ctx_EntryState") or #ctor("Ctx_CallString") $k$;
- $p$, the program, an #isatype("imp_prog").
The run of @fig:chain is #isaconst("run_voblint") [#ctor("Interval_Analysis")]
#ctor("Globals_Warrow") #ctor("Ctx_EntryState") $p$. The variables are universally quantified, so the theorem
holds for every configuration, without a separate theorem per analysis or
policy.
#proved("run_voblint_certified_source_sound", note: [Source-level soundness of
  the analyzer.])

The theorem assumes four premises:

#[
  #set enum(numbering: n => "(P" + str(n) + ")")
  + $s_0 in #isaconst("cinit_stores")$, the initial stores $S$ of @ch:traces:
    $s_0$ zeroes every global, and the locals are unconstrained.
  + A finite source execution from `main` reaches $("residual", s, "frs")$. Any
    stopping point is allowed, so nonterminating programs are covered through
    their prefixes.
  + #isaconst("config_terminates"): the solver's recursion is defined on this
    program's query under this configuration.
  + The analyzer returned an answer. Malformed programs are rejected, so
    well-formedness is not a separate premise.
]

From all four together, not from any one of them, it concludes:

#[
  #set enum(numbering: n => "(S" + str(n) + ")")
  + some CFG node $v$ and stack are related to the source configuration by
    #isaconst("csim");
  + #isai("s \<in> \<C>\<^bsub>\<G>,g,S\<^esub> v"): the store is collected
    at that node;
  + the typed result table covers $s$ at $v$ in some context, before its
    abstract values are printed (@sec:codegen);
  + every check listed at $v$ is not `DEAD`, every `PROVED` check holds in $s$,
    and every `REFUTED` check is false in $s$.
]

Two gaps separate the chain of @sec:chain from this statement: the client
reads a table instead of a solver valuation, and one verdict per check instead
of one per context (@sec:verdicts).

== Verdicts <sec:verdicts>

The solver returns a valuation over its unknowns, but the client reads the result
table, indexed by node and context, through #isaconst("lookup_context"). The theorem
#isathm("gamma_reader_eq_lookup") states that both describe the same stores at
every node and context. Unsolved unknowns read as unreachable, which is sound
because every unknown an execution visits is solved (@sec:cert-forward). A
reached store is covered at its node _in some context_:
$
  exists c, A. quad #isaconst("lookup_context") thin r thin v thin c = ctor("Lifted") A and s in sem(A)
$
for the result table $r$ (#isaconst("table_covers")).
The quantifier cannot become universal. Under entry-state routing the test in
`f` is analyzed in one context per recursion depth, and a store with $n = 2$
is admitted in the context of the outer call only. The relation is the
solution-dependent #isaconst("admitted_contexts"), the #isalocale("dg_analysis")
instance of #isaconst("routed_entry_context_rel") (@sec:eq-entry-routing).

A check has one verdict per node, while the table may hold several contexts
there. Each context whose state is not #ctor("Bot") is classified as proved,
refuted or unknown from the answers of @sec:coop-examples: the check asks the
truth value of its condition, every active analysis answers this query from
its field, and #isaconst("answer_check") reads the meet of these answers. An
exact $1$ proves the check, an exact $0$ refutes it, and every other answer
leaves it unknown. Proved and refuted are sound because a definite answer
holds in every store the state describes (#isathm("mcp_classify_proved"),
#isathm("mcp_classify_refuted")). An answer that admits no value also gives
unknown, so the classification never yields `DEAD`.

The per-context verdicts are joined in the flat order in which unknown is the
top. The join follows from the existential context above: the theorem
does not say which context covers a store, so the node verdict may claim only
what every contributing context claims, and a proved and a refuted context
give unknown. A context whose state is #ctor("Bot") denotes no store and
contributes nothing: classifying it would be vacuous, since every verdict is
true of every store it denotes. The type #isatype("contextual_verdict") is the
verdict type lifted by a bottom element, and that bottom is `DEAD`, the unit of
the join. A node is `DEAD` exactly when every context the table holds there is
#ctor("Bot"). The join ranges over the contexts solved at the node, a finite
set because a terminating solve returns a finite set of unknowns
(#isathm("finite_stabl_solve"), @sec:cert-param).

Each verdict below has a meaning only under the premises of the theorem
(P3 and P4 in @sec:headline): the abstract solve terminates, and #isaconst("run_voblint")
returned an answer. It speaks about _covered executions_: finite source
executions of `main` from an initial store in #isaconst("cinit_stores"),
stopped at any point. Except for `DEAD`, the meaning is conditional on
reaching the check:

- `PROVED`: whenever a covered execution reaches the check, the condition
  holds (#isathm("run_voblint_check_sound")).
- `REFUTED`: whenever a covered execution reaches the check, the condition
  fails (#isathm("run_voblint_check_sound")). It is not a verified counterexample. The abstraction admits stores no
  run has, so a condition that fails at every admitted store does not imply
  that any admitted store is reached.
- `UNKNOWN`: the abstraction decides neither.
- `DEAD`: the node collecting semantics at the node is empty, so no covered
  execution reaches the check's node (#isathm("run_voblint_dead_check_unreached")). This is the one reachability claim. The other
  three verdicts constrain each store at the node and hold vacuously when there
  is none. `DEAD` constrains the whole set.

#let _pu = check-row("verdicts-proved-unreachable", cond: "x > 0")
A `PROVED` verdict at a check that no run reaches is therefore no
contradiction. In the program below, $x = 3n$ is never 1 or 2, so no run
reaches the check. The interval analysis cannot see this and keeps
#raw(_pu.state) there, where `x > 0` holds, so it reports #raw(_pu.verdict).
The verdict is sound, because it only claims that `x > 0` holds whenever a run
reaches the check.

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

Conditions are evaluated in the VIMP semantics, so a `PROVED` verdict can
depend on its convention for division by zero (@sec:vimp-vs-c).

In @fig:verdict-regions no run reaches either check, yet the interval analysis
marks only one of them `DEAD`.

#listing(lang: "c", claim: "verdicts-mult3-interval", ```
fun main() {
  n = __voblint_nondet_int();
  x = 3 * n;
  if (x > 0) {
    if (x < 3) {
      __voblint_check(x == 1);
    }
  } else {
    if (x > 5) {
      __voblint_check(x == 6);
    }
  }
}
```)

#figure(
  {
    set text(size: 8.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let (lo, hi) = (-7, 7)
    let snap(node) = snapshot-var("verdicts-mult3-interval", "main_" + node + "_ctx0", "x")
    let int-verdict(cond) = raw(check-row("verdicts-mult3-int", cond: cond).verdict)
    let ivl-verdict(cond) = raw(check-row("verdicts-mult3-interval-checks", cond: cond).verdict)
    // reach(x): whether some run has this x at the node; runs have x = 3n.
    let row(node, path, reach, verdicts) = {
      let v = snap(node)
      let inside = printed-set(v)
      let kind(x) = if inside(x) and calc.rem-euclid(x, 3) == 0 and reach(x) {
        "run"
      } else if inside(
        x,
      ) { "extra" } else { none }
      (raw(node), path, ..int-strip(lo, hi, kind), raw(v), ..verdicts)
    }
    let dash = text(fill: vb.muted)[–]
    table(
      columns: (auto, auto) + (auto,) * (hi - lo + 3) + (auto, auto, auto),
      column-gutter: (3pt, 3pt) + (0pt,) * (hi - lo + 2) + (3pt, 4pt, 5pt),
      stroke: none,
      inset: (x: 0.9pt, y: 1.6pt),
      align: center + horizon,
      table.hline(stroke: 0.5pt),
      [*node*], [*reached after*], table.cell(colspan: hi - lo + 3)[$x$],
      [*state*], table.cell(colspan: 2)[*verdict*],
      [], [], ..int-axis(lo, hi), text(size: 7pt)[Interval], text(size: 7pt)[Interval],
      text(size: 7pt)[Int],
      table.hline(stroke: 0.4pt),
      ..row("pp3", [`x > 0`], x => x > 0, (dash, dash)),
      ..row("pp4", [`x > 0`, `x < 3`], x => false, (ivl-verdict("x == 1"), int-verdict("x == 1"))),
      ..row("pp6", [`!(x > 0)`], x => x <= 0, (dash, dash)),
      ..row(
        "pp7",
        [`!(x > 0)`, `x > 5`],
        x => false,
        (ivl-verdict("x == 6"), int-verdict("x == 6")),
      ),
      table.hline(stroke: 0.5pt),
    )
  },
  kind: image,
  placement: auto,
  caption: [Verdicts on the program of this section, projected on $x = 3n$. Green: values
    some run has at the node (by hand); blue: values the interval admits
    although no run has them. States and verdicts are analyzer output (claims
    `verdicts-mult3-*`, without contexts). At `pp4` the interval $[1, 2]$ admits
    values no run has, so the check is `UNKNOWN` although no run reaches it. At
    `pp7` the guard contradicts $[-infinity, 0]$ and the check is `DEAD`. The
    Int product also tracks $x equiv 0 med (mod 3)$ and marks both `DEAD`.],
) <fig:verdict-regions>

For a source run about to execute a check,
#isathm("run_voblint_check_sound") finds a listed check with the same label
and condition at a node where the store is collected, and that check's verdict
holds of the store. The label is the check's source position, written by the
parser, which is trusted to write it correctly.
#isathm("run_voblint_labelled_check_sound") additionally assumes that the labels
of a result are distinct. The command-line tool checks this condition and
refuses to print a result when it fails. Under this assumption, every row
carrying a source label belongs to the check written at that position. The listed check is existential because a source state does not
determine its node, so the statement cannot be read backwards to conclude that
a `DEAD` node is unreached. #isathm("run_voblint_dead_check_unreached") proves
that conclusion forwards instead: every store collected at the node would
satisfy the claim there, and a `DEAD` claim admits none.

Arithmetic diagnostics are stated per node as well. By
#isathm("run_voblint_arithmetic_safe"), a node without a diagnostic has nonzero
divisors in every collected store. A warning only means that the abstraction
could not exclude a zero divisor.


Four features of the theorem are forced. The node is existential because a
source configuration does not determine its CFG node (@ch:traces), the context
because a store is covered in some context only, and coverage of the solved
unknowns is absent because it is derived (@sec:cert-forward). Termination of the
abstract solve is the one premise not discharged in general (@sec:termination),
so the theorem is a partial-correctness result, and the analyzed program need
not terminate. #isathm("certificate_demo_source_certified") discharges every
premise by evaluation for one program and configuration, a non-vacuity witness.
@ch:instances compares what the shipped domains can prove under the theorem,
and @ch:executable draws the boundary between #isaconst("run_voblint") and the
delivered tool.
