#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/sources.typ": proved
#import "../lib/theme.typ": vb
#import "../lib/math.typ": conc, ctor
#import "../lib/figures.typ": check-row, int-axis, int-strip, printed-set, snapshot-var

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

// The value range of `a` in a one-variable interval state, `none` for top.
#let a-range(state) = {
  let m = state.match(regex("\[(-?\d+),(-?\d+)\]"))
  if m == none {
    assert(state.contains("⊤"), message: "unexpected state " + state)
    none
  } else { (int(m.captures.at(0)), int(m.captures.at(1))) }
}

= The Source-Level Soundness Theorem <ch:results>

RQ1 asks for one theorem about the answers of the exported analyzer
#isaconst("run_voblint"), from source executions to verdicts. @sec:headline
states it. Chaining the preceding results does not yet give it. Equation
soundness bounds only the unknowns the solver certified, and the certificate
is closed backward from the query, while an execution moves forward into keys
the query need not depend on (@sec:live-keys). The client reads a table and a
verdict per check, not a solver valuation per context (@sec:table). A verdict
also needs a precise meaning: a check that no execution reaches makes every
condition true there (@sec:verdicts).

== The source-level theorem <sec:headline>

The theorem is stated once for every domain, global update rule and context
policy that #isaconst("run_voblint") accepts:
#proved("run_voblint_certified_source_sound", note: [Source-level soundness of
  the analyzer.])

#figure(
  table(
    columns: (1fr, 1fr),
    align: (left, left),
    stroke: none,
    inset: (x: 6pt, y: 4pt),
    table.hline(),
    [*What it assumes*], [*What it establishes*],
    table.hline(stroke: 0.5pt),
    [$s_0 in #isaconst("cinit_stores")$, the initial stores $S$ of
      @ch:traces: $s_0$ zeroes every global; locals are unconstrained.],
    [A CFG node $v$ and stack that #isaconst("csim") relates to the source
      configuration.],

    [A finite source execution from `main` reaches $("residual", s, "frs")$.
      Any stopping point is allowed, so nonterminating programs are covered
      through their prefixes.],
    [#isai("s \<in> \<C>\<^bsub>\<G>,g,S\<^esub> v"): the store is collected at that node.],

    [#isaconst("config_terminates"): the solver's recursion is defined on this
      program's query under this configuration.],
    [The typed table covers $s$ at $v$ in some context, before its abstract
      values are printed (@sec:codegen).],

    [The analyzer returned an answer. Malformed programs are rejected, so
      well-formedness is not a separate premise.],
    [Every check listed at $v$ is not `DEAD`; `PROVED` holds and `REFUTED`
      fails in $s$.],
    table.hline(),
  ),
  caption: [The premises and conclusions of
    #isathm("run_voblint_certified_source_sound"). The rows are not paired: the
    conclusions follow from all four premises together.],
) <tab:headline>

Four features of the statement are forced. The node is existential because a
source configuration does not determine its CFG node (@ch:traces), the context
because a store is covered in some context only (@sec:table), and coverage of
the solved keys is absent because @sec:live-keys derives it. Termination is a
premise of its own, separate from the answer, because #isaconst("run_voblint")
is a total HOL function that denotes an unspecified answer where the solve does
not terminate (@sec:termination).

Termination is the one premise not discharged in general, so the theorem is a
partial-correctness result. The premise concerns the abstract solve, not the
analyzed program, whose finite prefixes are covered (@tab:headline).
@sec:termination shows configurations under which the solve diverges
and explains why no vendored termination theorem applies.
#isathm("certificate_demo_full_certificate") discharges the premise by
evaluation, trusting the code generator, for one program at one configuration:
the Int product, the join rule and call strings of length one. A solve that
does not finish gives no answer from the delivered tool, and the theorem makes
no claim about it.

The theorem is about the HOL constant #isaconst("run_voblint"). The delivered
tool also relies on the parser, Isabelle's code generator, the OCaml toolchain
and the rendering code, which @sec:trust-boundary lists as trusted. What its
verdicts mean, including why `REFUTED` is no counterexample and `DEAD` the only
reachability claim, is defined in @sec:verdicts.

== The chain at one check <sec:chain>

At a CFG node $v$ the proof of the theorem is a chain of inclusions between
sets of stores, followed by one implication. Writing $C_c$ for
#isai("activation_collect \<G> R startcontext g S v c"),
$
  "stores of source runs at" v subset.eq #isai("\<C>\<^bsub>\<G>,g,S\<^esub> v")
  = union.big_c C_c, quad C_c subset.eq conc(A_(v, c))
  quad => quad "verdict at" v.
$
Here $A_(v,c)$ is the abstract state the published table holds for $v$ in
context $c$. Every inclusion may lose precision, but none may lose a store.

The recursive program below computes $f(2) = 2 dot f(1) = 2$, so every run
reaches the check with $a = 2$. It is a regression fixture of the analyzer.

#listing(lang: "c", claim: "chain-factorial-entry", ```
fun f(n) {
  if (n < 2) {
    return 1;
  } else {
    r = f(n - 1);
    return n * r;
  }
}

fun main() {
  a = f(2);
  __voblint_check(a == 2);
}
```)

#let chain-none = cli-row("chain-factorial-none", "a == 2")
#let chain-entry = cli-row("chain-factorial-entry", "a == 2")
#let chain-join = cli-row("chain-factorial-none-join", "a == 2")

#figure(
  {
    set text(size: 9pt)
    let values = range(-1, 5)
    let cell(kind, body: none) = box(
      width: 7.2mm,
      height: 4.2mm,
      radius: 1pt,
      stroke: 0.5pt + vb.frame,
      fill: if kind == "run" { vb.proved.lighten(25%) } else if kind == "extra" {
        vb.accent.lighten(72%)
      } else if kind == "cond" { vb.neutral.lighten(55%) } else { none },
      align(center + horizon, body),
    )
    // A strip over a = -1..4 with an overflow cell at each end.
    let strip(range, kind: "run") = {
      let unbounded = range == none
      let inside(x) = unbounded or (range.at(0) <= x and x <= range.at(1))
      let pick(x) = if not inside(x) { "none" } else if x == 2 or kind == "cond" {
        kind
      } else { "extra" }
      let edge = cell(if unbounded { "extra" } else { "none" }, body: sym.dots.h)
      (edge, ..values.map(x => cell(pick(x))), edge)
    }
    let label-col(n, body) = align(left + horizon)[#text(fill: vb.muted)[#n] #h(3pt) #body]
    table(
      columns: (auto,) + (auto,) * (values.len() + 2) + (auto,),
      stroke: none,
      inset: (x: 1.2pt, y: 1.5pt),
      align: center + horizon,
      [], [], ..values.map(x => [$#x$]), [], [*verdict*],
      label-col(1, [stores of source runs at the check]), ..strip((2, 2)), [],
      label-col(2, [#isaconst("ltr_collect") at `pp6`, the one context of `main`]),
      ..strip((2, 2)),
      [],

      label-col(3, [$conc(A)$ without contexts, #raw(chain-none.at(4))]),
      ..strip(a-range(chain-none.at(4))),
      raw(chain-none.at(3)),

      label-col(4, [$conc(A)$ with entry-state contexts, #raw(chain-entry.at(4))]),
      ..strip(a-range(chain-entry.at(4))),
      raw(chain-entry.at(3)),

      table.hline(stroke: 0.4pt + vb.frame),
      label-col([], [stores where `a == 2` holds]), ..strip((2, 2), kind: "cond"), [],
    )
  },
  caption: [The soundness chain at the check of this section, projected on $a$. Green:
    the value every run has there; blue: values admitted although no run has
    them. Rows 1 and 2 are derived by hand; rows 3 and 4 are analyzer output.
    Row 1 lies in row 2 by #isathm("source_reaches_ltr_collect"), and row 2 in
    rows 3 and 4 by #isathm("run_voblint_sound_at"). `PROVED` requires the
    admitted stores to lie in the bottom row.],
  kind: image,
  placement: auto,
) <fig:chain>

@fig:chain draws the chain for two context policies. Rows 1 and 2 do not
depend on the policy, and every inclusion holds under both. The policy only decides
how far the abstract rows exceed row 2.
Without contexts, the two activations of `f` share one entry and one exit. The
combine after the recursive call reads the returned value from that same exit,
so the value `f` returns is computed from itself, and the analysis loses it.
Widening the entry is not the cause: under the joining update rules the entry
stays at $n in [1, 2]$, and the check is still #raw(chain-join.at(3)) with
#raw(chain-join.at(4)). With entry-state contexts each recursion depth keeps
its own entry and exit, and the result stays exact. Precision is decided at
the last inclusion, while soundness needs all of them.

The first link is the compiler simulation of @ch:program-model composed with
the trace construction of @ch:traces. The split of the collection into context
buckets is #isathm("ltr_collect_eq_Union_activation_collect"), which rests on
#oblig("TOTAL"). Equation soundness (@ch:equations) bounds each bucket by the
solver's valuation, given the certificate of @ch:solving. Two steps remain:
coverage of every key an execution visits, and the passage from the solver's
valuation to the table a client reads.

== From certified keys to executions <sec:live-keys>

Equation soundness bounds only the unknowns in the certified set $V$. A
concrete execution may visit any node in any admitted context, so the proof
needs $V$ to be closed _forward_: along intraprocedural edges, from a call site
to its continuation, and into the callee's entry under the context the call
selects. The certificate provides the opposite closure. An equation reads its
predecessors, so $V$ is closed _backward_ from the query at the exit of `main`.
A statement compiled after a `return` shows that the two differ: it can be
solved, yet nothing the query depends on reads its successors.

The fix restricts attention to _live_ keys (#isaconst("live_keys")): solved
keys whose node is live in a procedure whose result is solved in the same
context. Liveness (#isaconst("prog_live")) is defined on the program text: a
statement is live if no command before it in its sequence cannot fall through.
The semantic alternative, that the node can still reach its procedure's result,
is not preserved along the edges of an arbitrary graph, and control after a
`return` can run into a node with no way out. The syntactic notion has the two
properties the argument needs. Every live node reaches the procedure's result
along the steps an equation reads backwards, and every edge out of a live node
lands on a live node. A successor of a live key therefore reaches a solved
result, and backward closure from that result puts the successor into $V$.

The call case has one more condition. The callee's entry is covered only when
the state the call enters is not #ctor("Bot"), because only then does the
solve select a callee context and demand its result. An execution that makes
the call enters with a store that this state describes, so the state is not
#ctor("Bot") in the cases the proof needs. #isathm("live_keys_cover")
derives the forward closure from well-formedness and termination alone, so
coverage is not a premise of the final theorem.

== Reading the published table <sec:table>

The solver returns a valuation over its unknowns, but the client reads a table
indexed by node and context through #isaconst("lookup_context"). The theorem
#isathm("gamma_reader_eq_lookup") states that both describe the same stores at
every node and context. Unsolved keys read as unreachable. This is sound
because every key an execution visits is live, and live keys are solved.

A reached store is covered at its node _in some context_:
$ exists c, A. quad "lookup"(v, c) = A and s in conc(A). $
The quantifier cannot become universal. Under entry-state routing the test in
`f` is analyzed in one context per recursion depth, and a store with $n = 2$
lies in the bucket of the outer call only. For entry-state policies the
relation $R$ that indexes the buckets is #isaconst("admitted_contexts"), the
instance of the solution-dependent relation of @sec:eq-routing. The
source-level theorem is stated over the context-free collection
#isai("\<C>\<^bsub>\<G>,g,S\<^esub> v"), so this dependence on the solution
does not enter its statement.

== Verdicts <sec:verdicts>

A check has one verdict per node, while the table may hold several contexts
there. Each context's state is classified as proved, refuted or unknown, and
the verdicts are joined in the flat order in which unknown is the top. The
join follows from the existential context of @sec:table: the theorem does not
say which context covers a store, so the node verdict may claim only what
every contributing context claims, and a proved and a refuted context give
unknown. A context whose state denotes no store contributes nothing:
classifying an empty state is vacuous, since every verdict is true of every
store it denotes. The type #isatype("contextual_verdict") keeps that case
apart as `DEAD`, the verdict of a node where no context holds a reachable
state.

Each verdict below has a meaning only under the premises of the theorem
(@tab:headline): the abstract solve terminates, and #isaconst("run_voblint")
returned an answer. It speaks about _covered executions_: finite source
executions of `main` from an initial store in #isaconst("cinit_stores"),
stopped at any point. Except for `DEAD`, the meaning is conditional on
reaching the check:

- `PROVED`: whenever a covered execution reaches the check, the condition
  holds. It does not assert that the check is reached.
- `REFUTED`: whenever a covered execution reaches the check, the condition
  fails. It is not a verified counterexample. The abstraction admits stores no
  run has, so a condition that fails at every admitted store does not imply
  that any admitted store is reached.
- `UNKNOWN`: the abstraction decides neither.
- `DEAD`: the collecting semantics at the node is empty, so no covered
  execution reaches the check. This is the one reachability claim. The other
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

Conditions are evaluated in the VIMP semantics, where division by zero yields
zero (@sec:vimp-vs-c), so a `PROVED` verdict can depend on that convention.
Only the absence of an arithmetic diagnostic at a node excludes zero divisors
there.

`UNKNOWN` and `DEAD` are not a pair of reachability answers. In
@fig:verdict-regions no run reaches either check, yet the interval analysis
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
#isathm("run_voblint_check_sound") finds a listed check with the same condition
at a node where the store is collected, and that check's verdict holds of the
store. The listed check is existential because a source state does not
determine its node, so the statement cannot be read backwards to conclude that
a `DEAD` node is unreached. #isathm("run_voblint_dead_check_unreached") proves
that conclusion forwards instead: every store collected at the node would
satisfy the claim there, and a `DEAD` claim admits none. Arithmetic
diagnostics are stated per node as well. By
#isathm("run_voblint_arithmetic_safe"), a node without a diagnostic has nonzero
divisors in every collected store. A warning only means that the abstraction
could not exclude a zero divisor.

The theorem of @sec:headline answers RQ1 and is K1. Each of its conclusions
rests on one step of this chapter: collection at a simulating node on the
compiler simulation and the trace construction (@sec:chain), coverage by the
published table on the live keys and the readback (@sec:live-keys,
@sec:table), and the verdict conclusions on the join over contexts
(@sec:verdicts). Well-formedness and the closure of the certified keys are
derived. Termination of the abstract solve stays a per-program premise, so the
result is partial correctness, and the delivered tool adds the trusted
components of @sec:trust-boundary. The companion theorems
#isathm("run_voblint_dead_check_unreached") and
#isathm("run_voblint_arithmetic_safe") give `DEAD` and the arithmetic
diagnostic their meaning, and #isathm("certificate_demo_full_certificate")
shows for one program and configuration that the premises can be met, which K4
counts as a non-vacuity witness. @ch:instances compares what the shipped
domains can prove under this theorem, and @ch:executable draws the boundary
between the proved constant and the delivered tool.
