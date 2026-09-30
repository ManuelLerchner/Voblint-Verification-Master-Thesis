#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/math.typ": *
#import "../lib/theorems.typ": theorem
#import "../lib/figures.typ": call-edge, entry-node, intra-edge
#import "../lib/claims.typ": claim-snapshot, snapshot-cluster-of, snapshot-verdict

// A verdict or state of a registered CLI claim (shared/claims.toml), read from
// the checked output rather than typed.
#let _cli(name, cond, col) = {
  let cells = read("/shared/generated/" + name + ".txt")
    .split("\n")
    .map(l => l.trim().split(regex("\s{2,}")))
    .find(c => c.len() == 5 and c.at(2) == cond)
  assert(cells != none, message: "claim " + name + " has no check " + cond)
  raw(cells.at(col))
}

= Equations, Contexts, and Routing <ch:equations>

The previous chapters fixed what each operation of an analysis must guarantee:
@ch:traces reduced soundness to five local obligations on a claim
#isai("cover v c"), @ch:analysis-interface gave the operations an analysis
supplies, and @ch:cooperation combined several analyses into one. This chapter
connects those operations into a whole-program analysis whose result is such a
claim.

For a program without procedures, one abstract state per graph node suffices.
Procedures break this: the same node is reached by different activations, and
merging them loses facts. Voblint therefore keeps one unknown per node and
_context_. Local edges pass values between unknowns of the same context. Calls
are harder, because the context in which the callee runs can depend on an
abstract value that is known only once the caller is solved. The equations
discover such calls while they are solved: each call chooses a context of the
callee from its entry value, sends the entry value there, and reads the
callee's result back at its continuation. We call this choice _routing_, and
the context policy decides it.

The goal is a solution $sol$ that over-approximates the buckets of
@sec:contexts: for every node $v$ and context $c$,
$
  #isai("\<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v c") subset.eq conc_(M)(sol(v, c)),
$
where $conc_(M)$ reads a solved local unknown together with the solved
analysis global: it gives the stores that the local half of $sol(v, c)$
describes jointly with the global half of the analysis global's unknown
(@sec:global-unknowns), and the empty set for unknowns outside the solved set.
The main result (#isathm("activation_collect_dg_sound"), @sec:eq-discharge) shows that every post-solution
of the equations meets this goal, for every domain and context policy,
provided the analysis is sound and the policy routes every concrete call to
a context that the concrete semantics also admits for it (@sec:eq-routing). Whether a solve terminates is a separate premise
(@sec:termination). The
running example is the program of @fig:program-to-equations, repeated in
@fig:eq-running with the names this chapter gives its calls.

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    let pt(pos, name, pp) = node(
      pos,
      [#name #text(size: 6.5pt, fill: vb.muted, raw(pp))],
      stroke: 0.8pt + vb.neutral,
      fill: white,
      corner-radius: 6pt,
      inset: 3.5pt,
    )
    let resume(from, to) = edge(
      from,
      to,
      "-|>",
      stroke: (paint: vb.muted, thickness: 0.7pt, dash: "dotted"),
      label: text(size: 6.5pt, fill: vb.muted)[resumes],
      label-side: right,
      bend: -40deg,
    )
    grid(
      columns: (auto, auto),
      column-gutter: 8mm,
      align: horizon,
      block(width: 56mm, listing(lang: "c", claim: "pg-contexts-entry", ```
      fun bump(n) {
        return n + 1;
      }

      fun main() {
        a = bump(5);
        b = bump(4);
        __voblint_check(a == 6);
        __voblint_check(b == 5);
      }
      ```)),
      diagram(
        spacing: (14mm, 6mm),
        entry-node((0, 0), text(size: 7pt, raw("entry_main"))),
        pt((0, 1), $u_1$, "pp2"),
        pt((0, 2), $u_2 = k_1$, "pp3"),
        pt((0, 3), $k_2$, "pp4"),
        entry-node((1.4, 1), text(size: 7pt, raw("entry_bump"))),
        entry-node((1.4, 2.4), text(size: 7pt, raw("exit_bump"))),
        intra-edge((0, 0), (0, 1)),
        intra-edge((1.4, 1), (1.4, 2.4), label: [return n + 1], label-side: left),
        call-edge((0, 1), (1.4, 1), label: [bump(5)], label-side: left),
        call-edge((0, 2), (1.4, 1), label: [bump(4)], label-side: right),
        resume((0, 1), (0, 2)),
        resume((0, 2), (0, 3)),
      ),
    )
  },
  kind: image,
  placement: none,
  caption: [The running example of this chapter. Call $u_1$ enters `bump`
    with argument 5 and resumes at $k_1$, which is the second call $u_2$. It
    enters `bump` with 4 and resumes at $k_2$, where the checks start. Dashed
    arrows are call edges, dotted ones connect a call with its continuation.],
) <fig:eq-running>

== Context-indexed unknowns <sec:eq-unknowns>

The intraprocedural recipe of @ch:background keeps one unknown per graph node.
Extended naively to calls, the entry of `bump` joins both call sites and holds
$n in {4, 5}$ at best, the return at $k_1$ assigns $a in {5, 6}$, and the check
`a == 6` fails although every execution satisfies it. With the join update rule
(@sec:update-rules) the analyzer without contexts reports exactly this, with the verdicts of
@fig:intro-answers:
#_cli("pg-contexts-none-join", "a == 6", 3) with
#_cli("pg-contexts-none-join", "a == 6", 4). The default rule, warrowing, reports
#_cli("pg-contexts-none", "a == 6", 4)\; its lower bound $-infinity$ comes from
widening the shared entry value (@sec:eq-seed-global). The concrete semantics keeps
the two calls apart: the collecting semantics of @sec:contexts files each
activation of `bump` under its own context. Voblint indexes the unknowns by the
same contexts.

A local unknown is a pair $(v, c)$, the index $[v, c]$ of the claims of
@ch:traces, and $sol(v, c)$ is the state claimed for activations of context $c$
at node $v$. Goblint's local unknowns have the
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L26-L28")[same shape], a node paired
with a context. @fig:eq-unknowns shows the unknowns of the
running example when `main` runs in context $c_0$ and the two calls enter
`bump` in contexts $c_1$ and $c_2$. Each call gets its own copy of `bump`.
Under entry-state contexts the analyzer separates the copies this way and
reports #_cli("pg-contexts-entry", "a == 6", 3) for `a == 6` with
#_cli("pg-contexts-entry", "a == 6", 4), and likewise for `b == 5`.

#let _loc(pos, body) = node(
  pos,
  text(0.8em, body),
  stroke: 0.7pt + vb.accent,
  fill: vb.accent.lighten(93%),
  corner-radius: 2pt,
  inset: 4pt,
)
#let _seed(pos, body) = node(
  pos,
  text(0.8em, body),
  stroke: 0.7pt + vb.called,
  fill: vb.called.lighten(93%),
  corner-radius: 7pt,
  inset: 4pt,
)
#let _read(a, b, lab, side: left) = edge(
  a,
  b,
  "-|>",
  stroke: 0.7pt + vb.neutral,
  label: text(7.5pt, fill: vb.neutral, lab),
  label-side: side,
)
#let _pub(a, b, lab, side: left) = edge(
  a,
  b,
  "-|>",
  stroke: (paint: vb.called, thickness: 0.7pt, dash: "dashed"),
  label: text(7.5pt, fill: vb.called, lab),
  label-side: side,
)

#let _b = $italic("bump")$

#figure(
  placement: none,
  diagram(
    spacing: (18mm, 8mm),
    _seed((0, 0), $italic("Seed")(#_b, c_1)$),
    _loc((0, 1), $(ctor("FunctionEntry") thin #_b, c_1)$),
    _loc((0, 2), $(ctor("FunctionResult") thin #_b, c_1)$),
    _loc((1.3, 0), $(u_1, c_0)$),
    _loc((1.3, 2), $(k_1, c_0) = (u_2, c_0)$),
    _loc((1.3, 5), $(k_2, c_0)$),
    _seed((2.6, 3), $italic("Seed")(#_b, c_2)$),
    _loc((2.6, 4), $(ctor("FunctionEntry") thin #_b, c_2)$),
    _loc((2.6, 5), $(ctor("FunctionResult") thin #_b, c_2)$),
    _read((1.3, 0), (1.3, 2), [caller]),
    _read((1.3, 2), (1.3, 5), [caller], side: right),
    _read((0, 0), (0, 1), [seed read], side: right),
    _read((0, 1), (0, 2), [local], side: right),
    _read((0, 2), (1.3, 2), [result], side: right),
    _read((2.6, 3), (2.6, 4), [seed read]),
    _read((2.6, 4), (2.6, 5), [local]),
    _read((2.6, 5), (1.3, 5), [result]),
    _pub((1.3, 2), (0, 0), $n = 5$, side: right),
    _pub((1.3, 5), (2.6, 3), $n = 4$),
  ),
  caption: [Unknowns of the running example when the two calls reach
    different contexts $c_1 != c_2$ (`main` runs in $c_0$). A solid arrow: the
    right-hand side at its head reads the unknown at its tail. A dashed arrow:
    the right-hand side at its tail publishes to the global unknown at its head.
    Under the unit context the two copies coincide and one seed receives both
    publications. Drawn from the equation definitions.],
) <fig:eq-unknowns>

== Interprocedural equations <sec:eq-call>

For a post-solution to cover the bucket of $(v, c)$, the right-hand side of
$(v, c)$ must join everything that can reach $v$ in context $c$
(#isaconst("routed_node_rhs")). Schematically,
$
  italic("rhs")(v, c) = italic("init")(v) union.sq
  lJoin_(u ->^a v) sh(f)_a (sol(u, c)) union.sq
  lJoin_(u in italic("calls")(v)) italic("call")_u (c) union.sq
  italic("seed")(v, c):
$
the initial state if $v$ is the program entry, the transfer along each
incoming local edge, the contribution $italic("call")_u (c)$ of each call node
$u$ whose continuation is $v$ (the set $italic("calls")(v)$), and the seed if
$v$ is a callee entry. A transfer that uses analysis globals also
reads and publishes them (@sec:manager).

Local edges keep the context. An activation keeps its context from entry to
return (@sec:contexts), so a local edge never changes it, and #oblig("INTRA")
follows from edge-transfer soundness before any context
policy is chosen.

A call follows the protocol of @sec:calls (@fig:eq-protocol). Its contribution
reads the caller's value at $(u, c)$ and applies the entry operation, which
yields the resume value $q$ and the entry value $e$. The entry value selects
the callee context $c' = ctxh(u, c, e)$. The call publishes $e$ to the callee's
entry in $c'$, reads the callee's result $r$ at $c'$, and returns the combined
value to $(k, c)$. In @fig:eq-unknowns the continuation $(k_1, c_0)$ reads
$(u_1, c_0)$, publishes $n = 5$ to the seed of `bump` in $c_1$ and reads the
result there.

When the entry value is bottom, no store enters the callee. The call then
publishes nothing, reads no result, and combines $q$ with a bottom callee
result. Apinis et al. add the same test so that procedures which are not called
are not analyzed @apinis12 (TODO: check locator), and Goblint's
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L244")[call handling] applies it
as well. The test needs one assumption of the routed locale: a value it
classifies as bottom concretizes to the empty set.

#let _step(pos, body) = node(
  pos,
  text(0.8em, body),
  stroke: 0.6pt + vb.neutral,
  fill: white,
  corner-radius: 2pt,
  inset: 4pt,
)
#let _p = $p$

#figure(
  placement: auto,
  diagram(
    spacing: (16mm, 7.5mm),
    _loc((0, 0), $(u, c)$),
    _step((0, 1), $enterh: (q, e)$),
    _step((1.2, 1), $c' = ctxh(u, c, e)$),
    _seed((1.2, 2), $italic("Seed")(#_p, c')$),
    _loc((2.4, 2), $(ctor("FunctionEntry") thin #_p, c')$),
    _loc((2.4, 3.4), $(ctor("FunctionResult") thin #_p, c')$),
    _step((0, 4.4), $combineassignh(combineenvh(q, r), r)$),
    _loc((0, 5.4), $(k, c)$),
    _read((0, 0), (0, 1), [caller value], side: right),
    _read((0, 1), (1.2, 1), $e$),
    _pub((1.2, 1), (1.2, 2), [publish $e$], side: left),
    _read((1.2, 2), (2.4, 2), [seed read]),
    edge(
      (2.4, 2),
      (2.4, 3.4),
      "-|>",
      stroke: (paint: vb.neutral, thickness: 0.7pt, dash: "dotted"),
      label: text(7.5pt, fill: vb.neutral)[callee body],
      label-side: left,
    ),
    _read((2.4, 3.4), (0, 4.4), $r$),
    _read((0, 1), (0, 4.4), $q$, side: right),
    _read((0, 4.4), (0, 5.4), [joined into], side: right),
  ),
  caption: [One call at node $u$ in context $c$, contributing to its
    continuation $(k, c)$. The entry operation turns the caller value into a
    resume value $q$ and an entry value $e$, and $e$ selects the callee context
    $c'$. The call publishes $e$ to the seed of $(#_p, c')$ (dashed) and reads
    the callee's result $r$ at $c'$. All steps except the callee body belong to
    the right-hand side of $(k, c)$. The callee's unknowns have their own
    equations.],
) <fig:eq-protocol>


== Dynamic call routing <sec:eq-seed>

Which unknown a call reads last depends on the value it read first: the callee
context $c'$ is computed from the entry value. The equations therefore cannot
wire callers to callee entries in advance. For the same reason the entry
unknown $(ctor("FunctionEntry") thin p, c')$ cannot list its contributors,
because which call sites route to $c'$ is known only once their callers are
solved. Side-effecting systems reverse the direction: each caller contributes
to the callee's entry while it evaluates its own equation (@ch:background).

Voblint adds one _seed_ $italic("Seed")(p, c')$ per callee entry and context.
Every call routed to $(p, c')$ publishes its entry value $e$ to the seed, and
the entry reads the seed back, so a post-solution satisfies
$
  e lle sol(italic("Seed")(p, c')) quad "and" quad
  sol(italic("Seed")(p, c')) lle sol(ctor("FunctionEntry") thin p, c')
$
(#isathm("routed_seed_publish_bound_seed"), #isathm("routed_seed_read_bound")).
The seed thus collects every entry value routed to $(p, c')$. Routing and
publication use the same value $e$. A route computed from any other value,
such as the caller's own state, could file the seed under a context the entry
value does not belong to, because entry changes the state, for instance by
binding the formals. A call's contribution names the callee's unknowns and
never enters the callee, so recursion needs no special case.

== Relating routing to concrete activations <sec:eq-routing>

The equations route calls by abstract entry values, while #oblig("CALL") and
#oblig("TOTAL") speak about the relation $R$ of @sec:contexts, which admits
contexts for concrete calls. Two per-instance obligations connect them.
_Adequacy_: whenever $R$ admits $c'$ for a real call from a covered caller
store $s$, the entry answer $(q, e)$ covers $s$ and the entered store
(@sec:calls), its entry value routes to exactly $c'$, and the callee entry at
$c'$ is solved. _Totality_: every covered call admits some context.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    stroke: none,
    table.hline(),
    [*policy*], [*callee context*], [*relation $R$*],
    table.hline(stroke: 0.5pt),
    [unit], [always $()$ (#isaconst("route_unit"))],
    [graph of #isaconst("enterc_unit")],
    [call strings], [site and caller context (#isaconst("cs_route"))],
    [graph of #isaconst("cs_context")],
    [entry states], [the formals' abstract values in $e$ \ (#isaconst("formals_context"))],
    [read off the solution \ (#isaconst("admitted_contexts"))],
    table.hline(),
  ),
  placement: none,
  caption: [The three context policies. The first two are _functional_: the
    context ignores abstract values, and $R$ is the graph of the same function
    on concrete calls.],
) <tab:eq-policies>

For a functional policy $R$ is the graph of the context function on concrete
calls (#isaconst("call_context_rel_of_fun")), so totality is immediate. For
call strings, the concrete function applies the same term as the route
(#isathm("cs_route_context_agree")), so the entry value routes to the admitted
context. The rest of adequacy is the entry coverage of @sec:calls and closure
of the solved unknowns.

An entry-state context is the list of abstract values of the callee's formal
parameters in the entered state, an instance of the partial contexts of Apinis
et al. @apinis12 (TODO: check locator). Such a context cannot be computed from the concrete call.
If the entry value computed from the caller's solved value maps $n$ to
$[4, 5]$, a concrete call with $n = 4$
is routed to the context $[4, 5]$, while abstracting its own entered store
gives $[4, 4]$, a context at which no seed was published. The relation
#isaconst("routed_entry_context_rel") therefore reads the contexts off the
solution: it admits $c'$ for a concrete call exactly when the entry answer at
the caller's solved value covers the call and routes to $c'$. Adequacy then
holds by definition and closure, and totality is entry coverage. The
context-indexed collecting semantics is thus indexed by the analyzer's own
solution. The source-level theorem of @ch:results is stated over the
context-free collecting semantics, so this dependence does not reach it.

The policy decides which calls share an unknown, and with it what the analysis
can prove (@fig:eq-policies). A call string of length one keeps the two calls
of `wrap` apart but merges them in `scale`, because both arrive from the same
site. Length two and entry-state routing keep them apart down to `scale`.
@sec:eval-rq4 reports a machine-checked strict separation of this kind between
lengths one and two for one program.

#let _policy(name, title) = {
  let s = claim-snapshot(name)
  let procs = ("main", "wrap", "scale")
  let shown = s.clusters.filter(c => c.proc in procs)
  let ctxlabel(c) = {
    let t = c.ctx
    if t == "root context" { "root" } else if t.starts-with("call-string=") {
      t.slice("call-string=".len())
    } else { t }
  }
  let pos = (:)
  for (row, p) in procs.enumerate() {
    let copies = shown.filter(c => c.proc == p)
    for (i, c) in copies.enumerate() {
      pos.insert(c.id, (i - (copies.len() - 1) / 2, row))
    }
  }
  let pairs = ()
  for e in s.edges.filter(e => e.label.starts-with("enter ")) {
    let a = snapshot-cluster-of(s, e.src)
    let b = snapshot-cluster-of(s, e.dst)
    if a != none and b != none and a.id in pos and b.id in pos {
      // Calls from several sites into one copy share an arrow and list the sites.
      let site = s.nodes.at(e.src).label
      let i = pairs.position(p => p.at(0) == a.id and p.at(1) == b.id)
      if i == none { pairs.push((a.id, b.id, site)) } else if not pairs.at(i).at(2).contains(site) {
        pairs.at(i).at(2) += ", " + site
      }
    }
  }
  let check = s.nodes.values().find(n => "check a == 2" in n.lines)
  let state = check.lines.find(l => l.starts-with("a="))
  let verdict = snapshot-verdict(s, "a == 2")
  let tone = if verdict == "PROVED" { vb.proved } else { vb.unstable }
  block(width: 100%, {
    align(center, text(size: 8pt, weight: "bold", title))
    v(2pt)
    align(center, diagram(
      spacing: (19mm, 7mm),
      ..shown.map(c => node(
        pos.at(c.id),
        text(size: 7pt)[#c.proc \ #raw(ctxlabel(c))],
        shape: rect,
        stroke: 0.6pt + vb.accent,
        fill: vb.accent.lighten(93%),
        corner-radius: 2pt,
        inset: 3pt,
      )),
      ..pairs.map(((a, b, site)) => edge(
        pos.at(a),
        pos.at(b),
        "-|>",
        stroke: 0.6pt + vb.called,
        label: text(size: 7pt, fill: vb.called, raw(site)),
        label-sep: 1pt,
      )),
    ))
    v(2pt)
    align(center, text(size: 7.5pt)[`a == 2`: #text(fill: tone, verdict), #raw(state)])
  })
}

// The call site of a call as the analyzer numbers it, so the caption cannot
// drift from the graph it describes.
#let _site(call) = {
  let s = claim-snapshot("ctx-demo-k2")
  raw(s.nodes.at(s.edges.find(e => e.label == "enter " + call).src).label)
}

#figure(
  {
    set par(first-line-indent: 0pt, justify: false)
    grid(
      columns: (1fr, 1fr),
      column-gutter: 8pt,
      row-gutter: 10pt,
      _policy("ctx-demo-none", [no contexts]), _policy("ctx-demo-entry", [entry states]),
      _policy("ctx-demo-k1", [call strings, length 1]),
      _policy("ctx-demo-k2", [call strings, length 2]),
    )
  },
  kind: image,
  placement: auto,
  caption: [Procedure copies under four context policies for the playground's
    default program (@fig:pg-overview): `scale(v)` returns `2 * v`, `wrap(w)`
    returns `scale(w)` from #_site("scale(w)"), and `main` calls `a = wrap(1)`
    at #_site("wrap(1)") and `b = wrap(4)` at #_site("wrap(4)"), then checks
    `a == 2`. Boxes are procedure copies labelled with their contexts as the
    analyzer prints them (`root` is the initial context of `main`), arrows
    calls labelled with their sites. Read from
    the analyzer's solved graph (Interval, claims `ctx-demo-*`).],
) <fig:eq-policies>

== Soundness of the generated system <sec:eq-discharge>

The equations were built so that $sol(v, c)$ covers the bucket of $c$ at $v$.
The routed locale #isalocale("routed_context_base_hetero") proves this for
every post-solution, discharging the five obligations once for all policies
and domains. Adequacy and totality are assumptions of that locale.

#theorem(name: [Routed collecting soundness], isa: "activation_collect_dg_sound")[
  Every post-solution $sol$ of the generated system satisfies
  #isai("\<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v c") $subset.eq
  conc_(M)(sol(v, c))$ for every node $v$ and context $c$, and the left-hand
  side is empty outside the solved set, provided: the solved set contains the
  program entry in the initial context and is closed under local edges and call
  continuations; the initial abstract state covers the initial stores; the
  specification satisfies the analysis soundness contract
  #isalocale("analysis_contract"); the callee list the generator uses at each
  call site includes every callee a covered call can enter; and routing is
  adequate and total.
]

The statement paraphrases the lemma together with the assumptions of its
locale. "Post-solution" means a bound on the solved set only: every local
right-hand side and every publication there is bounded by $sol$
(#isaconst("post_bounded")), and closure is the separate premise above. The
statement omits the soundness of the bottom test of @sec:eq-call,
well-formedness of the generated programs, and assumptions that every compiled
program satisfies: finitely many local and call edges, one call edge per call
node (#isaconst("calls_source_unique")), and seeds distinct from the global
unknown of the analysis's own globals. Closure under local edges is required
only from unknowns whose claim is nonempty. The analyzer's specification meets the contract through
#isathm("dg_spec_of_contract") (@sec:whole-state), and the theorem uses nothing
else about the analysis. The functional policies reach the analyzer through
#isathm("fun_route_activation_collect_sound"), the entry-state policy through
#isathm("entry_state_activation_collect_sound"). @tab:eq-obligations shows where
each obligation comes from.

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    stroke: none,
    table.hline(),
    [*obligation*], [*where the equations meet it*],
    table.hline(stroke: 0.5pt),
    [#oblig("INIT")], [the initial state joined at the program entry],
    [#oblig("INTRA")], [the local-edge terms, at a fixed context],
    [#oblig("CALL")],
    [the call publishes $e$ to the seed, the post-solution
      bounds the seed, and the callee entry reads it],
    [#oblig("RETURN")],
    [the call reads the result at the context $c'$ that
      adequacy returns and combines it with $q$],
    [#oblig("TOTAL")], [routing totality],
    table.hline(),
  ),
  placement: auto,
  caption: [How the generated equations discharge the five obligations of
    @ch:traces in #isathm("activation_collect_dg_sound").],
) <tab:eq-obligations>

== Encoding the equations in the solver <sec:eq-encoding>

The construction above is independent of how the equations are solved. This
section describes how it is represented for the reused TD solver of
@sec:td.

=== Value-dependent reads <sec:eq-trees>

A call reads an unknown chosen by a value it read first, so the solver must see
the reads one at a time. The reused solver therefore takes each right-hand side
as a strategy tree (#isatype("strategy_tree"), @sec:td). The
generator writes each contribution as a small program over reads of unknowns
(#isatype("strategy_program")), joins their results and compiles them into one
tree. For a single callee the call contribution (#isaconst("routed_callee_call_program")) is
$
  italic("call") & = #ctor("QueryL") thin (u, c) thin (lambda d. thick t_(q, e)),
                   quad (q, e) = enterh(d), \
        t_(q, e) & = #ctor("Side") thin (italic("Seed")(p, c'), e) thin
                   (#ctor("QueryL") thin (ctor("FunctionResult") thin p, c') \
                 & #h(4em) (lambda r. thick
                     #ctor("Answer") thin combineassignh(combineenvh(q, r), r)))
$
with $c' = ctxh(u, c, e)$, plus the bottom test of @sec:eq-call. The entry
operation is itself a small program, since it may read analysis globals. The
solver records the reads of each evaluation and re-evaluates their readers
when a value grows (@sec:td).

=== Activation seeds <sec:eq-seed-global>

Apinis et al. side-effect the entered state directly into the start unknown of
the callee @apinis12 (TODO: check locator), and Goblint does the same with a side effect on a local
unknown. The reused solver's #ctor("Side") targets global unknowns only, and
adding local side effects would mean forking the solver and redoing its
partial-correctness proof, so the seed is a global unknown. Publishing does not
make the solver analyze the callee: #ctor("Side") joins its value into the seed
and destabilizes the seed's readers, and the solver demands an unknown only
when some right-hand side reads it. The callee is demanded by the result read
that follows the publication. Solving that unknown reaches the entry through
local dependencies, and the entry equation reads the seed, which the
publication has already filled. The regressions
#isathm("w0_seed_at_entered_frame") and #isathm("w0_no_seed_at_caller_frame")
evaluate one call whose entry reads a global: the seed is published at the
context of the entered frame and nowhere else.

Being a global unknown, a seed is merged with the update rule selected for
global unknowns, so under a warrowing rule it can be widened. In the example
without contexts the first call contributes ${n |-> [5, 5]}$ to the one seed of
`bump` and the second ${n |-> [4, 4]}$. Their join is not below ${n |-> [5, 5]}$,
so the rule widens the lower bound to $-infinity$. Neither contribution changes
afterwards, and the rule leaves the seed untouched when an origin repeats its
contribution, so no narrowing step recovers the bound. No operational
equivalence with Goblint's fixpoint is claimed. @app:goblint-alignment records
the deviation.

=== Global unknowns and the manager <sec:global-unknowns>

Seeds are not the only global unknowns. An analysis global of
@sec:analysis-globals is one as well. Goblint also keeps
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L55",
)[one global unknown per function]
next to the analysis's globals, but its value is the set of contexts the
function is called in, not an entry state. Voblint names its global unknowns
by the datatype #isatype("global_unknown"): #isaconst("Analysis_Global") wraps
the name of an analysis global, and #isaconst("Activation_Seed") is the seed of
@sec:eq-seed for one callee entry and context.

The vendored solver requires all unknowns to share one value type, whereas
local unknowns and analysis globals range over different domains. Every unknown
therefore holds a pair #isatype("dg_state") of a local and a global component,
#isaconst("dg_local") and #isaconst("dg_global"). A local unknown
or a seed uses the local half, an analysis global the global half, and the
unused half is $lbot$. Transfers never see the pair: #isaconst("man_local") and
#isaconst("man_global") hand them the half they need. Goblint's solvers also
need one value type and use a #link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/constraint/translators.ml#L30")[lifted sum] of the two lattices
instead. Voblint deviates here on purpose. A sum needs an extra top element where a
local and a global value meet, and every proof that reads an unknown would have
to handle it. With the pair, all lattice operations work componentwise, so the
solver's requirements on the value type follow from those on the two halves.

The manager of @sec:manager maps the name of an analysis global to its global
unknown. In the manager #isaconst("mk_dg_man") builds, #isaconst("man_global")
$v$ compiles to a #ctor("QueryG") of that unknown, and #isaconst("man_sideg")
$v$ $g$ compiles to a #ctor("Side") to it. A transfer names its analysis
globals and never their global unknowns, so the framework's seeds are out of
its reach. The analyses of this thesis keep program globals in the
flow-sensitive local state. @sec:mixed-flow shows a lifter that keeps them in
an analysis global instead, proved sound at the level of the analysis
soundness contract.

=== One publication per global unknown <sec:eq-buffer>

A right-hand side can publish to the same global unknown twice, for instance
when every incoming edge of a node publishes the analysis global
(@sec:mixed-flow). The update rules record the latest contribution of each
origin, the unknown whose equation published (@sec:update-rules), so the second
publication replaces the first, and under a warrowing rule the two can
alternate without converging. The regression theory defines such an unbuffered
equation but does not evaluate it, and this non-termination is not proved.
#isaconst("buffer_sides") therefore joins the publications of one right-hand
side per global unknown and flushes each once.
#isathm("keyed_multiwrite_buffered_terminates") shows by evaluation, on a
two-edge example, that the buffered version terminates under the warrowing
rule, and for a node with two
predecessor edges #isathm("merge_global_value") shows that the flushed value is
the join of both contributions. The executable analyses run the buffered generator. The
soundness proof speaks about the direct one, and
#isathm("part_post_solution_routed_node_rhs_buffered") transfers the
certificate between them. Whether the two schedules reach the same solution is
left to the regression corpus.

@ch:solving proves that a terminating solve returns a
post-solution of the generated equations, which is what the theorem of
@sec:eq-discharge consumes.
