#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig, thy-badge
#import "../lib/math.typ": *
#import "../lib/theorems.typ": theorem
#import "../lib/figures.typ": call-edge, entry-node, intra-edge, verdict as verdict-chip
#import "../lib/claims.typ": (
  claim-ref, claim-snapshot, claim-trace, snapshot-cluster-of, snapshot-verdict,
)
#import "../lib/sources.typ": proved, thy

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

@ch:traces reduced soundness to a cover, which assigns to every node $v$
and context $c$ a set of stores #isai("cover v c"), and stated five local
obligations under which the cover contains every store that an execution
brings to $v$ in context $c$. @ch:analysis-interface and @ch:cooperation stated what an analysis supplies
and proves. What is still missing is a way to compute such a cover.
This chapter turns the procedure-aware graph of @ch:program-model into a
system of equations and shows that every post-solution induces a sound cover.

Precisely, every post-solution $sol$ of the equations should satisfy
$
  #isai("\<A>\<^bsub>\<G>,adm,c₀,g,S\<^esub> v c") subset.eq conc_(M)(sol(v, c))
$
at every node $v$ and context $c$. The left side is the activation collecting
semantics of @sec:contexts, and $conc_(M)(sol(v, c))$ is the set of stores
that the solved abstract state at $(v, c)$ describes under the solved values
of the analysis globals (@sec:sound-core). For the edges inside a procedure,
the equations follow the graph directly. A call is harder, since the equations
must also determine which context of the callee it enters. Under entry-state
policies, this context is computed from the abstract state at the call, which
is known only while the equations are being solved.

== Unknowns and right-hand sides #thy-badge("Voblint_Framework", "DG_Indexed_Generator") <sec:eq-call>

Separate contexts give the activations of `bump(5)` and `bump(4)` separate
copies of `bump`, so the first result stays exactly $6$ (@sec:interproc).

Voblint therefore indexes the unknowns of the equations by contexts. For every
node $v$ and context $c$ there is a _local_ unknown $(v, c)$, whose value
$sol(v, c)$ is the abstract state for the activations of context $c$ at $v$.
These are the indices of the cover. Goblint's local unknowns have the
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L26-L28")[same shape] @apinis14[§5.2].
Besides the local unknowns, the equations have _global_ unknowns without a
program point (@sec:td). They hold the analysis globals of @sec:shared-facts
and the entry states that calls publish to their callees.

The equation of $(v, c)$ has to collect every abstract state that can reach
$v$ in context $c$, because a post-solution must cover every store that
reaches $v$ there. Such states come from four sources: the initial state at
the program entry, the transfer along each local edge into $v$, the result of
each call that returns to $v$, and, at a procedure entry, the entry states that
calls publish to it. An entry state is the abstract state in which the callee
starts, for example with its formal parameters bound to the abstract values of
the call's arguments (@sec:calls). Along an edge inside a procedure, the
activation keeps its context (@sec:contexts), so the second source applies the
transfer to the predecessor's value in the same context $c$. A callee, however,
runs in a context of its own.

As in @sec:constraints, a right-hand side reads the current values of other
unknowns from a _valuation_, which assigns a value to every unknown. Given a
valuation $tau$, the generated right-hand side #isaconst("routed_node_rhs") of
$(v, c)$ computes exactly the join of the four sources:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  proved("routed_node_rhs_parts")
}
Here $scripts(⨆)_(x <- italic("xs")) f(x)$ joins $f(x)$ over the list
$italic("xs")$, and the empty join is $lbot$. The lists range over the local
edges into $v$ and over the calls that return to $v$. The parts
#isaconst("rhs_init"), #isaconst("rhs_edge"), #isaconst("rhs_call"), and
#isaconst("rhs_seed") are the four sources in this order. A post-solution $sol$ assigns $(v, c)$ a value at least as large as this join.
Since $conc_M$ is monotone, $conc_(M)(sol(v, c))$ therefore contains the stores
that each source describes. Publications to analysis globals
(@sec:shared-facts) are side effects of the right-hand side and do not enter
this join.

At a call, the analyzer chooses the callee's context with a _routing_ function
$ctxh(u, c, e)$ of the call node $u$, the caller context $c$, and the entry
state $e$. Under entry-state contexts the choice depends on $e$, which is
known only while the equations are solved. The set of calls that contribute to
a particular callee context is therefore not known in advance, and the
callee's entry cannot list them in its equation. Each call instead publishes
its entry state to the callee as a side effect (@sec:side-effects).

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

#let _step(pos, body) = node(
  pos,
  text(0.8em, body),
  stroke: 0.6pt + vb.neutral,
  fill: white,
  corner-radius: 2pt,
  inset: 4pt,
)
#figure(
  placement: auto,
  scale(80%, reflow: true, diagram(
    spacing: (11mm, 6.5mm),
    _loc((2.8, 0), $(italic("pp2"), c_0)$),
    _loc((2.8, 4.2), $(italic("pp3"), c_0)$),
    _step((1.4, 0.9), $enterh: (q_1, e_1)$),
    _step((1.4, 1.9), [route: $c_1$]),
    _seed((0, 1.9), $ctor("Activation_Seed") thin #_b space c_1$),
    _loc((0, 2.9), $(ctor("FunctionEntry") thin #_b, c_1)$),
    _loc((0, 3.9), $(ctor("FunctionResult") thin #_b, c_1)$),
    _step((1.4, 4.2), $sh("combine")(q_1, r_1)$),
    _read((2.8, 0), (1.4, 0.9), [caller value], side: right),
    _read((1.4, 0.9), (1.4, 1.9), $e_1$, side: left),
    _pub((1.4, 1.9), (0, 1.9), [publish $e_1$], side: left),
    _read((0, 1.9), (0, 2.9), [seed read], side: right),
    _read((0, 2.9), (0, 3.9), [body], side: right),
    _read((0, 3.9), (1.4, 4.2), $r_1$, side: right),
    edge(
      (1.4, 0.9),
      (1.4, 4.2),
      "-|>",
      bend: 50deg,
      stroke: (paint: vb.neutral, thickness: 0.6pt, dash: "dotted"),
      label: text(7.5pt, fill: vb.neutral, $q_1$),
      label-side: left,
    ),
    _read((1.4, 4.2), (2.8, 4.2), [joined], side: left),
    node(
      enclose: ((2.8, 0), (2.8, 4.2)),
      stroke: 0.5pt + vb.muted,
      fill: vb.muted.lighten(94%),
      corner-radius: 4pt,
      inset: 8pt,
      name: <ctx-main>,
    ),
    node((2.8, -0.75), text(7pt, fill: vb.muted)[`main`, $c_0$], stroke: none),
    node(
      enclose: ((0, 2.9), (0, 3.9)),
      stroke: 0.5pt + vb.muted,
      fill: vb.muted.lighten(94%),
      corner-radius: 4pt,
      inset: 8pt,
      name: <ctx-bump>,
    ),
    node((0, 4.6), text(7pt, fill: vb.muted)[`bump`, $c_1$], stroke: none),
  )),
  caption: [The first call of the running example under entry-state contexts.
    The right-hand side of the continuation $(italic("pp3"), c_0)$ reads the
    caller's value, applies enter, routes the entry state $e_1$ to $c_1$,
    publishes it to the seed of `bump` in $c_1$ (purple, dashed), reads the
    result in the same context and joins the combined state into its own value.
    Blue boxes are local unknowns, the purple box is a global unknown, white
    boxes are steps of the right-hand side, and gray frames group the unknowns
    of one procedure in one context.],
) <fig:eq-unknowns>

@fig:eq-unknowns follows the first call of the running example. The equation
of its continuation, $(italic("pp3"), c_0)$, connects the caller and the
callee. It reads the caller's value at $(italic("pp2"), c_0)$ and applies
enter (@sec:calls), which yields an _entry pair_ of a resume state $q_1$ and an
entry state $e_1$ that binds $n$ to $[5, 5]$. The entry state selects the
callee context $c_1 = [[5, 5]]$. The equation publishes $e_1$ to that context,
reads the result $r_1$ of `bump` in $c_1$, and joins
$sh("combine")(q_1, r_1)$ into its own value. The equation of the second
call's continuation, $(italic("pp4"), c_0)$, does the same with
$c_2 = [[4, 4]]$. The two calls thus use separate copies of `bump`, and the
first result stays exactly 6.

In this protocol, the caller's equation publishes the entry state to the callee
and reads the callee's result. The verified solver, however, accepts side effects
only to global unknowns (@sec:eq-seed-global), so a call cannot publish to the
local unknown of the callee's entry directly. Each callee entry $p$ and context
$c'$ therefore has a global unknown, the _seed_
$ctor("Activation_Seed") thin p space c'$ (#isatype("global_unknown")). Every
call routed to $(p, c')$ publishes to it, and the equation of
$(ctor("FunctionEntry") thin p, c')$ reads it. A call with several callees, or
an enter that returns several entry pairs, routes and publishes each pair
separately.

Since a caller reads nothing of the callee except its result, a recursive call
needs no special treatment. Its equation reads a result that in turn depends on
the caller's own unknowns, so the dependencies form a cycle. The solver handles
this cycle like the cycle of a loop and widens at the unknown where a read
closes it (@sec:td).

The right-hand side handles one special case. A call whose entry state is
bottom publishes nothing and does not read the callee's result. No store enters the callee in that case, and the read would
only make the solver evaluate the callee's body from a state that describes no
store. Goblint's normal-call transfer
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L244-L245",
)[skips]
bottom entry states in the same way. Skipping them is sound because a state
classified as bottom is required to have an empty concretization
(#isathm("routed_context.is_bot_sound", thy: "Routed_Context", display: "is_bot_sound")).

== Routing and context policies #thy-badge("Voblint_Framework", "Routed_Context") <sec:eq-routing>

Every call is assigned a callee context twice. The equations choose one from
the abstract entry state, and the concrete semantics of @ch:traces chooses one
from the concrete call, through the context policy $italic("adm")$ of
@sec:contexts. The unknowns of a context only receive what the equations send
there, but they must describe every concrete activation that the policy admits
in it. The two choices must therefore agree. In the running example, the
policy admits the activation of `bump` with $n = 5$ in the context $[[5, 5]]$,
and the call `bump(5)` sends an entry state with $n = 5$ to the same context.
In general, whenever the policy admits a concrete call in a context, the
equations must send an entry pair that describes the call to that context
(@fig:eq-adequacy). For a caller store $s$ that the caller's solved value
describes and the store $s'$ in which the callee starts:
$
  italic("adm") "admits" c' "for" (s, s') quad ==> quad & "some entry pair" (q, e) "is routed to" c' \
                                                        & "with" s in conc(q) "and" s' in conc(e).
$
#figure(
  placement: auto,
  {
    set text(size: 8pt)
    diagram(
      spacing: (14mm, 6mm),
      node((0, -0.8), text(fill: vb.muted)[concrete], stroke: none),
      node((2, -0.8), text(fill: vb.muted)[abstract], stroke: none),
      _loc((0, 0), [caller store $s$]),
      _loc((0, 1.4), [entered store $s'$]),
      _step((2, 0), [resume state $q$]),
      _step((2, 1.4), [entry state $e$]),
      _loc((1, 2.8), [context $c'$]),
      edge(
        (0, 0),
        (0, 1.4),
        "-|>",
        stroke: 0.6pt + vb.neutral,
        label: text(7pt)[call],
        label-side: right,
      ),
      edge(
        (2, 0),
        (2, 1.4),
        "-|>",
        stroke: 0.6pt + vb.neutral,
        label: text(7pt)[enter],
        label-side: left,
      ),
      edge(
        (0, 0),
        (2, 0),
        "-",
        stroke: (paint: vb.accent, dash: "dashed", thickness: 0.6pt),
        label: text(7pt)[$s in conc(q)$],
      ),
      edge(
        (0, 1.4),
        (2, 1.4),
        "-",
        stroke: (paint: vb.accent, dash: "dashed", thickness: 0.6pt),
        label: text(7pt)[$s' in conc(e)$],
      ),
      edge(
        (0, 1.4),
        (1, 2.8),
        "-|>",
        stroke: 0.6pt + vb.neutral,
        label: text(7pt)[$italic("adm")$ admits],
        label-side: right,
      ),
      edge(
        (2, 1.4),
        (1, 2.8),
        "-|>",
        stroke: 0.6pt + vb.called,
        label: text(7pt)[routed, published],
        label-side: left,
      ),
    )
  },
  caption: [Adequacy. If the concrete semantics assigns a call to $c'$ (left),
    the equations must route a covering entry pair to the same $c'$ (right).],
) <fig:eq-adequacy>

We call this condition _adequacy_
(#isathm("routed_context.routing_adequate", thy: "Routed_Context", display: "routing_adequate")).
It also requires the callee's entry unknown in $c'$ to be in the solved set.
#oblig("CALL") and #oblig("RETURN") rely on adequacy, because the call
publishes $e$ and its continuation reads the callee's result in the same
context $c'$. Adequacy says nothing about a call to which $italic("adm")$
assigns no context. Such a call would disappear from the context-indexed
collecting semantics, which #oblig("TOTAL") of @sec:contract rules out. The
second condition, _totality_
(#isathm("routed_context.routing_total", thy: "Routed_Context", display: "routing_total")),
is what #oblig("TOTAL") asks of the generated equations. It requires
$italic("adm")$ to admit at least one context for every concrete call from a
store that the caller's solved value describes. Both conditions are premises of
the soundness theorem and are proved once for each context policy.

#figure(
  {
    table(
      columns: (auto, auto, auto, auto),
      align: (left, left, left, left),
      inset: (x: 5pt, y: 4pt),
      stroke: none,
      table.hline(),
      [*policy*], [*$italic("adm")$ admits $c'$ iff*], [*routed to*], [*why they agree*],
      table.hline(stroke: 0.5pt),
      [unit], [$c' = ()$], [$()$], [both constant],
      [call strings], [$c' = "take"_k (u dot c)$], [$"take"_k (u dot c)$], [the same term],
      [entry states],
      [$c' = e|_"formals"$, $(q, e)$ covers $(s, s')$],
      [$e|_"formals"$],
      [$italic("adm")$ reads the routing],
      table.hline(),
    )
  },
  placement: none,
  caption: [The contexts $italic("adm")$ admits for a call at site $u$ from
    caller context $c$ with caller store $s$ and entered store $s'$, where the
    equations route the entry state $e$, and why the two agree. $u dot c$ prepends the
    site, $"take"_k$ keeps the first $k$ entries, $e|_"formals"$ lists the
    formals' values in $e$, and an entry pair
    $(q, e)$ of the caller's solved value covers $(s, s')$ when
    $s in conc(q)$ and $s' in conc(e)$. Unit and call strings are
    _functional_ policies, since they choose the context without reading
    abstract states.],
) <tab:eq-policies>

For unit and call strings the correspondence is direct, as the last column of
@tab:eq-policies shows. $italic("adm")$ admits exactly the context that the
routing function computes for the call, which does not depend on $e$
(#isaconst("context_policy_of_fun")), so totality is immediate. Adequacy then reduces to the entry coverage of @sec:calls and a routed entry unknown in the solved set.

@fig:eq-policies shows how the policies differ on a call chain. A call string
of length one separates the two calls of `wrap` but merges them again in
`scale`, where both arrive from the same call site. Length two and entry-state
routing keep them apart.

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
  block(width: 100%, {
    align(center, text(size: 7pt, weight: "bold", title))
    v(2pt)
    align(center, diagram(
      spacing: (10mm, 4mm),
      ..shown.map(c => node(
        pos.at(c.id),
        text(size: 6.5pt)[#c.proc \ #raw(ctxlabel(c))],
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
    align(center, text(size: 6.5pt)[`a == 2`: #verdict-chip(verdict) \ #raw(state)])
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
      columns: (1fr, 1fr, 1fr, 1fr),
      column-gutter: 4pt,
      _policy("ctx-demo-none", [no contexts]),
      _policy("ctx-demo-k1", [call strings, $k = 1$]),
      _policy("ctx-demo-k2", [call strings, $k = 2$]),
      _policy("ctx-demo-entry", [entry states]),
    )
  },
  kind: image,
  placement: none,
  caption: [Procedure copies under four context policies, on a nested-call
    program: `scale(v)` returns `2 * v`, `wrap(w)` returns `scale(w)` from
    #_site("scale(w)"), and `main` calls `a = wrap(1)` at #_site("wrap(1)") and
    `b = wrap(4)` at #_site("wrap(4)"), then checks `a == 2`. Boxes are copies labeled with their contexts (`root` is that of `main`), and arrows are calls labeled with their sites (Interval, claims #claim-ref("ctx-demo-*")).],
) <fig:eq-policies>

An entry-state context consists of the abstract values that the entry state
$e$ gives the callee's formal parameters, written $e|_"formals"$. For
`bump(n)` and an $e$ that binds $n$ to $[4, 5]$, the context is $[[4, 5]]$, a
list with one entry per formal. Unlike a call string, such a context depends
on the abstract entry state, so the concrete call alone does not determine it.

The entry-state policy (#isaconst("routed_entry_context_rel")) therefore reads
the context of a concrete call from the solution at that call. It admits a
context exactly when the equations, at this call node and in this caller
context, route an entry pair that describes the call to it. Suppose the
caller's solved state at a call `bump(x)` says $x in [4, 5]$. The equations
publish $n |-> [4, 5]$ to $[[4, 5]]$, so a run that passes this call with
$x = 4$ is admitted in $[[4, 5]]$ and not in $[[4, 4]]$. At another call whose
solved state says $x in [4, 4]$, the equations route to $[[4, 4]]$, and a run
with $x = 4$ through that call is admitted there. The policy thus copies the
routing of the equations call by call. Every admitted context has received an
entry state that describes the call, which is adequacy. Entry coverage
(@sec:calls) guarantees such an entry pair for every call from a store that the
caller's solved state describes, which is totality.

== Soundness of the generated system #thy-badge("Voblint_Framework", "Routed_Context") <sec:eq-discharge>

#figure(
  table(
    columns: (auto, 1fr),
    align: (left, left),
    stroke: none,
    table.hline(),
    [*obligation*], [*what the generated equations provide*],
    table.hline(stroke: 0.5pt),
    [#oblig("INIT")], [the initial state at the program entry covers the initial stores],
    [#oblig("INTRA")], [the transfer along each local edge is sound],
    [#oblig("CALL")], [the routed entry state covers the entered store (adequacy)],
    [#oblig("RETURN")], [the callee's result is combined soundly in the same context (adequacy)],
    [#oblig("TOTAL")], [every covered call is admitted in some context (totality)],
    table.hline(),
  ),
  placement: none,
  caption: [How the generated equations meet the five obligations of
    @ch:traces, for an arbitrary program.],
) <tab:eq-obligations>

Each obligation of @ch:traces is met by one part of the generated equations
(@tab:eq-obligations). The argument holds for every
domain and context policy. Its locale
#isalocale("routed_context") assumes a post-solution $sol$ on a solved set
closed under local edges and call continuations, the
#isalocale("analysis_contract") of @ch:analysis-interface, a sound bottom test,
a sound callee resolution, and adequate and total routing. The theorem adds that the program entry
is solved in the initial context and that the initial state $d_0$ describes the initial stores $S_0$.
#theorem(name: [Routed collecting soundness], isa: "activation_collect_dg_sound")[
  #proved("activation_collect_dg_sound")
]
The solver gives guarantees only for the unknowns in its solved set, so the
cover #isai("cover v c") is $conc_(M)(sol(v, c))$ there and empty elsewhere. No
execution reaches an unknown outside the solved set, since the set contains the
program entry and is closed under local edges, call continuations, and routed
calls. The proof checks each obligation for this cover, one row of
@tab:eq-obligations each. Instantiated for the policies of @tab:eq-policies,
the theorem covers the analyzer's equations, and @ch:solving computes such a
post-solution.
