#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/math.typ": *
#import "../lib/theorems.typ": theorem
#import "../lib/figures.typ": call-edge, entry-node, intra-edge
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

@ch:traces reduced soundness to a _claim_, which assigns to every node $v$
and context $c$ a set of stores #isai("cover v c"), and stated five local
obligations under which the claim contains every store that an execution
brings to $v$ in context $c$. @ch:analysis-interface and @ch:cooperation stated what an analysis supplies
and proves. What is still missing is a way to compute such a claim.
This chapter turns the procedure-aware graph of @ch:program-model into a
system of equations and shows that every post-solution induces a sound claim.

Inside a procedure the construction is direct, while calls need more care. A
call enters a context of the callee. Under some context policies,
that context depends on the abstract entry state computed from the caller,
which becomes known only while the equations are solved. Formally, the goal is
that every post-solution $sol$ satisfies
$
  #isai("\<A>\<^bsub>\<G>,adm,c₀,g,S\<^esub> v c") subset.eq conc_(M)(sol(v, c))
$
at every node $v$ and context $c$. The left side is the activation collecting
semantics of @sec:contexts, and $conc_(M)(sol(v, c))$ is the set of stores
that the solved abstract state at $(v, c)$ describes under the solved values
of the analysis globals (@sec:sound-core). The running example is the program
of @fig:program-to-equations.

== Unknowns and right-hand sides <sec:eq-call>

The running example calls `bump` first with 5 and then with 4. If both
activations shared one abstract state at the entry of `bump`, that state would
have to contain both values, the return would merge the two results, and the
analysis could no longer show that the first result is exactly 6. Contexts
avoid this merge by giving the two activations separate copies of `bump`.

Voblint therefore indexes the unknowns of the equations by contexts. For every
node $v$ and context $c$ there is a _local_ unknown $(v, c)$, whose value
$sol(v, c)$ is the abstract state for the activations of context $c$ at $v$.
These are the indices of the claim. Goblint's local unknowns have the
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L26-L28")[same shape].
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

The generated right-hand side #isaconst("routed_node_rhs") computes exactly
the join of these four sources under a valuation $tau$:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  proved("routed_node_rhs_parts")
}
Here $scripts(⨆)_(x <- italic("xs")) f(x)$ joins $f(x)$ over the list
$italic("xs")$, and the empty join is $lbot$. The lists range over the local
edges into $v$ and over the calls that return to $v$. The parts
#isaconst("rhs_init"), #isaconst("rhs_edge"), #isaconst("rhs_call") and
#isaconst("rhs_seed") are the four sources in this order. Publications to analysis globals (@sec:shared-facts) are not part of this
value. A post-solution lies above it, and $conc_M$ is monotone, so
$conc_M(sol(v, c))$ contains what each source describes.

At a call, the analyzer chooses the callee's context with a _routing_ function
$ctxh(u, c, e)$ of the call node $u$, the caller context $c$ and the entry
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
    boxes are steps of the right-hand side, and grey frames group the unknowns
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

A caller's equation publishes to the callee's seed and reads the callee's
result, and it reads no other unknown of the callee. A recursive call is
therefore an ordinary call. Its equation reads the result of the callee in
some context, which creates a cycle of dependencies between unknowns. The
solver treats this cycle like the cycle of a loop, and the unknown at which a
read closes it becomes a widening point (@sec:td). The explainer's
#link(
  "https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/index.html#replay",
)[solve replay]
animates this protocol.

Formally, a call publishes its entry state to a _seed_
$ctor("Activation_Seed") thin p space c'$, one global unknown
(#isatype("global_unknown")) per callee entry and context. Every call routed
to $(p, c')$ publishes to this seed, and the equation of the entry
$(ctor("FunctionEntry") thin p, c')$ reads it. In general a call may enter
several callees, and enter may return several entry pairs. Each of them is
routed separately.

If the entry state is bottom, no store enters the callee, so the call publishes
nothing and does not read the callee's result. Without this test, the read
would make the solver evaluate the callee's body from an entry state that
describes no store. Goblint's normal-call transfer
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L244-L245",
)[skips]
bottom entry states in the same way. The optimization is sound because a state
classified as bottom is required to have an empty concretization
(#isathm("routed_context.is_bot_sound", thy: "Routed_Context", display: "is_bot_sound")).

== Routing and context policies <sec:eq-routing>

The analyzer chooses a callee context from abstract information. The concrete
semantics of @ch:traces also assigns each concrete activation to a context,
through the context policy $italic("adm")$ of @sec:contexts, and its choice may
depend on concrete stores that the analyzer never sees. For the equations to
be sound, the two choices must fit together. Whenever the concrete semantics
assigns an activation to a context $c'$, some call must have published to the
seed of $c'$ an abstract entry state that covers the activation's entered
store. Otherwise the unknowns of $c'$ would have to cover a store that no
equation put there.

Suppose a concrete call from a caller store $s$, which the caller's solved
value covers, enters the callee in store $s'$, and $italic("adm")$ admits $c'$
for it. Then enter, applied to the caller's solved value, must return some
entry pair $(q, e)$ that the equations route to $c'$, with $q$ covering $s$
and $e$ covering $s'$ (@fig:eq-adequacy):
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
#oblig("CALL") and #oblig("RETURN") need adequacy, because the call publishes
$e$ and its continuation reads the callee's result in the same $c'$. A second
condition, _totality_
(#isathm("routed_context.routing_total", thy: "Routed_Context", display: "routing_total")),
requires $italic("adm")$ to admit at least one context for every concrete call
from a store that the caller's solved value covers. Without totality, a
concrete call could be assigned no context at all and would therefore
disappear from the context-indexed collecting semantics. The obligation
#oblig("TOTAL") of @sec:contract rules this out, and totality is exactly what
it asks of the generated equations. Both conditions are premises of the
soundness theorem and are proved once for each context policy.

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
(#isaconst("context_policy_of_fun")), so totality is immediate. The rest of
adequacy is the entry coverage of @sec:calls and the routed entry unknown
being in the solved set.

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
  let tone = if verdict == "PROVED" { vb.proved } else { vb.unstable }
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
    align(center, text(size: 6.5pt)[`a == 2`: #text(fill: tone, verdict) \ #raw(state)])
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
    `b = wrap(4)` at #_site("wrap(4)"), then checks `a == 2`. Boxes are copies
    labelled with their contexts (`root` is that of `main`), arrows calls
    labelled with their sites (Interval, claims #claim-ref("ctx-demo-*")).],
) <fig:eq-policies>

An entry-state context consists of the abstract values that the entry state
$e$ gives the callee's formal parameters, written $e|_"formals"$. For
`bump(n)` and an $e$ that binds $n$ to $[4, 5]$, the context is $[[4, 5]]$, a
list with one entry per formal. Unlike a call string, it depends on the
abstract entry state, so the concrete call alone does not determine it.

If the caller's solved state says $x in [4, 5]$ at `bump(x)`, the equations
publish $n |-> [4, 5]$ to the context $[[4, 5]]$. An execution with $x = 4$
must then be assigned to $[[4, 5]]$, where its covering entry state was
published, and not to $[[4, 4]]$.

The entry-state policy (#isaconst("routed_entry_context_rel")) does exactly
this. For a call from $s$ with entered store $s'$, it admits $c'$ only when
$c' = e|_"formals"$ for an entry pair $(q, e)$ with $s in conc(q)$ and
$s' in conc(e)$. The equations publish that same $e$ to $c'$, so every admitted context is
backed by a covering entry state, which is adequacy. Entry coverage (@sec:calls)
gives every covered call such a pair, which is totality.

This policy depends on the solved analysis (@sec:contexts) without circularity:
the proof fixes $sol$, defines $italic("adm")$ from it, and shows that $sol$
covers the collecting semantics this $italic("adm")$ induces.

== Soundness of the generated system <sec:eq-discharge>

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

The argument holds for every domain and context policy. Its locale
#isalocale("routed_context") assumes a post-solution $sol$ on a solved set
closed under local edges and call continuations, the
#isalocale("analysis_contract") of @ch:analysis-interface, a sound bottom test,
a sound callee resolution, and adequate and total routing. The theorem adds that the program entry
is solved in the initial context and that the initial stores $S_0$ lie in
$conc_(D G)(d_0, e_0)$: the initial state $d_0$ describes them under an
environment $e_0$ of analysis-global values below the solved ones.
#theorem(name: [Routed collecting soundness], isa: "activation_collect_dg_sound")[
  #proved("activation_collect_dg_sound")
]
Here #isai("cover v c") is $conc_(M)(sol(v, c))$ inside the solved set and
empty outside it. The proof turns the bound on each part, and on each seed,
into its row of @tab:eq-obligations. #isathm("fun_route_activation_collect_sound") and
#isathm("entry_state_activation_collect_sound") instantiate the theorem for the
analyzer, and @ch:solving computes such a post-solution.
