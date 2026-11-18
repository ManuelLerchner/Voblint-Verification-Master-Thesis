#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": (
  isaconst, isai, isalocale, isathm, isatype, listing, oblig, site, thy-badge,
)
#import "../lib/math.typ": *
#import "../lib/theorems.typ": theorem
#import "../lib/figures.typ": call-edge, entry-node, intra-edge, verdict as verdict-chip
#import "../lib/claims.typ": (
  claim-ref, claim-snapshot, claim-trace, snapshot-cluster-of, snapshot-verdict,
)
#import "../lib/sources.typ": proved, thy


= Context-Indexed Equations and Routing <ch:equations>

@ch:traces reduced soundness to a cover, a set of stores $"cover"(v,c)$ for every node $v$ and context $c$, and stated five local
obligations under which it contains every store that executions bring to $v$
in $c$. This chapter computes such a cover. It turns the
procedure-aware graph of @ch:program-model into a system of equations whose
post-solutions all induce sound covers.

Precisely, every post-solution $sol$ of the equations should satisfy
$
  cal(A)(v,c) subset.eq conc_(M)(sol(v, c))
$
at every node $v$ and context $c$. The left side is the activation collecting
semantics of @sec:contexts, with graph, initial stores, root context, and
policy fixed for this chapter, and $conc_(M)(sol(v, c))$ is the set of stores
that the solved abstract state at $(v, c)$ describes under the solved values
of the analysis globals (@sec:analysis-globals). At a call, the equations must also
determine which callee context the call enters. Under entry-state
policies, this context is computed from the abstract state at the call, which
is known only while the equations are being solved.

== Context-indexed unknowns and call equations #thy-badge("Voblint_Framework", "DG_Indexed_Generator") <sec:eq-call>

The equations must keep the activations of `bump(5)` and `bump(4)` apart, so
that the first call's result stays exactly $6$ (@sec:interproc). Voblint
therefore indexes the unknowns of the equations by contexts. For every
node $v$ and context $c$, there is a _local_ unknown $(v, c)$, whose value
$sol(v, c)$ is the abstract state for the activations of context $c$ at $v$. Goblint's local unknowns have the
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L26-L28")[same shape] @apinis14[§5.2].
Besides the local unknowns, the equations have _global_ unknowns without a
program point (@sec:side-effects). They hold the analysis globals of @sec:shared-facts
and the entry states that calls publish to their callees.

Since a post-solution must describe every store that reaches $v$ in context
$c$, the equation of $(v, c)$ collects abstract states from four sources. They are the
initial state at the program entry, the transfer along each local edge into
$v$, the result of each call returning to $v$, and, at a procedure entry, the
entry states published by calls (@sec:calls). Along a local edge, the
activation keeps its context $c$ (@sec:contexts), whereas a callee runs in a
context of its own.

For a valuation $tau$ of the other unknowns (@sec:constraints), the local
component $F_(v,c)(tau)$ of the right-hand side of $(v,c)$ joins the four sources:
$
  F_(v,c)(tau) = & #isaconst("rhs_init") (v) \
           ljoin & scripts(⨆)_(e in P(v,c)) #isaconst("rhs_edge") (tau,c,e) \
           ljoin & scripts(⨆)_(k in K(v)) #isaconst("rhs_call") (tau,c,k,v) \
           ljoin & #isaconst("rhs_seed") (tau,c,v).
$
Here $P(v,c)$ lists the local edges into $v$ selected for context $c$, $K(v)$
the calls returning to $v$, and $scripts(⨆)$ joins over a list, with empty join
$lbot$. The fixed parameters of the generator are omitted
(#isathm("routed_node_rhs_parts")), and the decomposition assumes that the
operations of the analysis are well formed (@sec:analysis-globals). The
equations that Voblint generates are the inequalities
$ sol(v, c) lge F_(v,c)(sol) quad "for every local unknown" (v, c), $
together with the side effects of the right-hand sides, which publish entry
states to seeds and contributions to analysis globals (@sec:side-effects).
Since $conc_M$ is monotone, $conc_(M)(sol(v, c))$ of a post-solution contains
the stores that each source describes.

In the running example, most nodes use only the edge source. The program entry
of `main` adds #isaconst("rhs_init"), the entry of `bump` in a context $c'$
reads its seed through #isaconst("rhs_seed"), and the node after a call, such
as $(italic("pp3"), c_0)$ after `bump(5)`, has only the call source.
@fig:eq-unknowns follows this last case.

At a call, the analyzer chooses the callee's context with a _routing_ function
$ctxh(u, c, e)$ of the call site $u$, the caller context $c$, and the entry
state $e$. Under entry-state contexts, the choice depends on $e$, so the
calls that contribute to a callee context become known only during solving,
as the routing cannot be fixed from the graph alone. The equation of the callee's entry
therefore cannot list them. Each call instead publishes its entry state to the
callee as a side effect (@sec:side-effects).

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
  placement: none,
  scale(80%, reflow: true, diagram(
    spacing: (11mm, 6.5mm),
    _loc((0, 0), $(italic("pp2"), c_0)$),
    _loc((0, 4.2), $(italic("pp3"), c_0)$),
    _step((1.4, 0), $enterh: (q_1, e_1)$),
    _step((1.4, 1.9), [route: $c_1$]),
    _seed((2.8, 1.9), $ctor("Activation_Seed") thin #_b space c_1$),
    _loc((2.8, 2.9), $(ctor("FunctionEntry") thin #_b, c_1)$),
    _loc((2.8, 3.9), $(ctor("FunctionResult") thin #_b, c_1)$),
    _step((1.4, 4.2), $sh("combine")(q_1, r_1)$),
    _read((0, 0), (1.4, 0), [caller value], side: left),
    edge(
      (0, 0),
      (0, 4.2),
      stroke: (paint: vb.called, thickness: 0.8pt, dash: "dotted"),
      label: text(7.5pt, fill: vb.called)[continuation],
      label-side: right,
      label-angle: auto,
    ),
    _read((1.4, 0), (1.4, 1.9), $e_1$, side: left),
    _pub((1.4, 1.9), (2.8, 1.9), [publish $e_1$], side: right),
    _read((2.8, 1.9), (2.8, 2.9), [seed read], side: left),
    _read((2.8, 2.9), (2.8, 3.9), [body], side: left),
    _read((2.8, 3.9), (1.4, 4.2), $r_1$, side: left),
    edge(
      (1.4, 0),
      (1.4, 4.2),
      "-|>",
      bend: -50deg,
      stroke: (paint: vb.neutral, thickness: 0.6pt, dash: "dotted"),
      label: text(7.5pt, fill: vb.neutral, $q_1$),
      label-side: right,
    ),
    _read((1.4, 4.2), (0, 4.2), [joined], side: right),
    node(
      enclose: ((0, 0), (0, 4.2)),
      stroke: 0.5pt + vb.muted,
      fill: vb.muted.lighten(94%),
      corner-radius: 4pt,
      inset: 8pt,
      name: <ctx-main>,
    ),
    node((0, -0.75), text(7pt, fill: vb.muted)[`main`, $c_0$], stroke: none),
    node(
      enclose: ((2.8, 2.9), (2.8, 3.9)),
      stroke: 0.5pt + vb.muted,
      fill: vb.muted.lighten(94%),
      corner-radius: 4pt,
      inset: 8pt,
      name: <ctx-bump>,
    ),
    node((2.8, 4.6), text(7pt, fill: vb.muted)[`bump`, $c_1$], stroke: none),
  )),
  caption: [The first call under entry-state contexts. Node-context pairs are
    local unknowns, and the rounded seed is a global unknown. The other boxes
    are the steps of the equation of $(italic("pp3"), c_0)$. Solid arrows are
    reads, the dashed arrow publishes the entry state, and dotted arrows mark
    the continuation and the resume state $q_1$ that skips the callee.],
) <fig:eq-unknowns>

In the figure, `main` runs in the root context $c_0$, and its call `bump(5)` sits on the edge from
$italic("pp2")$ to $italic("pp3")$. The equation of the continuation
$(italic("pp3"), c_0)$ connects caller and callee. First,
enter (@sec:calls) turns the caller's value at $(italic("pp2"), c_0)$ into an
_entry pair_ $(q_1, e_1)$. The resume state $q_1$ describes the caller's
store during the call, and its entry state $e_1$ describes the callee's store
at entry, with $n$ bound to $absval(ivl(5, 5))$. Second, routing computes the
callee context $c_1 = ctxh(u, c_0, e_1) = [[5, 5]]$ from the call site $u$,
the caller context and the entry state, and the equation publishes $e_1$ to
that context. Third, the equation reads the exit state $r_1$ of `bump` in
$c_1$ and joins $sh("combine")(q_1, r_1)$, the caller's store after the call,
into its own value. The equation of the second call's continuation,
$(italic("pp4"), c_0)$, does the same with $c_2 = [[4, 4]]$. The calls `bump(5)` and `bump(4)`
thus use separate copies of `bump`, and the first result stays exactly 6.

Each callee entry $p$ and context $c'$ has a global unknown, the _seed_
$ctor("Activation_Seed") thin p space c'$ (#isatype("global_unknown")). Every
call routed to $(p, c')$ publishes to it, and the equation of
$(ctor("FunctionEntry") thin p, c')$ reads it. A call with several callees, or
an enter that returns several entry pairs, routes and publishes each pair
separately.

Since a caller reads nothing of the callee except its exit state, a recursive call
needs no special treatment. Its equation reads an exit state that in turn depends on
the caller's own unknowns, so the dependencies form a cycle. The solver handles
this cycle like the cycle of a loop and widens at the unknown where a read
closes it (@sec:td).

The right-hand side handles one special case. A call whose entry state is
bottom publishes nothing and does not read the callee's exit state. No store enters the callee in that case, and the read would
only make the solver evaluate the callee's body from a state that describes no
store. Goblint's normal-call transfer
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L244-L245",
)[skips]
bottom entry states in the same way. Skipping them is sound because a state
classified as bottom is required to have an empty concretization
(#isathm("routed_context.is_bot_sound", thy: "Routed_Context", display: "is_bot_sound")).

== Routing consistent with the context policy #thy-badge("Voblint_Framework", "Routed_Context") <sec:eq-routing>

Every call is assigned a callee context twice. The equations choose one from
the abstract entry state, and the concrete semantics of @ch:traces chooses one
from the concrete call, through the context policy $italic("adm")$ of
@sec:contexts. The unknowns of a context receive only what the equations publish
there, but they must describe every concrete activation that the policy admits
in it. The two choices must therefore agree. In the running example, the
policy admits the activation of `bump` with $n = 5$ in the context $[[5, 5]]$,
and the call `bump(5)` publishes an entry state with $n = 5$ to the same context.
In general, whenever the policy admits a concrete call in a context, the
equations must publish to that context an entry pair that describes the call
(@fig:eq-adequacy). For a caller store $s$ that the caller's solved state
describes and the entered store $s'$:
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
  caption: [Routing adequacy. If the concrete semantics assigns a call to $c'$ (left),
    the equations must route an entry pair that describes the call to the same $c'$ (right).],
) <fig:eq-adequacy>

This condition is called _routing adequacy_
(#isathm("routed_context.routing_adequate", thy: "Routed_Context", display: "routing_adequate")).
It also requires the callee's entry unknown in $c'$ to be in the solved set.
#oblig("CALL") and #oblig("RETURN") rely on routing adequacy, because the call
publishes $e$ and its continuation reads the callee's exit state in the same
context $c'$. Routing adequacy says nothing about a call to which $italic("adm")$
assigns no context. A call without a context would disappear from the activation
collecting semantics, which #oblig("TOTAL") of @sec:contract rules out. The
second condition, _routing totality_
(#isathm("routed_context.routing_total", thy: "Routed_Context", display: "routing_total")),
is what #oblig("TOTAL") asks of the generated equations. It requires
$italic("adm")$ to admit at least one context for every concrete call from a
store that the caller's solved state describes. Both conditions are premises of
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
      [entry-state contexts],
      [$c' = e|_"formals"$, $(q, e)$ describes $(s, s')$],
      [$e|_"formals"$],
      [$italic("adm")$ reads the routing],
      table.hline(),
    )
  },
  placement: none,
  caption: [The contexts that $italic("adm")$ admits for a call at site $u$
    from caller context $c$, the context to which the equations route the
    entry state $e$, and why the two agree. $u dot c$ prepends the site,
    $"take"_k$ keeps the first $k$ entries, and $e|_"formals"$ lists the
    formals' values in $e$.],
) <tab:eq-policies>

@tab:eq-policies compares the three context policies that Voblint implements.
In it, an entry pair $(q,e)$ of the caller's solved state describes $(s,s')$ when $s in conc(q)$ and
$s' in conc(e)$. Unit and call strings are _functional_ policies, since they
choose the context without reading abstract states. For them, $italic("adm")$ admits exactly the context that the
routing function computes for the call, which does not depend on $e$
(#isaconst("context_policy_of_fun")), so routing totality is immediate. Routing
adequacy then reduces to the entry coverage of @sec:calls and a routed entry unknown in the solved set.

@fig:eq-policies shows how the policies differ on a call chain from the
playground's demo program:

#listing(lang: "c", claim: "ctx-demo-k1", ```
fun scale(v) { return v * 2; }
fun wrap(w) { r = scale(w); return r; }
fun main() { a = wrap(1); b = wrap(4); __voblint_check(a == 2); }
```)

A call string
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
      ..pairs.map(((a, b, site)) => {
        // Two arrows converging on one copy would put both labels in the
        // gap between them; each label goes on its arrow's outer side.
        let dx = pos.at(b).at(0) - pos.at(a).at(0)
        let side = if pos.at(b).at(1) == 2 and dx > 0 { right } else if (
          pos.at(b).at(1) == 2 and dx < 0
        ) { left } else { auto }
        edge(
          pos.at(a),
          pos.at(b),
          "-|>",
          stroke: 0.6pt + vb.called,
          label: text(size: 7pt, fill: vb.called, raw(site)),
          label-sep: 1pt,
          label-side: side,
        )
      }),
    ))
    v(2pt)
    align(center, text(
      size: 6.5pt,
    )[`a == 2`: #verdict-chip(verdict) \ #raw("a=")#absval(raw(state.slice(2)))])
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
      _policy("ctx-demo-none", [unit]),
      _policy("ctx-demo-k1", [call strings, $k = 1$]),
      _policy("ctx-demo-k2", [call strings, $k = 2$]),
      _policy("ctx-demo-entry", [entry-state contexts]),
    )
  },
  kind: image,
  placement: none,
  caption: [Procedure copies of the program above under four context policies.
    The call sites are #_site("scale(w)") in `wrap` and #_site("wrap(1)") and
    #_site("wrap(4)") in `main`. Boxes are copies labeled with their contexts (`root` is that of `main`), and arrows are calls labeled with their sites (Interval, claims #claim-ref("ctx-demo-*")).],
) <fig:eq-policies>

An entry-state context $e|_"formals"$ lists the abstract values that the entry
state $e$ gives the formal parameters, such as $[[4, 5]]$ for `bump(n)` when $e$
binds $n$ to $absval(ivl(4, 5))$. It depends on the abstract entry state, so
the concrete call alone does not determine it.

The entry-state policy therefore takes its admissibility relation
(#isaconst("routed_entry_context_rel")) from the solution. The definition is not
circular. The solver computes $sol$ from the equations alone and never consults
the policy. The relation is defined afterwards for the finished $sol$, and only
the soundness statement uses it, to fix which activations $cal(A)(v, c)$
assigns to each context. It admits a concrete call in exactly the contexts to
which the equations route an entry pair that describes the call. Routing
adequacy thus holds by construction. Entry coverage (@sec:calls) supplies such
an entry pair for every call from a store that the caller's solved state
describes, which gives routing totality.

== Soundness of the generated equations #thy-badge("Voblint_Framework", "Routed_Context") <sec:eq-discharge>

With the equations and their routing fixed, every post-solution should induce
a cover that meets the five obligations of @ch:traces. The argument assumes the analysis contract of
@ch:analysis-interface and the routing adequacy and totality of
@sec:eq-routing. It also assumes that a state classified as bottom describes
no store (@sec:eq-call), and that every call resolves to its callee from every
store the caller's solved state describes (#isalocale("routed_context")).

The solver gives guarantees only for the unknowns in its solved set, which is
closed under local edges and call continuations. The cover is therefore $"cover"(v,c) = conc_(M)(sol(v, c))$ for $(v,c)$ in the solved set
and empty elsewhere. As in @ch:traces, $v_0$ is the entry node, $c_0$ the root
context, and $S$ the set of initial stores. Let $d_0$ be the initial local
abstract state, $eta_0$ the initial global environment, and $eta$ the solved
environment.
#theorem(name: [Post-solutions yield sound covers], isa: "activation_collect_dg_sound")[
  Under the routing and analysis assumptions above, if $(v_0,c_0)$ is solved,
  $S subset.eq conc_(D G)(d_0,eta_0)$, and $eta_0 lle eta$, then
  $ cal(A)(v,c) subset.eq "cover"(v,c) $
  for every node $v$ and context $c$.
]
The proof reduces the theorem to the coverage contract of @sec:contract. That
theorem already shows, by induction over the traces, that a cover meeting the
five obligations contains $cal(A)(v,c)$ (#isathm("activation_collect_sound")).
It remains to check the obligations for the cover $conc_(M)(sol(v, c))$, one
per source of the equations. Each check follows the same
pattern. A post-solution satisfies $F_(v,c)(sol) lle sol(v, c)$, so every source
lies below $sol(v, c)$. Since $conc_M$ is monotone, the stores a source
describes are also described by $sol(v, c)$, and the soundness law of the source
turns this into its obligation. The edge source, for instance, describes every
successor of a store that the predecessor's state describes, which is
#oblig("INTRA"). For calls, routing adequacy places the published entry state
and the exit state read back in the context that the concrete semantics
assigns, and routing totality gives #oblig("TOTAL").

Theorem 8.1 is the result of this chapter. Every post-solution $sol$ of the
equations $F_(v,c)$ of @sec:eq-call meets the goal stated at the start of the
chapter,
$ cal(A)(v,c) subset.eq conc_(M)(sol(v, c)), $
at every $(v, c)$ in its solved set, for every domain and each policy of
@tab:eq-policies. The theorem does not compute a post-solution, however. Something still has to
solve the equations. @ch:solving obtains a post-solution from the verified TD
solver whenever a solve returns.
