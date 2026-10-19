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
brings to $v$ in context $c$. To compute such a claim, Voblint turns the
procedure-aware graph of @ch:program-model into a system of equations. The
goal is that every post-solution $sol$ on a set of solved unknowns that
executions cannot leave satisfies
$
  #isai("\<A>\<^bsub>\<kappa>,adm,c₀,g,S\<^esub> v c") subset.eq conc_(M)(sol(v, c))
$
at every solved node $v$ and context $c$. The left side is the activation
collecting semantics of @sec:contexts. The right side reads the solved state
through the concretization of @sec:sound-core,
$conc_(M)(sol(v, c)) = conc_(D G)(d, rho)$, where $d$
is the local state that $sol$ assigns to $(v, c)$ and the environment $rho$
holds the values that $sol$ assigns to the analysis globals. Calls make this hard, because the
callee's context may depend on abstract values that become known only while
the equations are solved. The running example is the program of
@fig:program-to-equations.

== Unknowns and right-hand sides #thy-badge("Voblint_Framework", "DG_Indexed_Generator") <sec:eq-call>

The running example calls `bump` first with 5 and then with 4. If both
activations shared one abstract state at the entry of `bump`, that state would
have to contain both values, the return would merge the two results, and the
analysis could no longer show that the first result is exactly 6. Contexts
avoid this merge by giving the two activations separate copies of `bump`.

Voblint therefore indexes the unknowns of the equations by contexts. For every
node $v$ and context $c$ there is a _local_ unknown $(v, c)$, the unknown
$[v, c]$ of @ch:traces, whose value
$sol(v, c)$ is the abstract state for the activations of context $c$ at $v$.
These are the indices of the claim, and Goblint's local unknowns have the
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L26-L28")[same shape] @apinis14[§5.2].
The equations also have _global_ unknowns without a program point (@sec:td),
which hold the analysis globals of @sec:shared-facts and the entry states that
calls publish to their callees.

The equation of $(v, c)$ collects every abstract state that can reach $v$ in
context $c$. These states come from four sources: the initial state at the
program entry, the transfer along each local edge into $v$, the result of each
call that returns to $v$, and, at a procedure entry, the entry states (the
abstract states in which the callee starts, @sec:calls) that calls publish to
it. A local edge keeps the activation's context (@sec:contexts), so its
transfer reads the predecessor in the same context $c$. The generated right-hand side
(#isaconst("routed_node_rhs")) is the join of the four sources, evaluated
under a valuation $tau$ (the statement's name for it, unrelated to the
strategy trees of @sec:td), an arbitrary assignment of values to the unknowns:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  proved("routed_node_rhs_parts")
}
Here $scripts(⨆)_(x <- italic("xs")) f(x)$ joins $f(x)$ over the list
$italic("xs")$, the empty join is $lbot$, and the lists range over the local
edges into $v$ and the calls that return to $v$. The four parts inside
#isai("DG") are the four sources in the order above. The remaining parameters
select the edges and calls and fix how the right-hand side is encoded for the
solver, which @sec:eq-encoding explains, and #isai("DG") pairs the local state
with an unused global half. A post-solution lies above this join, and $conc_M$
is monotone, so $conc_M(sol(v, c))$ contains what each source describes.

At a call, a _routing_ function $ctxh(u, c, e)$ chooses the callee's context
from the call node $u$, the caller context $c$, and the entry state $e$. Under
entry-state contexts the choice depends on $e$, which is known only while the
equations are solved, so the callee's entry cannot list in its equation the
calls that contribute to one of its contexts. Each call instead publishes its
entry state as a side effect (@sec:side-effects). Apinis et al.
@apinis12[§6] and Goblint publish it directly to the callee's entry. In
Goblint this entry holds a value of the local domain but has no right-hand
side of its own
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L396-L399")[`constraints.ml`]).
In Voblint's equations the entry is a local unknown with a right-hand side,
and the verified solver accepts side effects only to global unknowns, so
Voblint publishes to
a _seed_ $ctor("Activation_Seed") med p space c'$, the global unknown
(#isatype("global_unknown")) that carries the entry state of callee $p$ in
context $c'$ (@sec:eq-seed-global). Every call routed to $(p, c')$ publishes
to this seed, and the equation of the entry
$(ctor("FunctionEntry") med p, c')$ reads it.

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
    _seed((0, 1.9), $ctor("Activation_Seed") med #_b space c_1$),
    _loc((0, 2.9), $(ctor("FunctionEntry") med #_b, c_1)$),
    _loc((0, 3.9), $(ctor("FunctionResult") med #_b, c_1)$),
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
    The right-hand side of $(italic("pp3"), c_0)$ routes the entry state $e_1$
    to $c_1$, publishes it to the seed of `bump` in $c_1$ (purple, dashed),
    reads the result there and joins the combined state into its own value.
    Blue boxes are local unknowns, the purple box is a global unknown, white
    boxes are steps of the right-hand side, and gray frames group one procedure
    in one context.],
) <fig:eq-unknowns>

In @fig:eq-unknowns, the equation of the continuation $(italic("pp3"), c_0)$
reads the caller's value at $(italic("pp2"), c_0)$ and applies enter
(@sec:calls), which yields an _entry pair_ of a resume state $q_1$ and an
entry state $e_1$ that binds $n$ to $[5, 5]$. The entry state selects the
callee context $c_1 = [[5, 5]]$. The equation publishes $e_1$ to the seed of
$c_1$, reads the result $r_1$ of `bump` there, and joins
$sh("combine")(q_1, r_1)$ into its own value. The second call does the same
with $c_2 = [[4, 4]]$, so the two calls use separate copies of `bump` and the
first result stays exactly 6. The generic framework allows several call edges
at one call site and several entry pairs per call, and it routes each pair
separately. A compiled VIMP program, however, has one call edge per call site
(#isathm("compile_prog_calls_source_unique")), and the shipped analyses
return one entry pair per call.

A caller's equation reads no unknown of the callee other than its result, so
a recursive call needs no special treatment. Its cycle of dependencies is
handled like that of a loop, with a widening point where a read closes it
(@sec:td). The explainer's
#link(site("index.html#replay"))[solver replay] animates this protocol.

If the bottom test of the analysis classifies the entry state as empty, no
store enters the callee, so the call
publishes nothing and does not read the callee's result, which would make the
solver evaluate the callee's body for no store. Goblint's normal-call transfer
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L244-L245",
)[skips]
bottom entry states in the same way. The test is sound because a state it
classifies as empty must have an empty concretization
(#isathm("routed_context_base.is_bot_sound", thy: "Routed_Context", display: "is_bot_sound")).

== Routing and context policies #thy-badge("Voblint_Framework", "Routed_Context") <sec:eq-routing>

The analyzer chooses a callee context from abstract information. The concrete
semantics of @ch:traces assigns each activation its contexts through the
context policy $italic("adm")$ of @sec:contexts, which may depend on concrete
stores that the analyzer never sees. For entry-state contexts,
$italic("adm")$ must follow the analyzer's choice, so it is defined from the
solved valuation $sol$, as @sec:activation-trace anticipated. The argument is
nevertheless not circular. The valid traces and their node collecting
semantics are fixed before any analysis runs, and only the labelling of
traces by contexts depends on $sol$. The source-level result concerns only the
union over all contexts, and this union equals the node collecting semantics
under every policy whose claim meets the five obligations (the theorem
#isathm("node_collect_eq_Union_activation_collect") of @sec:contract). The
proof therefore fixes $sol$ first, defines $italic("adm")$ from it, and shows
that $sol$ covers the induced activation collecting semantics.

The equations are sound only if the two context choices agree. Suppose a concrete call from a caller store $s$, which the
caller's solved value covers, enters the callee in store $s'$, and
$italic("adm")$ admits $c'$ for it. Then enter, applied to the caller's solved
value, must return an entry pair $(q, e)$ that the equations route to $c'$,
with $q$ covering $s$ and $e$ covering $s'$ (@fig:eq-adequacy):
$
  italic("adm") "admits" c' "for" (s, s') quad ==> quad & "some entry pair" (q, e) "is routed to" c' \
                                                        & "with" s in conc(q) "and" s' in conc(e).
$
Otherwise the unknowns of $c'$ would have to cover a store that no equation
put there.
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
    the equations must route a covering entry pair to the same $c'$ (right).],
) <fig:eq-adequacy>

We call this condition _routing adequacy_
(#isathm("routed_context.routing_adequate", thy: "Routed_Context", display: "routed_context.routing_adequate")).
It also requires the callee's entry unknown in $c'$ to be in the solved set,
because $sol$ bounds the stores of an unknown only there (@sec:eq-discharge).
#oblig("CALL") and #oblig("RETURN") need routing adequacy, because the call publishes
$e$ and its continuation reads the callee's result in the same $c'$. A second
condition, _totality_
(#isathm("routed_context.routing_total", thy: "Routed_Context", display: "routed_context.routing_total")),
requires $italic("adm")$ to admit at least one context for every concrete call
from a covered caller store. Otherwise a concrete call could be assigned no
context and would disappear from the activation collecting semantics,
which the obligation #oblig("TOTAL") of @sec:contract rules out. Both
conditions are premises of the soundness theorem and are proved once for each
context policy.

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
    caller context $c$, with caller store $s$ and entered store $s'$, and where
    the equations route the entry state $e$. $u dot c$ prepends the site,
    $"take"_k$ keeps the first $k$ entries, $e|_"formals"$ lists the formals'
    values in $e$, and an entry pair $(q, e)$ of the caller's solved value
    covers $(s, s')$ when $s in conc(q)$ and $s' in conc(e)$. Call strings are
    a _store-independent_ policy, which computes the context from the call
    site and the caller context alone, and $k = 0$ is the context-insensitive
    analysis.],
) <tab:eq-policies>

For call strings, $italic("adm")$ admits exactly the context that the routing
function computes for the call, which does not depend on $e$
(#isaconst("context_policy_of_fun")). Totality is then immediate
(#isathm("call_context_total_on_of_fun")), and routing adequacy
reduces to the entry coverage of @sec:calls and a routed entry unknown in the
solved set.

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
    program: `scale(v)` returns `v * 2`, `wrap(w)` returns `scale(w)` from
    #_site("scale(w)"), and `main` calls `a = wrap(1)` at #_site("wrap(1)") and
    `b = wrap(4)` at #_site("wrap(4)"), then checks `a == 2`. Boxes are copies labeled with their contexts (`root` is that of `main`, and `unit` is how the analyzer prints the single context of $k = 0$, the empty call string), and arrows are calls labeled with their sites (Interval, claims #claim-ref("ctx-demo-*")).
    Where both calls reach one copy of `scale`, they publish to one seed,
    which the update rule widens to $v >= 1$ (@sec:eq-seed-global), so
    `v * 2` may overflow and `a` can be any `i32` value.],
) <fig:eq-policies>

An entry-state context is the list $e|_"formals"$ of the abstract values that
the entry state $e$ gives the callee's formals. For `bump(n)` and an $e$ that
binds $n$ to $[4, 5]$, it is $[[4, 5]]$. If the caller's
solved state has $x in [4, 5]$ at `bump(x)`, the equations publish
$n |-> [4, 5]$ to the context $[[4, 5]]$, and an execution with $x = 4$ must
then be admitted in $[[4, 5]]$, where its covering entry state was published,
and not in $[[4, 4]]$. The entry-state policy
(#isaconst("routed_entry_context_rel")) therefore admits $c'$ for a call from
$s$ with entered store $s'$ only when $c' = e|_"formals"$ for an entry pair
$(q, e)$ with $s in conc(q)$ and $s' in conc(e)$. The equations publish that
same $e$ to $c'$, which gives routing adequacy, and entry coverage (@sec:calls) gives
every covered call such a pair, which gives totality. Because the policy reads
the entry pairs of the solved values, it is defined from $sol$, in the order
described at the start of this section.

== Soundness of the generated system #thy-badge("Voblint_Framework", "Routed_Context") <sec:eq-discharge>

By the soundness theorem of @sec:contract
(#isathm("activation_collect_sound")), every claim that meets the five
obligations contains the activation collecting semantics. It therefore
suffices to discharge the obligations for the claim that the solved equations
define. Let $V$ be the solved set, the local unknowns at which $sol$ satisfies
the equations as inequalities. The claim is
$
  #isai("cover v c") = conc_(M)(sol(v, c)) "if" (v, c) in V, quad #isai("cover v c") = emptyset "otherwise".
$
Outside $V$ the solver bounds nothing, so $sol$ may describe too few stores
there, and only the empty claim needs no bound. In exchange, executions must
not leave $V$. We call $V$ _closed under execution steps_ if a local edge
leads from a node of $V$ whose state describes some store to a node of $V$,
and a call site in $V$ has its continuation in $V$. Routing adequacy adds the callee's
entry in the routed context. @tab:eq-obligations lists which part of the
right-hand side discharges each obligation.

#figure(
  table(
    columns: (auto, 1fr),
    align: (left, left),
    stroke: none,
    table.hline(),
    [*obligation*], [*what the generated equations provide*],
    table.hline(stroke: 0.5pt),
    [#oblig("INIT")], [initial part, which lies above $d_0$],
    [#oblig("INTRA")], [edge part and the step law],
    [#oblig("CALL")], [call part publishing to the seed, seed part, routing adequacy],
    [#oblig("RETURN")], [call part reading the result, combine law, routing adequacy],
    [#oblig("TOTAL")], [totality],
    table.hline(),
  ),
  placement: none,
  caption: [How the parts of the generated right-hand side of @sec:eq-call
    meet the five obligations of @ch:traces, for an arbitrary program.],
) <tab:eq-obligations>

The argument holds for every domain and context policy. Its locale
#isalocale("routed_context") assumes a post-solution $sol$ on a solved set
closed under execution steps, the analysis contract of @ch:analysis-interface
(#isalocale("analysis_contract")), a sound bottom test, a sound callee
resolution, and adequate and total routing. Callee resolution lists, from the
caller's state, the procedures a call may enter, and it is sound if it lists
the actual callee for every covered caller store. The analyzer reads the
callee from the call edge, since every VIMP call names its callee. The theorem
adds that the program entry is solved in the initial context and that the
initial state $d_0$ describes the initial stores $S_0$ under an environment
$rho_0$ of analysis-global values below the solved ones,
$S_0 subset.eq conc_(D G)(d_0, rho_0)$ ($rho_0$ is #isai("e\<^sub>0") in the
statement).
#theorem(name: [Routed collecting soundness], isa: "activation_collect_dg_sound", statement: true)[]
Each row of @tab:eq-obligations follows from the bound that the post-solution
gives one part of the right-hand side, together with a law of the analysis
contract and the monotonicity of $conc_(D G)$. The step that needs care is
#oblig("RETURN"), where a trace resumes its caller with the final store of a
callee activation that carries some context $c'$, so that store lies in the
claim at the callee's result in $c'$. Routing adequacy, applied to the same call and caller
store $s$, gives an entry pair $(q, e)$ that the equations route to this same
$c'$ with $s in conc(q)$, so the call part of the continuation reads exactly
that result and the combine law places the resumed store in the claim.
#isathm("fun_route_activation_collect_sound") and
#isathm("entry_state_activation_collect_sound") instantiate the theorem for
store-independent and entry-state routing, and @ch:solving computes such a
post-solution.
