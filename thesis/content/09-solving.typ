#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "@preview/cetz:0.5.2"
#import "../lib/code.typ": (
  c11, fixture, isaconst, isai, isalocale, isathm, isatype, listing, thy-badge,
)
#import "../lib/sources.typ": thy, update-rule-steps
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": verdict
#import "../lib/claims.typ": claim-ref, claim-snapshot, claim-text, claim-trace

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
#let _b = $italic("bump")$

= Solving the Equations <ch:solving>

@ch:equations showed that every post-solution of the generated equations
covers the activation collecting semantics, provided the solved set
contains the program entry and is closed under execution steps
(#isathm("activation_collect_dg_sound")). The analyzer computes such a
post-solution with the verified top-down solver of Tilscher et al.
@tilscher26, which is proved partially correct. Two steps connect the two
results. The solver needs each right-hand side as a strategy tree (@sec:td), a
small program that reads one unknown at a time and makes every read and every
publication explicit, so the equations must be brought into this form. The
solver's correctness theorem must then be connected to the premises of the
soundness theorem. Both steps assume that the solver returns, which no theorem
establishes (@sec:termination).

== Adapting the equations to the solver <sec:eq-encoding>

A direct encoding of the equations, along the lines of Apinis et al. and
Goblint, needs four things that the interface of the vendored solver does not
offer (@tab:eq-adapters). @ch:equations stated the equations with the first
three adapters already in place. Buffering is left out there because it
changes only when publications are issued, not the equations
(@sec:eq-buffer).

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    stroke: none,
    table.hline(),
    [*the direct encoding needs*], [*the solver offers*], [*adapter*],
    table.hline(stroke: 0.5pt),
    [read a result chosen from the caller's value], [one read at a time],
    [strategy tree (@sec:eq-trees)],
    [write the callee's entry unknown], [side effects to globals only],
    [seeds (@sec:eq-seed-global)],
    [different local and global values], [one value type],
    [product (@sec:global-unknowns)],
    [publish twice to one target], [update rule at every side effect],
    [buffering (@sec:eq-buffer)],
    table.hline(),
  ),
  placement: none,
  caption: [Where the direct encoding of the equations and the interface of
    the vendored solver differ, and the adapter that bridges each.],
) <tab:eq-adapters>

=== Dynamic reads #thy-badge("Voblint_Framework", "Routed_Call_Programs") <sec:eq-trees>

A local edge always reads its predecessor, whereas a call chooses what to read
from values it has already read. The continuation $(italic("pp3"), c_0)$ of
the running example reads the caller $(italic("pp2"), c_0)$, computes from its
value the entry state $n = [5, 5]$ and the context $c_1$, and only then knows
that it must read $(ctor("FunctionResult") med italic("bump"), c_1)$. A
strategy tree allows this, because each continuation receives the value just
read and may choose the next read from it. The contribution of a call at $u$
in context $c$ (#isaconst("rhs_call")) is the value of the tree
$
  t_"call" = #ctor("QueryL") ( & (u, c), lambda d. \
                               & #ctor("Side") ( ctor("Activation_Seed") med p space c', e, \
                               & quad #ctor("QueryL") ( (ctor("FunctionResult") med p, c'), lambda r.
                                   #ctor("Answer", thy: "Basics_side") (sh("combine") (q, r)) ) ) ),
$
where $d$ is the caller's value, $(q, e) = enterh(d)$, $c' = ctxh(u, c, e)$,
and $r$ is the callee's result. The #ctor("Side") step publishes the entry
state to the callee's seed. The generated tree
(#isaconst("routed_call_program")) also handles entry states that the bottom
test classifies as empty and
several callees or entry pairs.

=== Local entries <sec:eq-seed-global>

A call has to pass its entry state $e$ to the callee's entry
$(ctor("FunctionEntry") med p, c')$, which in Voblint's equations is a local
unknown with a right-hand side. Apinis et al. publish to the entry directly
@apinis12[§6], and Goblint does the same with its local side effect `sidel`
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L244")[`constraints.ml`]),
whose target holds a value of the local domain but has no right-hand side
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L396-L399")[`constraints.ml`]).
The vendored solver's #ctor("Side") accepts only global unknowns, and local
targets would require changing the solver and redoing its correctness proof.

Voblint therefore routes the entry state through the seed
$ctor("Activation_Seed") med p space c'$ of @sec:eq-call, a global unknown.
The call publishes $e$ to it with #ctor("Side"), and the equation of the entry
reads it back with #ctor("QueryG"). Publishing alone does not make the solver
evaluate the callee, since it solves only unknowns that some tree reads. The
call, however, also reads the callee's result, and solving the result reaches
the entry and its seed.

Because seeds are global unknowns, the solver merges the contributions of
different calls with its _update rule_ for globals, the operation that
combines a new contribution with the value the unknown holds
(@sec:update-rules compares the five rules). Without contexts, both calls of
the running example publish to the one seed of `bump`. The default rule,
warrow, widens the seed when a contribution is not below its value, so the
seed first holds $n = [5, 5]$ and then widens when $[4, 4]$ arrives. The
analyzer then reports #_cli("pg-contexts-none", "a == 6", 3) for `a == 6`
with #_cli("pg-contexts-none", "a == 6", 4). Widening moved the lower bound to
the least `i32` value, and the call added one. The joining rule keeps
#_cli("pg-contexts-none-join", "a == 6", 4) (claim
#claim-ref("pg-contexts-none-join")), which is the loss due to merging
alone.

=== One value type #thy-badge("Voblint_Framework", "DG_State") <sec:global-unknowns>

A local unknown holds an abstract state of the analysis's local domain, and an
analysis global holds a value of its global domain (@sec:shared-facts). The
vendored solver has a single value type for all unknowns, so every unknown
holds a pair (#isatype("dg_state")) of a local and a global half, uses one
half and leaves the other at $lbot$ (@tab:eq-carrier). Order and join on pairs
are componentwise, so the solver's requirements on the value type follow from
those on the two halves. A seed is a global unknown that holds a local value,
the entry state it passes to the callee.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    stroke: none,
    table.hline(),
    [*solver unknown*], [*role*], [*value*],
    table.hline(stroke: 0.5pt),
    [$(v, c)$, local], [the state at $v$ in context $c$], [$(d, lbot)$],
    [#isaconst("Activation_Seed"), global], [an entry state published by a call], [$(e, lbot)$],
    [#isaconst("Analysis_Global") $x$, global], [the analysis global $x$], [$(lbot, g)$],
    table.hline(),
  ),
  placement: none,
  caption: [Which half of #isatype("dg_state") each kind of unknown uses. The
    global unknowns are named by #isatype("global_unknown").],
) <tab:eq-carrier>

Transfers never see the pair or the seeds, because the manager of
@sec:shared-facts gives each transfer the local state and access to the
analysis globals. Goblint instead combines the two kinds of value in a
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/constraint/translators.ml#L30-L32")[lifted sum],
in which each unknown holds a value of exactly one kind. Voblint uses the
product because its componentwise lattice structure keeps the Isabelle proofs
simple, at the cost of an unused #lbot half in every unknown.

=== Repeated publications #thy-badge("Voblint_Solver", "Strategy_Tree_Side_Buffering") <sec:eq-buffer>

One right-hand side can publish to the same global unknown twice. In
`if (b) { x = f(1); } else { x = f(2); }` both calls resume at the node after
the conditional, so its right-hand side contains both calls, and under the
context-insensitive policy both publish to the one seed of `f`. Declaratively, two writes to one target $g$ mean one bound:
$
  #ctor("Side") (g, a); #ctor("Side") (g, b)
  quad "means" quad
  sol(g) gt.eq a union.sq b.
$
The vendored solver applies the update rule at every #ctor("Side"), first to
$a$ and then to $a union.sq b$. The update rules record each origin's latest
contribution, the _record per origin_ of @sec:td, and all rules except join
compute the new value from these records (@sec:update-rules). In every
re-evaluation the recorded contribution therefore first shrinks to $a$ and
then grows back to $a union.sq b$. Under warrowing
the shrinking step narrows, the growing step widens again, and the solver may
not stabilize. The update rules of Stemmler et al. assume one joined
contribution per target and evaluation @stemmler25[§3], and Goblint's
per-origin narrowing rule for globals (`narrow-globs`) joins the side effects
of an evaluation before updating
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/solver/td3UpdateRule.ml#L113-L228")[`td3UpdateRule.ml`]).

Voblint therefore buffers the publications of a right-hand side and joins
those to the same target until a flush point (#isaconst("buffer_sides")).
At a node where at most one call returns, it flushes before every local read,
so that an entry state reaches the callee before the callee's result is
demanded, in the order of Goblint's normal-call transfer
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L242-L245")[`constraints.ml`]).
At a node where several calls return, such as the node after the conditional
above, flushing before each read would issue one #ctor("Side") for each call
to the same seed. The right-hand side therefore flushes only when it answers,
and
each seed receives one #ctor("Side") per evaluation. The callee's result is
then first read before its entry state arrives. This costs time but not
soundness, because the late publication changes the seed, the solver
destabilizes the callee's entry, and the caller is evaluated again with the
updated result.

Buffering changes only when publications are issued. It leaves the value, the
joined publications, and the reads of a right-hand side unchanged
(#isathm("traverse_rhs_buffer_sides"), #isathm("sides_of_rhs_buffer_sides"),
#isathm("dep_aux_buffer_sides")), so the buffered right-hand side that the
analyzer runs answers the same join of four parts as in @sec:eq-call. Under
widening update rules the timing can change the computed result, though not
the equations it solves.

== A demand-driven solve <sec:eq-example>

The generator defines a right-hand side for every pair of a node and a context
(#isaconst("compiled_routed_eqs_for")). Under entry-state contexts over
intervals the contexts range over an infinite type, and even the intervals of
one 32-bit variable number about $2^63$, so a solve cannot enumerate them. It
starts instead from one query unknown, the unknown whose value is asked for
(@sec:side-effects), which is unrelated to the analysis queries of
@sec:coop-queries. This query unknown is the result of `main` in the initial
context $c_0$
(#isaconst("dg_pipeline.root_query", thy: "DG_Analysis", display: "root_query"),
as in @apinis12[§3]), and the solve evaluates an unknown only when a right-hand side it
is solving reads it @seidl21 @tilscher26. The solve thus runs backward from
the result and discovers contexts as it goes. At a call it computes the
callee's context from the caller's value and demands the callee's result
there. @tab:eq-trace and @fig:eq-walk follow this solve on the running
example, generated from the analyzer's solver trace (Interval, warrowing,
claim #claim-ref("pg-contexts-trace")). The entry states
$e_1 = {n |-> [5, 5]}$ and $e_2 = {n |-> [4, 4]}$ route to the contexts
$c_1 = [[5, 5]]$ and $c_2 = [[4, 4]]$.

#let _trace = claim-trace("pg-contexts-trace")
#let _tctx(c) = $c_#c.slice(1)$
#let _tnode(key) = {
  let (n, c) = key.split("@")
  if n.starts-with("Seed(") {
    $ctor("Activation_Seed") med italic(#n.slice(5, -1)) space #_tctx(c)$
  } else { raw(n) }
}
#let _tunk(key) = {
  let (n, c) = key.split("@")
  if n.starts-with("Seed(") { _tnode(key) } else { $(#raw(n), #_tctx(c))$ }
}
// A value as the trace prints it: bottom, a routed entry state e_i, or the
// bindings the analyzer shows.
#let _tval(v, route: none) = if v == "⊥" { $lbot$ } else if route != none and v == route.entry {
  $e_#route.context.slice(1)$
} else { raw(v) }
#let _tbind(v) = v.matches(regex("([a-z]\w*)=(\[[^\]]*\])")).map(m => m.text)
#let _tfind(p, pred) = p.events.find(pred)

#let _trows = {
  let rows = ()
  let routed = ()
  for (i, p) in _trace.phases.enumerate() {
    let evs = p.events
    let (who, what) = if p.kind == "descent" {
      let qs = evs.filter(e => e.event == "query_local")
      let path = qs.map(e => _tnode(e.target))
      (
        [#_tnode(qs.first().current) to #_tnode(qs.last().current)],
        [the root query at #_tnode(qs.first().current) queries back through
          #path.slice(0, -1).join(", ", last: " and ") to #path.last()],
      )
    } else if p.kind == "root-seed" {
      let q = _tfind(p, e => e.event == "query_global")
      (_tnode(q.current), [#ctor("QueryG") reads #_tunk(q.target) $=$ #_tval(q.value), joins $d_0$])
    } else if p.kind == "flush" {
      let sd = _tfind(p, e => e.event == "side")
      let up = _tfind(p, e => e.event == "update_global")
      let r = rows.last().route
      (
        _tnode(sd.current),
        [flushes #ctor("Side") $(#_tunk(sd.target), #_tval(sd.value, route: r))$: the seed grows
          from #_tval(up.old) and its reader, the entry, is destabilized],
      )
    } else {
      let r = p.route
      let res = _tfind(p, e => e.event == "value_local" and e.target.starts-with("exit_"))
      let cur = res.current
      let seed = _tfind(p, e => e.event == "query_global")
      let again = r.context in routed
      // The bindings the call adds to what the continuation read before it.
      let ans = _tfind(p, e => e.event == "answer" and e.current == cur)
      let before = _tfind(p, e => (
        e.event == "value_local" and e.current == cur and not e.target.starts-with("exit_")
      ))
      let fresh = if again { _tbind(ans.value).filter(b => b not in _tbind(before.value)) } else {
        ()
      }
      // Unknowns that change after the continuation answers: the answer
      // travelling back to the root query.
      let done = evs.position(e => e.event == "answer" and e.current == cur)
      let up = if done == none { () } else {
        evs
          .slice(done)
          .filter(e => e.event == "update_local" and e.unknown != cur)
          .map(e => e.unknown)
      }
      let unchanged = evs.any(e => e.event == "side")
      // A seed the call publishes before it first queries the callee.
      let first-query = evs.position(e => e.event == "query_local")
      let published = evs
        .slice(0, if first-query == none { evs.len() } else { first-query })
        .any(e => (
          e.event == "side"
        ))
      (
        [#_tnode(cur)#if again [, again]],
        if again [
          re-reads #_tnode(before.target) and the result, whose entry now reads
          #_tval(seed.value, route: r): #fresh.map(raw).join(", ")#if unchanged [. The second flush changes nothing]#if up.len() > 1 [. The answers then propagate up through #up.slice(0, -1).map(_tnode).join(" and ") to #_tnode(up.last())]
        ] else [
          computes #_tval(r.entry, route: r) and routes to the new context #_tctx(r.context),
          #if published [publishes it to #_tunk(seed.target), ]queries #_tunk(res.target),
          which queries back to the entry, which reads #_tunk(seed.target) $=$
          #_tval(seed.value, route: r): the result is #_tval(res.value)#if up.len() > 1 [. The answers then propagate up through #up.slice(0, -1).map(_tnode).join(" and ") to #_tnode(up.last())]
        ],
      )
    }
    if p.kind == "pass" and p.route.context not in routed { routed.push(p.route.context) }
    rows.push((
      route: if p.kind == "pass" { p.route } else if rows.len() > 0 { rows.last().route } else {
        none
      },
      cells: ([#(i + 1)], who, what),
    ))
  }
  rows.map(r => r.cells).flatten()
}

#[
  #set text(size: 8.5pt)
  #figure(
    table(
      columns: (auto, auto, 1fr),
      align: (right, left, left),
      stroke: none,
      inset: (x: 4pt, y: 3pt),
      table.hline(),
      [*phase*], [*evaluating*], [*what happens*],
      table.hline(stroke: 0.5pt),
      .._trows,
      table.hline(),
    ),
    placement: none,
    caption: [The solve of the running example, condensed into phases. The
      second column names the unknown, or chain of unknowns, whose right-hand
      side the phase evaluates.],
  ) <tab:eq-trace>
]

#figure(
  {
    set text(size: 7pt)
    let wnode(pos, key, body, color: vb.neutral) = node(
      pos,
      body,
      name: label(key),
      stroke: 0.7pt + color,
      fill: color.lighten(92%),
      corner-radius: 5pt,
      inset: 3pt,
    )
    let cfg(a, b, lab: none, side: left) = edge(
      label(a),
      label(b),
      "-|>",
      stroke: 0.6pt + vb.muted,
      label: if lab == none { none } else {
        text(size: 6pt, font: "DejaVu Sans Mono", fill: vb.muted, lab)
      },
      label-side: side,
    )
    // Layout of each solver step the trace records; the phases on the
    // arrows come from the trace.
    let styles = (
      "exit_main@c0 -> pp6@c0": (bend: 45deg),
      "pp6@c0 -> pp5@c0": (bend: 45deg),
      "pp5@c0 -> pp4@c0": (bend: 45deg),
      "pp4@c0 -> pp3@c0": (bend: 45deg),
      "pp3@c0 -> pp2@c0": (bend: 45deg),
      "pp2@c0 -> entry_main@c0": (bend: 45deg),
      "entry_main@c0 -> Seed(main)@c0": (bend: 0deg),
      "pp3@c0 -> Seed(bump)@c1": (bend: 20deg, side: right),
      "pp3@c0 -> exit_bump@c1": (bend: -10deg, side: right),
      "exit_bump@c1 -> pp0@c1": (bend: -45deg, side: right),
      "exit_bump@c1 -> pp1@c1": (bend: -30deg, side: right),
      "pp0@c1 -> entry_bump@c1": (bend: -45deg, side: right),
      "entry_bump@c1 -> Seed(bump)@c1": (bend: -45deg, side: right),
      "pp4@c0 -> Seed(bump)@c2": (bend: -15deg, side: right),
      "pp4@c0 -> exit_bump@c2": (bend: 10deg),
      "exit_bump@c2 -> pp0@c2": (bend: 45deg),
      "exit_bump@c2 -> pp1@c2": (bend: 30deg),
      "pp0@c2 -> entry_bump@c2": (bend: 45deg),
      "entry_bump@c2 -> Seed(bump)@c2": (bend: 45deg),
    )
    for k in styles.keys() { assert(k in _trace.arrows, message: "the trace no longer takes " + k) }
    let step(key, phases) = {
      let st = styles.at(key, default: none)
      assert(st != none, message: "no layout for the solver step " + key)
      let (a, b) = key.split(" -> ")
      edge(
        label(a),
        label(b),
        "-|>",
        stroke: (paint: vb.accent, thickness: 0.8pt, dash: "dashed"),
        bend: st.at("bend", default: 30deg),
        label: box(
          fill: white,
          inset: 1pt,
          text(size: 6.5pt, weight: "bold", fill: vb.accent, phases.map(str).join(", ")),
        ),
        label-side: st.at("side", default: left),
        label-pos: st.at("pos", default: 0.5),
      )
    }
    diagram(
      spacing: (16mm, 5.5mm),
      wnode((0, 0), "entry_main@c0", raw("entry_main")),
      wnode(
        (-1.0, 0),
        "Seed(main)@c0",
        [$ctor("Activation_Seed") med italic("main") space c_0$],
        color: vb.called,
      ),
      wnode((0, 1), "pp2@c0", raw("pp2")),
      wnode((0, 2), "pp3@c0", raw("pp3")),
      wnode((0, 3), "pp4@c0", raw("pp4")),
      wnode((0, 4), "pp5@c0", raw("pp5")),
      wnode((0, 5), "pp6@c0", raw("pp6")),
      wnode((0, 6), "exit_main@c0", raw("exit_main")),
      wnode(
        (1.2, 0),
        "Seed(bump)@c1",
        [$ctor("Activation_Seed") med #_b space c_1$],
        color: vb.called,
      ),
      wnode((1.2, 1), "entry_bump@c1", [#raw("entry_bump"), $c_1$]),
      wnode((1.2, 2), "pp0@c1", [#raw("pp0"), $c_1$]),
      wnode((1.2, 3), "exit_bump@c1", [#raw("exit_bump"), $c_1$]),
      wnode((1.9, 2), "pp1@c1", [#raw("pp1"), $c_1$], color: vb.muted),
      wnode(
        (-1.2, 1.8),
        "Seed(bump)@c2",
        [$ctor("Activation_Seed") med #_b space c_2$],
        color: vb.called,
      ),
      wnode((-1.2, 2.8), "entry_bump@c2", [#raw("entry_bump"), $c_2$]),
      wnode((-1.2, 3.8), "pp0@c2", [#raw("pp0"), $c_2$]),
      wnode((-1.2, 4.8), "exit_bump@c2", [#raw("exit_bump"), $c_2$]),
      wnode((-1.9, 3.8), "pp1@c2", [#raw("pp1"), $c_2$], color: vb.muted),
      cfg("entry_main@c0", "pp2@c0", lab: [body(main)], side: left),
      cfg("pp4@c0", "pp5@c0", lab: [check(a == 6)], side: left),
      cfg("pp5@c0", "pp6@c0", lab: [check(b == 5)], side: left),
      cfg("pp6@c0", "exit_main@c0", lab: [return], side: left),
      cfg("Seed(bump)@c1", "entry_bump@c1", lab: [seed read], side: right),
      cfg("entry_bump@c1", "pp0@c1", lab: [body(bump)], side: right),
      cfg("pp0@c1", "exit_bump@c1", lab: [return n + 1], side: right),
      cfg("pp1@c1", "exit_bump@c1", lab: [return], side: right),
      cfg("Seed(bump)@c2", "entry_bump@c2", lab: [seed read], side: left),
      cfg("entry_bump@c2", "pp0@c2", lab: [body(bump)], side: left),
      cfg("pp0@c2", "exit_bump@c2", lab: [return n + 1], side: left),
      cfg("pp1@c2", "exit_bump@c2", lab: [return], side: left),
      .._trace.arrows.pairs().map(((k, ph)) => step(k, ph)),
    )
  },
  kind: image,
  placement: auto,
  caption: [The solve of @tab:eq-trace on the unknowns. Gray arrows are graph
    edges, including a seed feeding its entry, and blue dashed arrows are the
    solver's queries and publications, labeled with their phases. The copies
    of `bump` for $c_1$ (right) and $c_2$ (left) are demanded as the solve
    discovers those contexts. Gray `pp1`, the unreachable end of the body of
    `bump`, stays #lbot.],
) <fig:eq-walk>

The checks at `pp4` and `pp5` read the solved values
#_cli("pg-contexts-entry", "a == 6", 4) and
#_cli("pg-contexts-entry", "b == 5", 4), and the analyzer proves both. Without
contexts, $c_1 = c_2$, both calls publish to one seed, and `bump` is solved
once for both (@sec:eq-seed-global). A terminating solve thus reaches finitely
many unknowns, in the contexts it discovers.

== What a terminating solve guarantees <sec:certificate>

A solve that returns gives a valuation #sol and the set $V$ of local unknowns
it stabilized. The soundness theorem of @sec:eq-discharge needs post-solution
bounds on a set that contains the program entry and is closed under execution
steps, which executions therefore never leave. The solver instead bounds #sol on a set that contains the query unknown and is
closed under the reads of right-hand sides.

=== The certificate #thy-badge("TD", "Basics_side") <sec:cert-def>

The verified solver states its guarantee as the certificate
#isaconst("part_post_solution", thy: "Basics_side") of @sec:side-effects, over
the equation system $T$, the valuation #sol and the solved set `vars`:

#thy("part_post_solution")

$T$ maps each unknown $u$ to its strategy tree $T med u$. Evaluating a tree
under the final valuation #sol determines the answer it returns
($#isaconst("eq", thy: "Basics_side") med T med u med sol$), the local
unknowns it reads ($#isaconst("dep\<^sub>L") med T med sol med u$), and the
contributions it publishes, joined per target and #lbot where it publishes
nothing (#isaconst("sides_of_rhs")). All three are taken under the final
valuation because the unknowns a tree reads depend on the values it has
already read (@sec:eq-trees). The certificate states four facts about the
query unknown $x$ and the solved set $V$:
$
  & x in V & wide "(C1)" \
  forall u in V. med & #isaconst("dep\<^sub>L") med T med sol med u subset.eq V & wide "(C2)" \
  forall u in V. med & #isaconst("eq", thy: "Basics_side") med T med u med sol lle sol(u) & wide "(C3)" \
  forall u in V. med & #isaconst("sides_of_rhs") med (T med u) med sol lle sol & wide "(C4)"
$
(C1) puts the query unknown into the solved set, and (C2) closes the solved set under
reading. (C3) is the post-solution bound for local unknowns, and (C4) bounds
every published contribution at once, since it compares two valuations
pointwise. Together, (C3) and (C4) are the pair condition of
@sec:side-effects, and #isathm("part_post_solution_iff_rhs_pair") proves the
certificate equivalent to (C1), (C2) and that pair bound at every $u in V$.
The returned #sol may lie above the least solution, because the solver widens
and narrows at its widening points (@sec:td), and (C1) to (C4) are all the
solver guarantees about #sol.

// How many local unknowns the recorded solve of the running example certifies.
#let _local-unknowns = {
  let m = claim-text("pg-contexts-trace").match(regex("\"local_unknowns\":(\\d+)"))
  m.captures.first()
}

In the running example the query unknown is
$(ctor("FunctionResult") med italic("main"), c_0)$, and $V$ holds the
#_local-unknowns local unknowns the solve of @sec:eq-example reached. The tree
of $(italic("pp3"), c_0)$ reads $(italic("pp2"), c_0)$ and
$(ctor("FunctionResult") med italic("bump"), c_1)$, so both lie in $V$ by
(C2). (C3) at $(italic("pp3"), c_0)$ requires
$sh("combine")(q_1, sol(ctor("FunctionResult") med italic("bump"), c_1)) lle
sol(italic("pp3"), c_0)$, where $q_1$ is the resume state of the first call's
entry pair, and (C4) there requires
$e_1 lle sol(ctor("Activation_Seed") med italic("bump") space c_1)$.

=== Solved backward, used forward <sec:cert-forward>

The solver discovers unknowns backward from the result of `main`, whereas the
soundness proof follows executions forward from the entry and uses the bound
(C3) at every node an execution visits. Since the argument is the same in
every context, we speak of nodes below.

(C2) connects the two directions. A node's equation reads its predecessors,
and the node after a call reads the call site, so every node that reaches a
solved result along such steps is solved as well. It therefore suffices that
every node of a procedure reaches the procedure's result along graph edges,
whether or not the guards on the way can hold. Code after a
`return` is the case to check, since no execution reaches it but the compiler
still compiles it. In @fig:cert-forward, line 3 reaches the result through
`return 1`, and line 6 reaches it through the return edge without a value that
the compiler adds at the end of every body (@sec:compile). Once the result of
`f` is solved, (C2) therefore makes every node of `f` solved, dead code
included.

#figure(
  {
    show raw: set text(size: 7pt)
    let mark(line) = (line: line, start: 2, end: none, fill: vb.muted)
    // `main` may not return, so the example is a callee; the link opens it with its caller.
    let program = read("/shared/programs/live-nodes.vimp").trim()
    box(width: 5cm, listing(
      lang: "c",
      program.split("\nfun main").first(),
      program: program,
      highlights: (mark(3), mark(6)),
    ))
  },
  placement: none,
  kind: image,
  caption: [Code after a `return` in `f`. No execution reaches lines 3 to 6,
    yet every line reaches the result of `f`: line 3 through `return 1`, line 6
    through the final return edge.],
) <fig:cert-forward>

The proof therefore uses the nodes of procedures whose result is solved in the
same context. An execution starts at the entry of `main`, which is solved
because the result of `main` is the query unknown (C1) and every node reaches its
procedure's result. Intra edges and the step from a call site to its
continuation stay inside a procedure, and a call reads the callee's result in
the context it computes, which is then solved by (C2). A call whose entry
state the bottom test classifies as empty reads no result (@sec:eq-call), so
its callee may stay unsolved, but then no covered caller store makes the call,
since such a state describes no store. Executions thus never leave this set.

The final return edge is the implicit return of a body that reaches its end
without a `return`. In a body that always returns, it starts in dead code,
where the analyzer computes #lbot, and adds nothing. Without it, code after a
`return` could end in a node without successors, and the proof would need a
syntactic description of the code no `return` cuts off.

The restricted set is
#isaconst("dg_analysis.live_unknowns", thy: "DG_Live_Unknowns", display: "dg_analysis.live_unknowns"),
and
#isathm(
  "dg_analysis.live_unknowns_cover",
  thy: "DG_Live_Unknowns",
  display: "dg_analysis.live_unknowns_cover",
)
proves from a well-formed program and a terminating solve alone that it
contains the entry and is closed under execution steps. The final theorem
therefore needs no premise about which unknowns the solve visited.

=== The solver as a parameter #thy-badge("Voblint_Solver", "TD_Solver_Bridge") <sec:cert-param>

The soundness argument uses the certificate (C1) to (C4) of a solve that
returns and three further facts, and none of them depends on how the solver
works. The solved set is finite, the run lies in the domain on which the
certificate and finiteness hold (@sec:isabelle), and the executable run
returns that same result. Finiteness lets the analyzer combine the finitely
many contexts solved at a node into one verdict. The solver is therefore a
parameter of the analysis (#isalocale("certified_solver") states the
certificate and the three facts), and another solver, for instance one with
local side effects, attaches to Voblint by proving them.
#isathm("td_certified_solver") proves them for the vendored solver under every
update rule.

== Merging contributions to global unknowns #thy-badge("TD", "Update_rules") <sec:update-rules>

A global unknown such as a seed receives contributions from several places.
The solver merges each new contribution into the value it holds with an
_update rule_. The certificate, and with it soundness, holds under each of
the five rules below (#isathm("td_certified_solver")), so the choice affects
only precision and termination. Joining keeps every contribution exactly, but a value may then
grow along a very long chain, such as the intervals
$[0, 0], [0, 1], [0, 2], dots$ of a 32-bit counter. Widening bounds this growth
but can lose precision. Stemmler et al. compare existing update rules and
propose new ones @stemmler25[§3–4], and Tilscher et al. formalize a generic
interface for them and prove five rules sound against it @tilscher26. Voblint
exposes all five. Every rule records the latest contribution of each origin,
the right-hand side that sent it (@sec:td), and in the analyzer each origin's
contributions to one target arrive already joined (@sec:eq-buffer). The rules
differ in how they compute the value and whether they widen:
- _join_ joins each contribution into the value and never reads its
  records;
- _join per origin_ records each origin's latest contribution and reports the
  join of the records;
- _warrow_ records the same, and warrows the value toward the join of the
  records;
- _warrow per origin_ warrows the origin's old record with the new
  contribution, then joins the records;
- _bounded narrowing_ does the same, but also counts how often an origin has
  switched from widening to narrowing. Once the count reaches a bound, a
  switch to narrowing still applies one narrowing step, but further smaller
  contributions of that origin are ignored until it grows again.
@fig:update-rules runs all five on one sequence of contributions, and the
#link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/#globals")[project site]
runs them on a program with several shared callee entries. In the analyzer,
the rule decides how a callee's entry state accumulates across call sites and,
with flow-insensitive program globals (@sec:mixed-flow), how a global
accumulates its writes. No rule is more precise on every program, and on one
program the joining rules give no answer within the time limit where the
warrowing rules answer (@sec:eval-precision).

#let _rule-steps = update-rule-steps()

#figure(
  {
    set text(size: 8.5pt)
    show raw: set text(size: 8pt)
    // Bold and a nabla as well as colour, so the mark survives greyscale. An
    // infinite bound can only come from widening here.
    let cell((lo, hi)) = {
      let v = "[" + lo + "," + hi + "]"
      if "∞" in lo or "∞" in hi {
        text(fill: vb.unstable, weight: "bold", [#raw(v)#super[$nabla$]])
      } else { raw(v) }
    }
    let r(v) = raw(v)
    let rule(name, c) = [#name \ #text(size: 8pt, c)]
    let names = (
      rule([join], isaconst("update_global_always_join")),
      rule([join per origin], isaconst("update_global_per_origin")),
      rule([warrow], isaconst("update_global_warrowing_apinis")),
      rule([warrow per origin], isaconst("update_global_warrowing_per_origin")),
      rule([bounded narrowing, bound 5], isaconst("update_global_bounded_narrowing")),
    )
    table(
      columns: (auto, 1fr, 1fr, 1fr, 1fr),
      align: (
        left + horizon,
        center + horizon,
        center + horizon,
        center + horizon,
        center + horizon,
      ),
      stroke: none,
      inset: (x: 4pt, y: 2.6pt),
      table.hline(stroke: 0.5pt),
      [*rule*, vendored update], [*1:* A sends #r("[0,3]")], [*2:* B sends #r("[4,4]")],
      [*3:* A sends #r("[1,1]")], [*4:* A sends #r("[0,8]")],
      table.hline(stroke: 0.4pt),
      ..names.zip(_rule-steps).map(((n, row)) => (n, ..row.map(cell))).flatten(),
      table.hline(stroke: 0.5pt),
    )
  },
  kind: table,
  placement: auto,
  caption: [One global unknown under each update rule, from #raw("⊥"), after
    four interval contributions from origins A and B. At step 3, join per
    origin replaces A's #raw("[0,3]") by #raw("[1,1]"). Warrow widens at step
    2, because #raw("[0,4]") is not below #raw("[0,3]"), and narrows at step 3.
    Warrow per origin widens only when A's own contribution grows, and bounded
    narrowing agrees with it here. A widened bound is bold and marked $nabla$.
    The vendored rules compute the cells on the unbounded intervals
    #isatype("ivl"). At a machine kind, widening jumps to the kind's limit
    instead of $infinity$ (@sec:domain-kinds). The contributions are
    illustrative and come from no program.],
) <fig:update-rules>

== Making abstract states executable #thy-badge("Voblint_Exec", "Default_St_Base") <sec:represented-function>

The solver decides after every evaluation whether an unknown changed, so it
needs a decidable order on abstract states. The pointwise analyses of
@ch:domains, however, are specified over total functions from variable
identities to abstract values tagged with their kind (#isatype("tabs"), the
relational order analysis has its own state type). This suits proofs, but
deciding $f lle g$ for two such functions means checking $f(x) lle g(x)$ for
infinitely many identities $x$. Nipkow and
Klein meet the same problem in the abstract interpreter of Concrete Semantics
and represent a state by a finite list of variables with their values, in
which every unlisted name reads as #ltop @nipkow14[§13.6]. This is a _default
dictionary_, a finite dictionary that answers every missing key with a
default. Voblint uses the same idea with two defaults and represents a total function exactly, so it loses no
precision. We call a state in this representation an _executable state_.

Two defaults are needed because VIMP initializes globals to zero, as C does
for objects with static storage (#c11("6.7.9p10")), and leaves the locals of
`main` arbitrary within their kinds (@sec:pstep). An executable state
therefore pairs a default dictionary for locals with one for globals, each a
default and a finite list of overrides. In the initial state
(#isaconst("nonrel_init_st")), the local default is #ltop and the global
default is the abstract zero of kind `i32`. Because an abstract value carries
its kind, every declared global is overridden by the zero of its own kind.

Different representations can describe the same state, because overrides of
distinct names may appear in any order and an override equal to its default
changes nothing. A _quotient type_ (@sec:isabelle) identifies the
representations that answer every lookup alike:

#thy("default_st")

Two executable states are therefore equal exactly when every lookup agrees
(#isathm("default_st_eq_iff")), and comparing the two defaults and the
finitely many listed names decides the order
(#isathm("le_default_st_rep_code_iff")).

A lookup reads the dictionary of the identity's _location_ $ell(x)$, local or
global (#isaconst("is_global")), and returns the override if there is one and
the default otherwise. We write $d⟨l⟩$ for the lookup at location $l$. Looking
up every variable at its location gives the total function $italic("fun")(d)$
that an executable state represents (#isaconst("default_st_to_fun")), and an
executable state denotes what its function denotes for the non-relational analyses, the stores
whose values lie within their kinds and in the concretization of each
identity's abstract value:
$
  conc(d) = conc(italic("fun")(d)) = setcomp(s, #isaconst("in_kinds") med s and forall x. s(x) in conc(d⟨ell(x)⟩)).
$
The solver never computes $conc(d)$ and uses only the executable lattice
operations. The executable states instantiate the lattice classes, including widening
and narrowing, which HOL's pointwise function instances lack, on
#isatype("gdefault_st") whenever the values do, so the generic solver runs on
it unchanged.

Each lattice operation applies the value domain's operation to the two
defaults and to each listed name, so under lookup it agrees with the pointwise
operation on functions. For the join, #isathm("default_st_get_sup") states
$(d union.sq e)⟨l⟩ = d⟨l⟩ union.sq e⟨l⟩$, and analogous lemmas cover the
other operations. The transfer functions and procedure entry commute with the
represented function in the same way,
$ italic("fun")("op"_"exec" (d)) = "op"_"abs" (italic("fun")(d)), $
and since $conc(d) = conc(italic("fun")(d))$, the soundness facts of
@ch:analysis-interface transport from the abstract to the executable
operation (#isathm("nonrel_exec_spec_sound")). The commutation is proved once
for every non-relational domain, because the abstract and executable steps are
derived from the same operations.

Emptiness, on which #verdict("DEAD") rests (@ch:domains), is the one operation
the listed overrides do not decide, since an unlisted identity can make the
state empty through its default. The emptiness test therefore inspects both
defaults and the overrides that the represented function reads, and it
succeeds exactly when that function maps some identity to an empty value
(#isathm("st_is_bot_iff")). A state it finds empty denotes no store
(#isathm("st_is_bot_sound")), so replacing it by #ctor("Bot") loses no store.

== Why termination is not proved <sec:termination>

The previous sections assume that the solve returns, and no theorem shows
that every solve does. HOL admits only terminating recursion, so Isabelle
defines the solver with a domain predicate
(#isaconst("solve_dom", thy: "TD_side_upd_rule"), @sec:isabelle), the
arguments on which its recursion terminates, and proves the certificate of
@sec:certificate on that domain. The analyzer runs the executable form
#isaconst("solve_c", thy: "TD_side_upd_rule"), which returns only when the
recursion finishes, and #isathm("solve_dom_of_solve_c") turns a returned run
into domain membership. The analyzer's soundness theorems therefore have no
termination premise.

Under call strings of bounded length $k$, which include the
context-insensitive policy as $k = 0$ with the empty call string as its single
context, the contexts of a compiled program form a finite space
(#isathm("compiled_call_strings_finite")), and so do its unknowns.
Under entry-state contexts no theorem bounds the number of contexts. With
Interval, a recursion that changes its argument at every level demands a fresh
context at every level, and widening bounds the values of existing unknowns
but not their number. A recursion that passes its 32-bit argument on changed
can thus enter with about $2^32$ distinct values (#fixture(
  "21-context-sensitivity/01-entry_state_context_chain_timeout.vimp",
  label: "01-entry_state_context_chain_timeout",
)). Goblint's
configuration for the SV-COMP competition avoids this explosion by omitting
intervals from the contexts of recursive functions @saan26phd[§3.4.3].
Finitely many unknowns do not ensure termination either. Without contexts, the
interval recursion `f(x) { f(x + 1) }` entered with $x = 0$ makes the one seed
of `f` grow through $[0, 0], [0, 1], [0, 2], dots$, and the joining update
rules never widen this chain, which has about $2^31$ steps before `x + 1`
wraps (#fixture(
  "24-site-figures/01-recursion_grows_join_timeout.vimp",
  label: "01-recursion_grows_join_timeout",
)). Neither program answers within its time limit, which shows neither
divergence nor termination. Both are recursive. For partial tabulation over abstract calling contexts, Schulze Frielinghaus et al.
give a local solver that terminates on every non-recursive program, even over
lattices with infinite ascending or descending chains @schulzefrielinghaus18.

The fixed widths have a further consequence, which we argue here and the
development does not prove. A compiled program has finitely many nodes and
fixed-width variables, so its graph runs meet only finitely many stores
restricted to the identities the program uses, and a run keeps one stack of
frames, each recording a return node, a destination and the caller's store
(@sec:cstep). The graph runs are therefore those of a pushdown system with
finitely many control states and stack symbols, in which reachability is
decidable.
// TODO: cite a primary source for decidable pushdown reachability (e.g.
// Bouajjani, Esparza and Maler, CONCUR 1997, not yet in literature.bib), and
// check with a locator whether @reps95 or @sharir81 gives an exact
// interprocedural algorithm for finite state sets that restores caller locals.
Whether some graph run violates a check is thus decidable, and by the
forward simulation (@sec:csim) a negative answer carries over to every source
execution. The exact procedure explores a state space exponential in the
number of variable bits, since three 32-bit variables already give $2^96$
stores, and Voblint does not use it. Rice's theorem (@ch:intro) thus does
not apply to compiled VIMP programs, and abstraction is needed there because
of the size of the state space.

The vendored termination theorems cover top-down solvers without side effects
over a finite type of unknowns. Under this condition the solver with separate
widening and narrowing phases terminates, given widening and narrowing
operators whose iterations are ultimately stable @tilscher26jar[Thm. 2], and
the warrowing solver additionally needs a precise widening and monotonic
right-hand sides and dependencies @tilscher26jar[Cor. 1]. These theorems
need the Isabelle type of unknowns to be finite. Voblint's unknowns pair
nodes of type #isatype("cfg_node") with contexts, and this type is infinite
although each program uses finitely many nodes, so the theorems apply to none
of its configurations. Fixed widths leave only finitely many intervals at each
kind, but they make neither the type of unknowns finite nor the widening
precise. Seidl and Vogler prove on paper that their side-effecting solver
terminates when side effects target only unknowns without a right-hand side,
finitely many unknowns are encountered @seidl21[§9, Thm. 5], and the widening
and narrowing iterations are ultimately stable @seidl21[§3]. The two joining
update rules never widen, so this result does not carry over to them, and we
have not checked whether it covers the three warrowing rules of
@sec:update-rules.
// TODO: check against @seidl21[§9] whether its termination argument covers the
// vendored warrowing, warrow-per-origin and bounded-narrowing update rules.
Mechanizing such a result for the vendored solver is future work, so the end-to-end theorem is a partial-correctness result about
every report the analyzer returns.
