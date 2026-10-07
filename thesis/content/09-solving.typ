#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "@preview/cetz:0.5.2"
#import "../lib/code.typ": c11, fixture, isaconst, isai, isalocale, isathm, isatype, listing
#import "../lib/sources.typ": thy, update-rule-steps
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
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
covers the context-indexed collecting semantics, provided the solved set
contains the program entry and every unknown an execution from the entry
reaches (#isathm("activation_collect_dg_sound")). This chapter shows that the
analyzer obtains such a post-solution. Voblint solves the equations with the
verified top-down solver of Tilscher et al. @tilscher26, which is proved
partially correct. @ch:equations described each right-hand side by the value it
computes from a valuation, together with what it publishes to global unknowns.
The solver needs each right-hand side as a strategy tree (@sec:td): a small
program that reads one unknown at a time and makes every read
and every publication explicit, so that the solver can record dependencies
while it evaluates. The equations first have to be brought into this form.
Then the solver's correctness
theorem has to be connected to the premises of the soundness theorem. Both
steps assume that the solver returns; whether it does is the last question.

== Adapting the equations to the solver <sec:eq-encoding>

The solver accepts a right-hand side only as a strategy tree, uses one value
type for all unknowns, and allows side effects only to global unknowns. A direct encoding of the equations, along the lines of Apinis et al.
and Goblint, needs four things this interface does not offer
(@tab:eq-adapters). @ch:equations already stated the equations in the adapted
form; this section explains why each adaptation is needed. Only buffering
rewrites a right-hand side after the fact, and it leaves the value, the
publications and the reads unchanged (#isathm("traverse_rhs_buffer_sides"),
#isathm("sides_of_rhs_buffer_sides"), #isathm("dep_aux_buffer_sides")).

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
    [write the callee's entry, a local unknown], [side effects to globals only],
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

=== Dynamic reads <sec:eq-trees>

A local edge always reads the same unknown, its predecessor, whereas a call
chooses what to read from values it has already read. In the running example the continuation $(italic("pp3"), c_0)$ first reads the
caller $(italic("pp2"), c_0)$. Only from that value does it compute the
entry state $n = [5, 5]$, which determines the context $c_1$, and only then
does it know which result to read, $(ctor("FunctionResult") thin italic("bump"), c_1)$. A strategy tree
allows this, because each continuation receives the value just read and may
choose the next read from it. In the notation of @sec:td, the contribution of
a call at $u$ in context $c$ (#isaconst("rhs_call")) is the value of the tree
$t_"call"$,
$
  t_"call" = #ctor("QueryL") ( & (u, c), lambda d. \
                               & #ctor("Side") ( ctor("Activation_Seed") thin p space c', e, \
                               & quad #ctor("QueryL") ( (ctor("FunctionResult") thin p, c'), lambda r.
                                   #ctor("Answer", thy: "Basics_side") (sh("combine") (q, r)) ) ) ),
$
where $d$ is the caller's value, $(q, e) = enterh(d)$, $c' = ctxh(u, c, e)$,
and $r$ is the callee's result; the #ctor("Side") step publishes the entry
state to the callee's seed (@sec:eq-seed-global).
#isaconst("routed_call_program") implements this tree for a call and
additionally handles bottom entry states and several callees or entry pairs.

=== Local entries <sec:eq-seed-global>

A call has to pass its entry state $e$ to the callee's entry
$(ctor("FunctionEntry") thin p, c')$, which is a local unknown. Apinis et al.
publish to the entry directly @apinis12[§6], and Goblint does the same with
its local side effect `sidel`
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L244")[`constraints.ml`]).
The vendored solver's #ctor("Side") accepts only global unknowns, and allowing
local targets would mean changing the solver and redoing its correctness
proof.

Voblint therefore routes the entry state through the seed
$ctor("Activation_Seed") thin p space c'$ of @sec:eq-call, a global unknown: the call
publishes $e$ to it with #ctor("Side"), and the equation of the entry reads it
back with #ctor("QueryG"). In the running example `bump(5)` publishes
${n |-> [5, 5]}$ to $ctor("Activation_Seed") thin #_b space c_1$, and
$(ctor("FunctionEntry") thin italic("bump"), c_1)$ reads it. Publishing alone
does not make the solver evaluate `bump`, since it solves only unknowns that
some tree reads. The call's read of the callee's result does, and solving the
result reaches the entry, which reads the seed.

Because seeds are global unknowns, the update rule for globals merges their
contributions (@sec:update-rules). Without contexts, both calls publish to
the one seed of `bump`, and warrowing widens it. The analyzer then reports
#_cli("pg-contexts-none", "a == 6", 3) for `a == 6` with
#_cli("pg-contexts-none", "a == 6", 4), whose lower bound $-infinity$ comes
from this widening.

=== One value type <sec:global-unknowns>

A local unknown holds an abstract state of the analysis's local domain, and an
analysis global holds a value of its global domain (@sec:shared-facts). The
vendored solver has a single value type $'d$ for all unknowns, so Voblint
stores both kinds in their product: every unknown holds a pair #isatype("dg_state") of
a local and a global half, #isaconst("dg_local") and #isaconst("dg_global"),
uses one half and leaves the other at $lbot$ (@tab:eq-carrier). Order and join
on pairs work componentwise, so the solver's requirements on the value type
follow from those on the two halves. Whether an unknown is global is a matter
of the solver's interface and says nothing about the half it uses: a seed is a
global unknown that carries a local value, the entry state it passes to the
callee.

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
    [#isaconst("Analysis_Global") $v$, global], [the analysis global $v$], [$(lbot, g)$],
    table.hline(),
  ),
  placement: none,
  caption: [Which half of #isatype("dg_state") each kind of unknown uses. The
    global unknowns are named by #isatype("global_unknown").],
) <tab:eq-carrier>

Transfers never see the pair or the seeds: the manager of @sec:shared-facts
gives each transfer the local state and access to the analysis globals.
Goblint combines the two kinds of value in a
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/constraint/translators.ml#L30-L32",
)[lifted sum]
instead, in which each unknown holds a value of exactly one of the two kinds.
Voblint uses the product because its componentwise lattice structure keeps
the Isabelle proofs simple, at the price of an unused #lbot half in every
unknown.

=== Repeated publications <sec:eq-buffer>

One right-hand side can publish to the same global unknown twice. Two calls
that resume at the same node may be routed to the same callee context and then
write the same seed. Declaratively two writes to one target $g$ mean one
bound:
$
  #ctor("Side") (g, a); #ctor("Side") (g, b)
  quad "means" quad
  sol(g) gt.eq a union.sq b.
$
The vendored solver applies the update rule at every #ctor("Side"), first to
$a$ and then to $a union.sq b$. The per-origin update rules keep one record
per origin (@sec:td), so in every re-evaluation the recorded contribution
first shrinks to $a$ and then grows back to $a union.sq b$. Under warrowing
the shrinking step narrows, the growing step widens again, and the solve need
not stabilize. One joined contribution per target and evaluation is what the
update rules of Stemmler et al. assume @stemmler25[§3], and Goblint's
per-origin narrowing rule for globals, when `narrow-globs` is enabled, joins
the side effects of an evaluation before updating
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/solver/td3UpdateRule.ml#L113-L228")[`td3UpdateRule.ml`]).

#isaconst("buffer_sides") collects the publications of a right-hand side and
joins those to the same target until a flush point. Where several calls return
at a node, it flushes only when the right-hand side answers, so each seed
receives one #ctor("Side") per evaluation. Elsewhere it flushes before every
local read, so that an entry state reaches the callee before the callee's
result is demanded, in the order of Goblint's normal-call transfer
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L242-L245")[`constraints.ml`]).
A flow-insensitive global (@sec:mixed-flow) assigned on two edges into one
node therefore still receives one #ctor("Side") per edge. Where the buffer
waits for the answer, the solver does extra work: a newly routed callee is
solved from the seed's old value first, and once the joined seed is published,
the callee and then the caller are evaluated again.

Buffering changes only when publications are issued. The buffered generator
#isaconst("routed_node_rhs_buffered"), which the analyzer runs, answers the
same join of the four parts as the direct generator of @sec:eq-call. Under
widening update rules the timing can change the computed result, though not
the equations it solves. @sec:outlook-extending discusses a solver
extension that would make seeds and buffering unnecessary.

== A demand-driven solve <sec:eq-example>

The generator defines a right-hand side for every pair of a node and a context
(#isaconst("compiled_routed_eqs_for")), infinitely many under entry-state
contexts over intervals. A solve never enumerates them all. It starts from one
query, the result of `main` in the initial context $c_0$
(#isaconst("dg_pipeline.root_query", thy: "DG_Analysis", display: "root_query"),
as in @apinis12[§3]), and evaluates an unknown only when a right-hand side it
is solving reads it @seidl21 @tilscher26. The solve thus runs backwards from
the result and discovers contexts as it goes: at a call it computes the
callee's context from the caller's value and demands the callee's result
there. @tab:eq-trace and @fig:eq-walk follow this solve on the running
example, generated from the analyzer's solver trace (`--trace`, Interval,
warrowing; claim #claim-ref("pg-contexts-trace")). The entry states
$e_1 = {n |-> [5, 5]}$ and $e_2 = {n |-> [4, 4]}$ route to the contexts
$c_1 = [[5, 5]]$ and $c_2 = [[4, 4]]$.

#let _trace = claim-trace("pg-contexts-trace")
#let _tctx(c) = $c_#c.slice(1)$
#let _tnode(key) = {
  let (n, c) = key.split("@")
  if n.starts-with("Seed(") {
    $ctor("Activation_Seed") thin italic(#n.slice(5, -1)) space #_tctx(c)$
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
      "pp4@c0 -> pp3@c0": (bend: -45deg, side: right, pos: 0.25),
      "pp3@c0 -> pp2@c0": (bend: -45deg, side: right),
      "pp2@c0 -> entry_main@c0": (bend: -45deg, side: right),
      "entry_main@c0 -> Seed(main)@c0": (bend: 0deg),
      "pp3@c0 -> Seed(bump)@c1": (bend: 25deg),
      "pp3@c0 -> exit_bump@c1": (bend: -20deg, side: right),
      "exit_bump@c1 -> pp0@c1": (bend: -45deg, side: right),
      "pp0@c1 -> entry_bump@c1": (bend: -45deg, side: right),
      "entry_bump@c1 -> Seed(bump)@c1": (bend: -45deg, side: right),
      "pp4@c0 -> Seed(bump)@c2": (bend: -25deg, side: right),
      "pp4@c0 -> exit_bump@c2": (bend: 40deg),
      "exit_bump@c2 -> pp0@c2": (bend: 45deg),
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
        [$ctor("Activation_Seed") thin italic("main") space c_0$],
        color: vb.called,
      ),
      wnode((0, 1), "pp2@c0", raw("pp2")),
      wnode((0, 2), "pp3@c0", raw("pp3")),
      wnode((0, 3), "pp4@c0", raw("pp4")),
      wnode((0, 4), "pp5@c0", raw("pp5")),
      wnode((0, 5), "pp6@c0", raw("pp6")),
      wnode((0, 6), "exit_main@c0", raw("exit_main")),
      wnode(
        (1.6, 0),
        "Seed(bump)@c1",
        [$ctor("Activation_Seed") thin #_b space c_1$],
        color: vb.called,
      ),
      wnode((1.6, 1), "entry_bump@c1", [#raw("entry_bump"), $c_1$]),
      wnode((1.6, 2), "pp0@c1", [#raw("pp0"), $c_1$]),
      wnode((1.6, 3), "exit_bump@c1", [#raw("exit_bump"), $c_1$]),
      wnode(
        (-1.6, 1.8),
        "Seed(bump)@c2",
        [$ctor("Activation_Seed") thin #_b space c_2$],
        color: vb.called,
      ),
      wnode((-1.6, 2.8), "entry_bump@c2", [#raw("entry_bump"), $c_2$]),
      wnode((-1.6, 3.8), "pp0@c2", [#raw("pp0"), $c_2$]),
      wnode((-1.6, 4.8), "exit_bump@c2", [#raw("exit_bump"), $c_2$]),
      cfg("entry_main@c0", "pp2@c0", lab: [body(main)], side: right),
      cfg("pp4@c0", "pp5@c0", lab: [check(a == 6)], side: left),
      cfg("pp5@c0", "pp6@c0", lab: [check(b == 5)], side: left),
      cfg("pp6@c0", "exit_main@c0", lab: [return], side: left),
      cfg("Seed(bump)@c1", "entry_bump@c1", lab: [seed read], side: right),
      cfg("entry_bump@c1", "pp0@c1", lab: [body(bump)], side: right),
      cfg("pp0@c1", "exit_bump@c1", lab: [return n + 1], side: right),
      cfg("Seed(bump)@c2", "entry_bump@c2", lab: [seed read], side: left),
      cfg("entry_bump@c2", "pp0@c2", lab: [body(bump)], side: left),
      cfg("pp0@c2", "exit_bump@c2", lab: [return n + 1], side: left),
      .._trace.arrows.pairs().map(((k, ph)) => step(k, ph)),
    )
  },
  kind: image,
  placement: none,
  caption: [The solve of @tab:eq-trace on the unknowns. Grey arrows are graph
    edges, including a seed feeding its entry; blue dashed arrows are the
    solver's queries and publications, labelled with their phases. The solve
    runs backwards from the result of `main` and demands the copies of `bump`
    for $c_1$ (right) and $c_2$ (left) as it discovers those contexts.],
) <fig:eq-walk>

The checks at `pp4` and `pp5` read the solved values
#_cli("pg-contexts-entry", "a == 6", 4) and
#_cli("pg-contexts-entry", "b == 5", 4), and the analyzer proves both. Without
contexts, $c_1 = c_2$, both calls publish to one seed, and `bump` is solved
once for both (@sec:eq-seed-global).


A terminating solve thus reaches finitely many unknowns, in the contexts it
discovers.

== What a terminating solve guarantees <sec:certificate>

A solve that returns gives a valuation #sol and the set $V$ of local unknowns
it stabilized. The soundness theorem of @sec:eq-discharge needs the bounds of
a post-solution on a set that contains the program entry and every unknown an
execution from there can move to. The solver instead bounds #sol on $V$, and
$V$ is closed under the reads of its
right-hand sides, starting from the query: everything the result of `main`
depends on is solved. @sec:cert-def states this certificate, and
@sec:cert-forward derives from it the set the theorem needs.

=== The certificate <sec:cert-def>

The verified solver states its guarantee as the certificate
#isaconst("part_post_solution", thy: "Basics_side") of @sec:side-effects, over
the equation system $T$, the valuation #sol and the solved set `vars`:

#thy("part_post_solution")

$T$ (#isatype("eqsT", thy: "Basics_side")) maps each unknown $u$ to its
strategy tree $T med u$. Evaluating a tree under the final valuation #sol
determines three things: the answer it returns, the local unknowns it reads,
and the contributions it publishes. In Isabelle these are
$#isaconst("eq", thy: "Basics_side") med T med u med sol$ (an abbreviation of
#isaconst("traverse_rhs", thy: "Basics_side")),
$#isaconst("dep\<^sub>L") med T med sol med u$, and
#isaconst("sides_of_rhs"), which joins the published values per target and is
#lbot where the tree publishes nothing. They are taken under the final
valuation because reads depend on values read (@sec:eq-trees). With them the
certificate states four facts about the query $x$ and the solved set $V$:
$
  & x in V & wide "(C1)" \
  forall u in V. med & #isaconst("dep\<^sub>L") med T med sol med u subset.eq V & wide "(C2)" \
  forall u in V. med & #isaconst("eq", thy: "Basics_side") med T med u med sol lle sol(u) & wide "(C3)" \
  forall u in V. med & #isaconst("sides_of_rhs") med (T med u) med sol lle sol & wide "(C4)"
$
(C1) puts the query into the solved set, and (C2) closes the solved set under
reading. (C3) is the post-solution bound for local unknowns, and (C4) bounds
every published contribution at once, since it compares two valuations
pointwise (#isathm("part_post_solution_query"),
#isathm("part_post_solution_closed"),
#isathm("part_post_solution_local_bound"),
#isathm("part_post_solution_side_bound")). The returned #sol may lie above the
least solution, because the solver widens and narrows at its widening points
(@sec:td), and (C1) to (C4) are all the solver guarantees about #sol.

// How many local unknowns the recorded solve of the running example certifies.
#let _local-unknowns = {
  let m = claim-text("pg-contexts-trace").match(regex("\"local_unknowns\":(\\d+)"))
  m.captures.first()
}

In the running example the query is
$(ctor("FunctionResult") thin italic("main"), c_0)$, and $V$ holds the
#_local-unknowns local unknowns the solve of @sec:eq-example reached. The tree
of $(italic("pp3"), c_0)$ reads $(italic("pp2"), c_0)$ and, in the context
$c_1$ it computes from that value,
$(ctor("FunctionResult") thin italic("bump"), c_1)$; by (C2) both lie in $V$.
(C3) at $(italic("pp3"), c_0)$ requires
$sh("combine")(q_1, sol(ctor("FunctionResult") thin italic("bump"), c_1)) lle
sol(italic("pp3"), c_0)$, where $q_1$ is the resume state of the first call's
entry pair, and (C4) there requires
$e_1 lle sol(ctor("Activation_Seed") thin italic("bump") space c_1)$.

=== Solved backwards, used forwards <sec:cert-forward>

The solver discovers unknowns backwards from the result of `main`. The
soundness proof follows executions forwards from the entry, and each step uses
the bound (C3) at the node the execution moves to, so it needs every node an
execution visits to be solved. Soundness thus works in the opposite direction
to the solver. The argument is the same in every context, so below we speak of
nodes rather than unknowns.

In most of the program the two agree. The solver works backwards: a node's
equation reads its predecessors, so by (C2) every node that leads to a solved
result is solved as well. The exception is code after a `return`. It is
compiled into the graph, although no execution reaches it, and parts of it may
lead nowhere. In @fig:cert-forward, the dead `if` on line 3 is solved, since it
reaches the result through `return 1`. Its successor `b = 2` on line 6 is not,
since the result is unreachable from there. So the proof cannot argue that the
next node is solved because the current one is.

No execution reaches line 3, so the failing step never happens. The proof only
needs a region of the graph that contains the entry, that executions cannot
leave, and in which every node leads to a solved result. To prove these
properties once for every solve, the region should be read off the program
text, independently of a particular solve. _Liveness_ provides such a region:
it marks the code that no preceding `return` cuts off. A command _can
complete normally_ if it can end without executing a `return`. Assignments and
calls can, `return` cannot, an `if` can when one of its branches can, and a
loop always counts as completing normally. A statement is _live_ if, in each
sequence that encloses it, every command before it can complete normally. In
@fig:cert-forward, `return b` cannot complete normally, so lines 3 to 6 are not
live.

// The markers tie lines of the listing to points of the diagram beside it.
// Solved nodes are circles, the unsolved node a grey square, so the two
// differ in shape as well as colour.
#let _badge(n, col, solved, r: 0.6em) = {
  let label = align(center + horizon, text(
    size: 5.5pt,
    fill: col.darken(20%),
    weight: "bold",
    str(n),
  ))
  box(baseline: 20%, if solved {
    circle(radius: r, stroke: 0.6pt + col, fill: col.lighten(80%), inset: 0pt, label)
  } else {
    rect(
      width: 2 * r,
      height: 2 * r,
      radius: 1pt,
      stroke: 0.6pt + col,
      fill: col.lighten(80%),
      inset: 0pt,
      label,
    )
  })
}

#figure(
  {
    show raw: set text(size: 7pt)
    let mark(line, n, col, solved) = (
      line: line,
      start: 2,
      end: none,
      fill: col,
      tag: [#h(2pt)#_badge(n, col, solved, r: 0.47em)],
    )
    // `main` may not return, so the example is a callee; the link opens it with its caller.
    let program = read("/shared/programs/live-nodes.vimp").trim()
    let code = listing(
      lang: "c",
      program.split("\nfun main").first(),
      program: program,
      highlight-stroke: _ => none,
      highlight-fill: _ => none,
      highlight-inset: 0.5pt,
      highlight-outset: 0pt,
      highlight-clip: false,
      highlights: (
        mark(2, 1, vb.proved, true),
        mark(3, 2, vb.unproved, true),
        mark(6, 3, vb.muted, false),
      ),
    )
    let cones = cetz.canvas(length: 1cm, {
      import cetz.draw: *
      let (w, h) = (2.3, 2.8)
      let lab(p, body, col: vb.muted) = content(p, text(size: 6.5pt, fill: col, body))
      let solved = ((0, 0), (-w, h), (w, h))
      let reached = ((0, h), (-w, 0), (w, 0))
      line(..solved, close: true, stroke: none, fill: vb.accent.lighten(90%))
      // The parts of the forward cone outside the solved set hold no node.
      for sx in (-1, 1) {
        line(
          (0, 0),
          (sx * w, 0),
          (sx * w / 2, h / 2),
          close: true,
          stroke: none,
          fill: vb.muted.lighten(80%),
        )
        lab((sx * 1.4, 0.4), [proved\ empty])
      }
      line(
        (0, h),
        (w / 2, h / 2),
        (0, 0),
        (-w / 2, h / 2),
        close: true,
        stroke: none,
        fill: vb.proved.lighten(80%),
      )
      line(..solved, close: true, stroke: 0.7pt + vb.accent)
      line(..reached, close: true, stroke: (paint: vb.proved, thickness: 0.7pt, dash: "dashed"))
      lab((0, h + 0.2), [entry of `f`])
      lab((0, -0.2), [result of `f`])
      content(
        (w + 0.1, h - 0.15),
        text(size: 6.5pt, fill: vb.accent)[can reach\ solved result],
        anchor: "west",
      )
      content(
        (w * 0.6 + 0.3, h * 0.4),
        text(size: 6.5pt, fill: vb.proved)[reachable\ from entry],
        anchor: "west",
      )
      lab((0, 0.85), [live], col: vb.proved)
      // Outside both regions: neither reachable from the entry nor solved.
      content(
        (-2.3, 1.45),
        text(size: 6.5pt, fill: vb.muted)[neither reached\ nor solved],
        anchor: "north",
      )
      let (p1, p2, p3) = ((0, 1.8), (-1.35, 2.45), (-2.3, 1.75))
      content(p1, _badge(1, vb.proved, true))
      content(p2, _badge(2, vb.unproved, true))
      content(p3, _badge(3, vb.muted, false))
    })
    grid(
      columns: (auto, auto),
      column-gutter: 2.5em,
      align: horizon,
      box(width: 5cm, code), cones,
    )
  },
  placement: none,
  kind: image,
  caption: [Backward solving and forward execution in `f`, schematic on the
    right. Blue: nodes from which the solved result of `f` is reachable.
    Dashed green: nodes reachable from the entry. The live nodes, which the
    soundness proof uses, lie in both, and the proof shows that no execution
    visits a node that is reachable from the entry but not solved. Line 3 is solved
    but unreachable (circle 2); line 6 is neither (grey square 3). The shapes
    show direction only, not graph geometry.],
) <fig:cert-forward>

Executions never leave live code, because every edge out of a live node leads
to a live node and the entry of a procedure is live. Every live node also
reaches its procedure's result along steps that equations read, so a live node
of a procedure whose result is solved is itself solved. The proof therefore
uses the _live unknowns_, the solved nodes that are live in a procedure whose
result is solved. For the same reasons no execution visits the grey corners of
@fig:cert-forward.

In Isabelle, completing normally is #isaconst("falls_through") and liveness
is #isaconst("prog_live"); #isathm("prog_live_reaches"),
#isathm("prog_live_intra"), #isathm("prog_live_calls") and
#isathm("prog_live_entry") prove these properties. The restricted set is
#isaconst("dg_analysis.live_unknowns", thy: "DG_Live_Unknowns", display: "live_unknowns"),
and
#isathm("dg_analysis.live_unknowns_cover", thy: "DG_Live_Unknowns", display: "live_unknowns_cover")
proves from a well-formed program and a terminating solve alone that it
contains the entry and that executions cannot leave it. The final theorem
therefore needs no premise about which unknowns the solve visited.

=== The solver as a parameter <sec:cert-param>

The soundness argument uses only four facts about a solve that returns, and
none of them depends on how the solver works. They are: the result is a post-solution on the solved set
(the certificate), the solved set is finite, the run lies in the domain on
which the first two facts hold (@sec:termination), and the executable run
returns that same result. Finiteness lets
@ch:results combine the finitely many contexts solved at a node into one
verdict. Since the proof uses nothing else, the solver is a parameter of the
analysis, and another solver, for instance one with local side effects
(@sec:outlook-extending), attaches to Voblint by proving the same four facts.
In Isabelle, the analysis locale #isalocale("dg_analysis") takes the solver
as a parameter and extends #isalocale("certified_solver"), which states the
four facts. #isathm("td_certified_solver") proves them for the vendored
solver under every update rule.

== Merging contributions to global unknowns <sec:update-rules>

A global unknown such as a seed receives contributions from several places.
The solver merges each new contribution into the value it holds, and this
merge, the _update rule_, decides both precision and termination. Joining
keeps every contribution exactly but may grow forever; widening stops the
growth but loses precision. Stemmler et
al. compare existing update rules and propose new ones @stemmler25[§3–4], and Tilscher et al. formalize a
generic interface for them and prove five rules sound against it
@tilscher26; Voblint exposes all five.

Every rule keeps one record per origin, the right-hand side that sent the
contribution (@sec:td). In the analyzer, each right-hand side's contributions
to one target arrive already joined (@sec:eq-buffer). The rules differ in what
they record and whether they widen:
- _join_ joins each contribution into the value;
- _join per origin_ records each origin's latest contribution and reports the
  join of the records;
- _warrow_ records the same, and warrows the value toward the join of the
  records;
- _warrow per origin_ warrows the origin's old record with the new
  contribution, then joins the records;
- _bounded narrowing_ does the same, but also counts how often an origin has
  switched from widening to narrowing. Once the count reaches a bound, every
  later switch to narrowing takes only its first narrowing step.
@fig:update-rules runs all five on one sequence of contributions, and the
#link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/#globals")[project site]
runs them on a program with several shared callee entries. In
#isaconst("run_voblint") the rule decides how a callee's entry state
accumulates across call sites and, with flow-insensitive program globals
(@sec:mixed-flow), how a global accumulates its writes.

No rule is more precise on every program, and the rules also differ in
termination. @sec:eval-precision compares them on the programs of
@fig:rules-programs.

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
  placement: none,
  caption: [One global unknown under each update rule, from #raw("⊥"), after
    four interval contributions from origins A and B. Join per origin reports
    the join of each origin's latest contribution, so at step 3 A's
    #raw("[1,1]") replaces #raw("[0,3]"). Warrow widens at step 2, because
    #raw("[0,4]") is not below #raw("[0,3]"), and narrows at step 3; warrow per
    origin widens only when A's own contribution grows. Bounded narrowing
    agrees with warrow per origin here, since A switches to narrowing once and
    the bound 5 is never reached. A widened bound is set
    bold and marked $nabla$. The cells are read from
    #isathm("update_rules_example"), which evaluates the vendored rules with
    Voblint's interval operators; the contributions separate the rules and come
    from no program.],
) <fig:update-rules>

No solver fact is proved per rule. Each rule meets the vendored update-rule
interface (#isathm("update_rule_update_global_of")), so the certificate is
proved once, with the rule as a parameter, and holds for all five.

== Making abstract states executable <sec:represented-function>

The pointwise analyses of @ch:domains are specified over abstract states
$"Var" -> A$, total functions on variable names (the relational order
analysis has its own state type, #isatype("relc")). This suits proofs, where
lookup is function application and the lattice operations are pointwise. The solver, however, cannot compute with it: after every
evaluation it decides whether an unknown changed, and deciding $f lle g$ for two such
functions means checking $f(x) lle g(x)$ for infinitely many names $x$. Nipkow and Klein address the same
problem in the abstract interpreter of Concrete Semantics by refining total
function states to a finite representation with a default @nipkow14[§13.6]:
a state is a finite list of variables with their values, every unlisted name
reads as #ltop, and two states are compared on the listed names. Such a
representation works like a default dictionary, a finite dictionary that
answers every missing key with a default. Voblint follows the same idea but
needs two defaults. It
represents a total function exactly and therefore loses no precision. We call such a representation an _executable state carrier_ (_carrier_ for
short, distinct from the carrier of a domain, @ch:background).

VIMP initializes globals to zero, as
C does for objects with static storage (#c11("6.7.9p10")), and leaves the
locals of `main` arbitrary (@sec:vimp-vs-c). The initial state must give every local
the value #ltop and every global the value $0^sharp$, the abstract value of the
constant $0$, without listing the declared globals. Voblint's carrier
therefore keeps two default dictionaries, one for the names the program
treats as local and one for the globals, each a default paired with a finite
list of overrides. We write the state with local dictionary $(d_l, "ls")$ and
global dictionary $(d_g, "gs")$ as $⟪(d_l, "ls"), (d_g, "gs")⟫$. The initial
state is $⟪(ltop, []), (0^sharp, [])⟫$, and the least element is
$⟪(lbot, []), (lbot, [])⟫$.

Different representations can describe the same state: overrides of distinct
names may appear in any order, and an override equal to its default changes
nothing. A _quotient type_ (@sec:isabelle) identifies the representations
that answer every lookup alike:

#thy("default_st")

Two carrier states are therefore equal exactly when every lookup agrees
(#isathm("default_st_eq_iff")). Comparing the two defaults and the finitely
many listed names decides the order (#isathm("le_default_st_rep_code_iff")),
and equality tests it in both directions.

The program's global-variable classifier $cal(G)$ (@sec:pstep) assigns each
name $x$ its _location_ $ell(x)$, local or global. A lookup reads the
dictionary of the variable's location: the override if there is one, the
default otherwise. We write
$d⟨l⟩$ for the lookup at location $l$ and $d⟨l := a⟩$ for the update. Looking
up every variable at its location gives the total function $rho_(cal(G))(d)$
that a carrier state represents (#isaconst("default_st_to_fun")). A carrier
state means what its function means under the concretization
#isaconst("gamma_state") of @sec:nonrel-state, so its own concretization
(#isaconst("default_st_gamma")) is
$ sem(d) = sem(rho_(cal(G))(d)) = setcomp(s, forall x. s(x) in conc(d⟨ell(x)⟩)). $
The solver never computes $sem(d)$; it uses only the executable lattice
operations. Function states get order, join and bottom pointwise from HOL, but
no widening or narrowing. The carrier instantiates all of these classes on
#isatype("default_st") whenever the values do, so the generic solver runs on
it unchanged.

Distinct carrier states can still denote the same stores: every state whose
local default is #lbot denotes $emptyset$, yet the quotient keeps such states
apart because they represent distinct functions.

Each lattice operation is computed with the value domain's operation on the
two defaults and on each listed name, so under lookup it agrees with the
pointwise operation on functions. For the join,
#isathm("default_st_get_sup") states
$(d union.sq e)⟨l⟩ = d⟨l⟩ union.sq e⟨l⟩$, and analogous lemmas cover
bottom, order, widening and narrowing. The transfer functions must commute
with the represented function in the same way,
$ rho_(cal(G))("op"_"exec" (d)) = "op"_"abs" (rho_(cal(G))(d)), $
and since $sem(d) = sem(rho_(cal(G))(d))$, the soundness facts of
@ch:analysis-interface then transport from the abstract to the executable
operation. The locale #isalocale("dg_analysis_exec") states this commutation
for the transfer on nonempty states and for procedure entry. For primitives
proved sound it holds without a per-domain proof, because the abstract and
executable steps are derived from the same operations
(#isathm("sound_nonrelational_ops.tf_st_for_commute"), @sec:instances-supply).

Emptiness, on which `DEAD` rests (@ch:domains), is the one operation the
listed overrides do not decide: an unlisted variable can make the state empty
through its default. The carrier's test inspects the local default, the
overrides that the represented function reads, and each declared global; the
globals are listed explicitly because a program has finitely many of them, so
the global default may describe no variable at all.
#isathm("default_st_is_bot_for_gamma_iff") proves the test exact,
$ #isaconst("default_st_is_bot_for") space "globals" space d <==> sem(d) = emptyset, $
provided the list enumerates exactly the globals of $cal(G)$. Because the test
is exact, collapsing the states it finds empty to #lbot commutes with the
represented function, as the specification's collapse requires, and a state
it keeps is nonempty, which is where the numeric transfer commutes
(#isaconst("live_default_st")).

== Why termination is not proved <sec:termination>

The previous sections assume that the solve returns, and no theorem shows
that every solve does. HOL admits only terminating recursion, so Isabelle
defines the solver with a domain predicate
(#isaconst("solve_dom", thy: "TD_side_upd_rule"), @sec:isabelle), the
arguments on which its recursion terminates, and proves the certificate of
@sec:certificate on that domain. The analyzer runs the executable form
#isaconst("solve_c", thy: "TD_side_upd_rule"), which returns only when the
recursion finishes, and #isathm("solve_dom_of_solve_c") turns a returned
run into domain membership, so the theorems about #isaconst("run_voblint")
have no termination premise.

Under the unit context the unknowns of a compiled program form a finite set
(#isathm("compiled_unit_vars_finite")), and bounded call strings over a
compiled program form a finite space (#isathm("compiled_call_strings_finite")).
Under entry-state contexts we expect termination to fail for some programs.
With Interval, a recursion that changes its argument at every level demands a
fresh context at every level, and widening bounds the values of existing
unknowns but not their number (#fixture(
  "21-context-sensitivity/01-unbounded_context_chain_diverges.vimp",
  label: "01-unbounded_context_chain_diverges",
)). Finitely many unknowns do not suffice either: without contexts, the
interval recursion `f(x) { f(x + 1) }` entered with $x = 0$ makes the one seed of `f`
grow through $[0, 0], [0, 1], [0, 2], dots$, and the joining update rules never
widen this chain (#fixture(
  "24-site-figures/01-recursion_grows_join_diverges.vimp",
  label: "01-recursion_grows_join_diverges",
), @fig:rules-programs). Both programs exceed their time limits, and we expect, without proof, that
they diverge (@sec:trust-boundary).

The vendored termination theorems cover top-down solvers without side effects
over a finite type of unknowns. The solver with separate widening and narrowing
phases terminates under this condition, given widening and narrowing operators
whose iterations are ultimately stable @tilscher26jar[Thm. 2], and the
warrowing solver additionally needs a precise widening and monotonic
right-hand sides and dependencies @tilscher26jar[Cor. 1]. Voblint's unknowns
pair nodes of an infinite type with contexts, so these theorems apply to no
configuration. Seidl and Vogler prove on paper that
their side-effecting solver terminates on every system in which side effects
target only unknowns without a right-hand side, as long as only finitely many
unknowns are encountered @seidl21[§9, Thm. 5], for widening and narrowing
operators whose iteration sequences are ultimately stable @seidl21[§3]. The joining update rules never widen, so this result does not carry over to
them. Mechanizing such a result for the vendored solver is future work, so the
end-to-end theorem (@sec:headline) is a partial-correctness result about every
report the analyzer returns.
