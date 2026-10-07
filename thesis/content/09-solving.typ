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

@ch:equations ended with post-solutions. Every valuation that satisfies the
generated equations on a suitably closed set of unknowns covers the
context-indexed collecting semantics (#isathm("activation_collect_dg_sound")).
That chapter did not say how such a valuation is computed. Voblint computes it
with the verified top-down solver of Tilscher et al., which is proved partially
correct and was not written for these equations @tilscher26.

This chapter describes how the equations are solved and why the solver's
result may be used. The equations are first brought into the form the solver
accepts (@sec:eq-encoding), and @sec:eq-example follows one solve of the
running example. The solver enters the proof only through a _certificate_,
which states that the valuation it returns is a post-solution on the unknowns
it evaluated (@sec:certificate). The proof therefore holds for every update
rule the solver may use (@sec:update-rules). The solver computes with a finite
representation of abstract states (@sec:represented-function), and termination
remains a premise for each program (@sec:termination). Together, whenever the
executable solver returns for a program, the valuation it returns covers every
store that reaches each solved unknown in its context. @ch:results builds on
this statement.

== From equations to the solver <sec:eq-encoding>

The solver's interface (@sec:td) is narrower than the equations of
@ch:equations, so Voblint adapts the equations to it. No
adaptation changes what a post-solution is. The whole interface is the type of
a right-hand side, with one value type $'d$ for all unknowns (@sec:td):

#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("strategy_tree")
}

The solver evaluates a tree step by step, solves an unknown the first time a
tree queries it, and merges each #ctor("Side") into its global unknown with the
selected update rule. Reads of local and global unknowns, publications to
analysis globals, and contexts discovered during the solve map onto this
directly. So do dependencies that depend on values read earlier, which the
tree expresses (@sec:eq-trees). Three remaining mismatches need an adapter:
side effects cannot target local unknowns such as a callee's entry
(@sec:eq-seed-global), all unknowns share one value type
(@sec:global-unknowns), and repeated writes from one right-hand side share one
origin (@sec:eq-buffer).



=== Dynamic dependencies as strategy trees <sec:eq-trees>

Most right-hand sides read a fixed set of unknowns: a local edge reads its
predecessor. A call does not. In the running example the continuation
$(italic("pp3"), c_0)$ first reads the caller $(italic("pp2"), c_0)$. Only from that value does it
learn the entry state $n = 5$ and with it the context $c_1$, and only then
does it know which result to read, $(ctor("FunctionResult") thin italic("bump"), c_1)$.
The second unknown depends on the value of the first, so the equation cannot
be handed to the solver as a function of a fixed list of arguments.

A strategy tree states exactly this. It queries one unknown, receives its
value, and decides from it what to do next. In the notation of @sec:td, the
contribution $italic("call")_u (c)$ of @sec:eq-call becomes the tree
$
  italic("call")_u (c) = #ctor("QueryL") ( & (u, c), lambda d. \
    & #ctor("Side") ( ctor("Activation_Seed") thin p space c', e, \
      & quad #ctor("QueryL") ( (ctor("FunctionResult") thin p, c'), lambda r.
        #ctor("Answer", thy: "Basics_side") (sh("combine") (q, r)) ) ) ),
$
where each continuation receives the value just read: $d$ is the caller's
value, $(q, e) = enterh(d)$, $c' = ctxh(u, c, e)$, and $r$ is the callee's
result. These are lines #ineq(3) and #ineq(5) of
@sec:eq-discharge in an order the solver can execute
(#isaconst("routed_callee_call_program"), plus the bottom test of
@sec:eq-call). The analyzer runs a buffered form of this tree
(@sec:eq-buffer).

=== Publishing to local entries through activation seeds <sec:eq-seed-global>

Line #ineq(4) of @sec:eq-discharge lets the callee's entry take in the entry state
$e$ the call computed. The natural encoding is a side effect of the call into
the entry unknown $(ctor("FunctionEntry") thin p, c')$, as Apinis et al. write
it @apinis12[§6] and as Goblint does with its local side effect `sidel`
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L244")[`constraints.ml`]). The entry is a
local unknown, though, and the vendored solver's #ctor("Side") accepts only
global unknowns. Allowing local targets would mean changing the solver and
redoing its correctness proof.

The seeds of @sec:eq-call are Voblint's way around this restriction. A seed
$ctor("Activation_Seed") thin p space c'$ is a global unknown and acts as a mailbox: the call
publishes $e$ to it with #ctor("Side"), and the entry equation of
$(ctor("FunctionEntry") thin p, c')$ reads it with #ctor("QueryG"). In the
running example `bump(5)` publishes ${n |-> 5}$ to $ctor("Activation_Seed") thin #_b space c_1$,
and $(ctor("FunctionEntry") thin italic("bump"), c_1)$ reads it back (@fig:eq-unknowns).
Publishing alone does not demand `bump`, since the solver solves only unknowns
that some tree queries. The result query does: solving
$(ctor("FunctionResult") thin italic("bump"), c_1)$ reaches the entry, which queries its seed.

Because seeds are global unknowns, they inherit the update rule for globals.
Without contexts, both calls publish to the one seed of `bump`, and warrowing
widens it. The analyzer then reports
#_cli("pg-contexts-none", "a == 6", 3) for `a == 6` with
#_cli("pg-contexts-none", "a == 6", 4), whose lower bound $-infinity$ comes
from this widening.

=== One value type for all unknowns <sec:global-unknowns>

An analysis works with two kinds of value. A local unknown holds an abstract
state of its local domain, and an analysis global holds a value of its global
domain (@sec:shared-facts). The vendored solver has a single value type
$'d$ for all unknowns, so both kinds must fit into one type.

Voblint uses their product. Every unknown holds a pair #isatype("dg_state") of
a local and a global half, #isaconst("dg_local") and #isaconst("dg_global"),
uses one half and leaves the other at $lbot$ (@tab:eq-carrier). Order and join
on pairs work componentwise, so the solver's requirements on the value type
follow from those on the two halves. "Global" names the solver's kind of
unknown, not the half it uses: a seed is a global unknown that carries a local
value, the entry state it passes to the callee.

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
    [#isaconst("Analysis_Buffer"), global], [a node's own global half], [$(lbot, g)$],
    table.hline(),
  ),
  placement: auto,
  caption: [Which half of #isatype("dg_state") each kind of unknown uses. The
    global unknowns are named by #isatype("global_unknown"). No selectable
    analysis publishes to #isaconst("Analysis_Buffer").],
) <tab:eq-carrier>

Transfers never see the pair or the seeds. The manager hands a transfer the
half it needs: in the manager #isaconst("mk_dg_man") builds,
#isaconst("man_global") $v$ becomes a #ctor("QueryG") and
#isaconst("man_sideg") $v$ $g$ a #ctor("Side") on the analysis global's
unknown. Goblint uses a
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/constraint/translators.ml#L30",
)[lifted sum]
for the same purpose. Voblint uses the product because its componentwise
lattice structure keeps the Isabelle proofs simple.

=== Buffering repeated publications <sec:eq-buffer>

One right-hand side can publish to the same global unknown twice. Two edges
into a node may both assign the flow-insensitive global `g` of @sec:mixed-flow,
and two call edges that resume at the same node are separate contributions:
when both are routed to the same callee context they write the same seed
$ctor("Activation_Seed") thin p space c'$. Declaratively the two writes mean one bound:
$
  #ctor("Side") (ctor("Activation_Seed") thin p space c', a); #ctor("Side") (ctor("Activation_Seed") thin p space c', b)
  quad "means" quad
  sol(ctor("Activation_Seed") thin p space c') gt.eq a union.sq b.
$
The vendored solver joins the publications of one evaluation, but it applies
the update rule at every #ctor("Side"), first to $a$ and then to
$a union.sq b$. The per-origin rules (@sec:update-rules) keep one record
per origin (@sec:td), so in every re-evaluation the recorded
contribution first shrinks to $a$ and then grows back to $a union.sq b$. Under
warrowing the shrinking step narrows and the growing step widens again, and
the solve need not stabilize. #isaconst("buffer_sides") gives the update rule
only complete joins: it collects the publications of one right-hand side,
joins those to the same target, and issues one #ctor("Side") per target at a
flush point, which is the input the update rules of Stemmler et al. assume
@stemmler25[§3]. Where the flush points lie decides when a seed reaches the
solver. A call publishes the callee's entry state and then reads the callee's
result, and that read is what makes the solver evaluate the callee. Flushed
only when the right-hand side has answered, the publication would arrive after
the callee had been solved from an empty seed, and the seed's change would send
the caller round a second time. So at a node where at most one call returns, the
buffer flushes before every local read, and the seed is published before the
result is read, in the order of Goblint's normal-call transfer
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L242-L245")[`constraints.ml`]).
At a node where several calls return, it flushes only at the answer: an earlier
flush would write a seed the next call may write again, and the per-origin
rules would again see a partial contribution first. There a newly routed
callee is still read once with an empty seed. Goblint's narrowing rule for globals, which also keeps
one contribution per origin, joins the side effects of an evaluation before
updating
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/solver/td3UpdateRule.ml#L113-L116")[`td3UpdateRule.ml`]).
The analyzer runs the buffered generator, and @sec:cert-param carries its
certificate to the direct generator the proof speaks about.
@sec:outlook-extending discusses a solver extension that would make seeds and
buffering unnecessary.

== A solve in action <sec:eq-example>

We now follow the running example of @fig:eq-running under entry-state
contexts: the part of the equation system a solve reaches, and the order in
which the solver reaches it. The generator defines a right-hand side for every
unknown. The solver does not enumerate them. Which context-indexed unknowns it
demands depends on values it computes: $c_1 = [[5, 5]]$ and $c_2 = [[4, 4]]$
become known only after the caller values at `pp2` and `pp3` have been read. We
therefore write out the finite fragment this run reaches. The calls have the
entry pairs $(q_1, e_1) = enterh (sol(italic("pp2"), c_0))$ with
$e_1 = {n |-> [5, 5]}$ and $(q_2, e_2) = enterh (sol(italic("pp3"), c_0))$
with $e_2 = {n |-> [4, 4]}$. With $c_0$ the initial context, every post-solution
satisfies
#[
  #show math.equation: set block(breakable: true)
  #set text(size: 10pt)
  $
    sol(ctor("FunctionEntry") thin italic("main"), c_0) & gt.eq d_0 union.sq sol(ctor("Activation_Seed") thin italic("main") space c_0) & quad & "initial state and seed" \
    sol(italic("pp2"), c_0) & gt.eq sh(f)_("body(main)") (sol(ctor("FunctionEntry") thin italic("main"), c_0)) & & "local edge" \
    sol(ctor("Activation_Seed") thin #_b space c_1) & gt.eq e_1 & & "call 1 publishes" \
    sol(ctor("FunctionEntry") thin italic("bump"), c_1) & gt.eq sol(ctor("Activation_Seed") thin #_b space c_1) & & "entry reads its seed" \
    sol(italic("pp0"), c_1) & gt.eq sh(f)_("body(bump)") (sol(ctor("FunctionEntry") thin italic("bump"), c_1)) & & "local edge" \
    sol(ctor("FunctionResult") thin italic("bump"), c_1) & gt.eq sh(f)_("return n + 1") (sol(italic("pp0"), c_1)) & & "local edge" \
    sol(italic("pp3"), c_0) & gt.eq sh("combine") (q_1, sol(ctor("FunctionResult") thin italic("bump"), c_1)) & & "call 1 returns" \
    sol(ctor("Activation_Seed") thin #_b space c_2) & gt.eq e_2 & & "call 2 publishes" \
    sol(ctor("FunctionEntry") thin italic("bump"), c_2) & gt.eq sol(ctor("Activation_Seed") thin #_b space c_2) & & "entry reads its seed" \
    sol(italic("pp0"), c_2) & gt.eq sh(f)_("body(bump)") (sol(ctor("FunctionEntry") thin italic("bump"), c_2)) & & "local edge" \
    sol(ctor("FunctionResult") thin italic("bump"), c_2) & gt.eq sh(f)_("return n + 1") (sol(italic("pp0"), c_2)) & & "local edge" \
    sol(italic("pp4"), c_0) & gt.eq sh("combine") (q_2, sol(ctor("FunctionResult") thin italic("bump"), c_2)) & & "call 2 returns" \
    sol(italic("pp5"), c_0) & gt.eq sh(f)_("check(a == 6)") (sol(italic("pp4"), c_0)) & & "local edge" \
    sol(italic("pp6"), c_0) & gt.eq sh(f)_("check(b == 5)") (sol(italic("pp5"), c_0)) & & "local edge" \
    sol(ctor("FunctionResult") thin italic("main"), c_0) & gt.eq sh(f)_("return") (sol(italic("pp6"), c_0)) & & "local edge"
  $
]
Each local edge gives one inequality, each call two (its publication and its
return), and each procedure entry one that reads its seed. The entry of `main`
reads a seed as every entry does. No call publishes to it, so it stays $lbot$
and the initial state $d_0$ supplies the value. The bottom test is omitted.

@tab:eq-trace shows how the solver reaches this fragment, condensed into
phases, and @fig:eq-walk draws the same phases on the unknowns. Both are
generated from the solver trace of the executable analyzer (`--trace`,
Interval, the warrowing update rule), stored as a checked claim. Each call
resumes at a node of its own, so the buffer of @sec:eq-buffer flushes the
seed before the callee's result is read: the entry of `bump` reads the
published entry state, and each context of `bump` is solved once.

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
  #set text(size: 9pt)
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
    caption: [The solve of the running example under entry-state contexts,
      condensed into phases. Generated from the solver trace (claim
      #claim-ref("pg-contexts-trace")); the phase numbers are assigned when the thesis
      renders the trace. The second column names the unknown, or the chain of
      unknowns, whose right-hand side the phase evaluates.],
  ) <tab:eq-trace>
]

At `pp4` and `pp5` the checks read the solution: the analyzer reports
#_cli("pg-contexts-entry", "a == 6", 3) for `a == 6` with
#_cli("pg-contexts-entry", "a == 6", 4) and
#_cli("pg-contexts-entry", "b == 5", 3) for `b == 5` with
#_cli("pg-contexts-entry", "b == 5", 4). Without contexts, $c_1 = c_2$, both
calls publish to one seed, and `bump` is solved once for both.

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
      spacing: (17mm, 7mm),
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
  caption: [The solve of @tab:eq-trace drawn on the unknowns. Grey arrows are
    the edges of the graph, including a seed feeding its entry. Blue dashed
    arrows are the solver's queries and publications, labelled with the
    phases of the table. Each call publishes to its seed before it queries the
    callee, so every arrow is taken once. The solve runs backwards from the result node of `main` and demands the
    copies of `bump` for $c_1$ (right) and $c_2$ (left) as those contexts are
    discovered. Generated from the same solver trace as @tab:eq-trace.],
) <fig:eq-walk>

By the soundness theorem of @sec:eq-discharge, every post-solution of this
system covers the activation collecting semantics of the running example. The
rest of this chapter proves that a terminating solve returns one.

== The certificate between solver and semantics <sec:certificate>

=== What a solve computes <sec:cert-solve>

The solver returns a valuation #sol together with the set $V$
of local unknowns it evaluated and stabilized.

The solve is demand-driven, as the recorded solve of the running example in
@sec:eq-example showed (@tab:eq-trace, @fig:eq-walk). The generator is a function that gives a
right-hand side to every pair of a graph node and a context
(#isaconst("compiled_routed_eqs_for")), so the system is total over
node-context pairs; for a policy with an infinite context type, such as
entry-state contexts over intervals, it has infinitely many unknowns. The solver starts from a
single query, the result node of `main` in the initial context $c_0$ (#isaconst("dg_pipeline.root_query", thy: "DG_Analysis", display: "root_query")),
evaluates its right-hand side, and solves every unknown that right-hand side
reads, recursively @seidl21 @tilscher26. Starting from the result node of `main`, it
follows the predecessor and call dependencies that the evaluated right-hand
sides expose, in each context the solve discovers, and a terminating solve
reaches finitely many unknowns in total. Apinis et al.
start local solving from the same unknown @apinis12[§3]. @fig:solve-infinite
draws the system of a five-procedure program and marks the part one solve
reaches. Unknowns from which the result node cannot be reached, such as code after a
`return`, are handled in @sec:cert-forward.

// The figure is drawn by hand for the explainer page; these checks pin the
// contexts it fills and the points it leaves hollow to the analyzer's run.
#let _inf = claim-snapshot("infinite-contexts")
#assert(
  _inf.clusters.map(c => c.proc + " " + c.ctx).sorted()
    == (
      "f [0,0]",
      "f [1,1]",
      "f [2,2]",
      "f [3,3]",
      "g [0,0], [0,0]",
      "g [1,1], [0,0]",
      "h [0,0]",
      "h [1,1]",
      "main root context",
      "w ⊤",
    ),
  message: "the solve reaches other contexts than the infinite-system figure fills",
)
#assert(
  _inf.nodes.values().filter(n => n.status == "unreachable").len() == 10,
  message: "the infinite-system figure draws ten points that answer bottom",
)

#figure(
  image("/shared/generated/svg/infinite.svg", width: 100%),
  placement: auto,
  caption: [The equation system of a five-procedure program as a grid: rows
    are program points grouped by procedure, columns are contexts, one cell
    per unknown. `main` calls `w` and `f(3)`, `f` calls itself twice and calls
    `g`, and `g` calls `h`; `w` calls itself with an unconstrained value.
    Under entry-state contexts with Interval, a column label lists a
    procedure's argument values: (3) is the entry state with argument
    $[3, 3]$, (1,0) that of `g` with arguments $[1, 1]$ and $[0, 0]$, and ()
    the initial context. Filled cells are the unknowns one solve reaches, starting
    from the ringed query at the result node of `main`; hollow orange cells are read
    and answer #lbot; grey cells are never reached. Dashed arrows are the publications to callee seeds, solid arrows the
    result reads. Axis breaks marked $infinity$ stand for the rows and columns
    left out, including procedures and contexts this program never uses.
    Lifted from the explainer page; the filled contexts and hollow points are
    checked against the analyzer (claim #claim-ref("infinite-contexts")).],
) <fig:solve-infinite>

=== Post-solutions on the solved set <sec:cert-def>

The certificate is the abbreviation
#isaconst("part_post_solution", thy: "Basics_side"), stated over the equation
system $T$, the valuation #sol and the solved set `vars`:

#thy("part_post_solution")

An equation system $T$ (#isatype("eqsT", thy: "Basics_side")) maps each unknown $u$ to its
right-hand side $T med u$, a strategy tree (@sec:eq-trees). The certificate
reads off three things the tree does under the valuation #sol. Each follows the path the
queries select, feeding each continuation the value #sol gives the unknown it
reads. #isaconst("traverse_rhs", thy: "Basics_side") returns the value of the #ctor("Answer", thy: "Basics_side") at
the end of that path, the value the equation computes, and
$#isaconst("eq", thy: "Basics_side") med T med u med sol$ abbreviates
$#isaconst("traverse_rhs", thy: "Basics_side") med (T med u) med sol$.
#isaconst("sides_of_rhs") joins the values of the #ctor("Side") steps on the
path per target, #lbot where the tree publishes nothing.
$#isaconst("dep\<^sub>L") med T med sol med u$ is the set of local unknowns
the path queries.


Written out for the query $x$ and the solved set $V$ (`vars`), the
certificate requires
$
  & x in V & wide "(C1)" \
  forall u in V. med & #isaconst("dep\<^sub>L") med T med sol med u subset.eq V & wide "(C2)" \
  forall u in V. med & #isaconst("eq", thy: "Basics_side") med T med u med sol lle sol(u) & wide "(C3)" \
  forall u in V. med & #isaconst("sides_of_rhs") med (T med u) med sol lle sol & wide "(C4)"
$
Isabelle keeps local and global unknowns apart in one valuation over their
disjoint union, so $sol(u)$ in (C3) is #isai("\<sigma> (Inl u)") there. Each
condition is a lemma about the certificate, cited with its explanation below,
and #isathm("part_post_solutionI") assembles a certificate from the four.
(C3) and (C4) compare objects of
different shape. $#isaconst("eq", thy: "Basics_side") med T med u med sol$ is
a single value, the answer of the tree of $u$, so (C3) compares it with the
value #sol stores at $u$. $#isaconst("sides_of_rhs") med (T med u) med sol$ is
a whole valuation, one value per unknown, so (C4) compares two valuations
pointwise: for every global unknown $g$, what the tree publishes to $g$ lies
below $sol(g)$. Where the tree publishes nothing, including every local
unknown, its valuation is #lbot and the bound holds trivially.

// How many local unknowns the recorded solve of the running example certifies.
#let _local-unknowns = {
  let m = claim-text("pg-contexts-trace").match(regex("\"local_unknowns\":(\\d+)"))
  m.captures.first()
}

#[
  #set enum(numbering: n => "(C" + str(n) + ")")
  + puts the query into the solved set (#isathm("part_post_solution_query")). In the running example the query is
    $(ctor("FunctionResult") thin italic("main"), c_0)$.
  + closes $V$ under reading: every local unknown that the equation of a solved
    unknown reads is itself solved (#isathm("part_post_solution_closed")). Which unknowns a right-hand side reads can depend on the
    values it reads (@sec:eq-trees), so the dependencies are taken under the
    final valuation. In the running example $V$ holds the #_local-unknowns local
    unknowns the solve of @sec:eq-example reached, and the tree of
    $(italic("pp3"), c_0)$ reads $(italic("pp2"), c_0)$ and, in the context
    $c_1$ it computes from that value, $(ctor("FunctionResult") thin italic("bump"), c_1)$; both
    lie in $V$.
  + is the post-solution inequality of @ch:background for local unknowns: the
    value #sol stores at $u$ is at least what the right-hand side of $u$
    computes from the values #sol stores for the unknowns it reads
    (#isathm("part_post_solution_local_bound")). That
    right-hand side joins everything that reaches $u$: the initial state, the
    transfer along each incoming edge, the seed read at a callee entry and each
    call's combined result. So $sol(u)$ over-approximates each of them; these
    are the inequalities #ineq(1), #ineq(2), #ineq(4) and #ineq(5) of
    @sec:eq-discharge. In the running example, (C3) at $(italic("pp3"), c_0)$
    requires $sh("combine")(q_1, sol(ctor("FunctionResult") thin italic("bump"), c_1)) lle
    sol(italic("pp3"), c_0)$, the value with $a = [6, 6]$.
  + carries a call into its callee: it makes the callee's seed hold every
    entry state routed there, and global unknowns receive their values only
    through it (#isathm("part_post_solution_side_bound")). It gives the seed inequality #ineq(3) of
    @sec:eq-discharge. In the running example, (C4) at $(italic("pp3"), c_0)$ and at
    $(italic("pp4"), c_0)$ requires
    ${n |-> [5, 5]} lle sol(ctor("Activation_Seed") thin italic("bump") space c_1)$ and
    ${n |-> [4, 4]} lle sol(ctor("Activation_Seed") thin italic("bump") space c_2)$, the entry
    values of `a = bump(5)` and `b = bump(4)` (@sec:eq-example).
]

Among local unknowns the solver widens and narrows only at widening points
(@sec:td). The returned #sol may therefore lie above the least
solution, and (C1) to (C4) state all the solver guarantees about it. The
collecting-soundness theorem of @ch:equations needs the bounds (C3) and (C4)
on a set $V$ that contains the program entry and that executions cannot leave,
together with premises on entry and routing. @sec:cert-forward obtains such a
set from (C1) and (C2) by restricting $V$ to its live unknowns.

=== Which solved unknowns the proof can use <sec:cert-forward>

The certificate bounds the solver's result only on the unknowns it solved. The
soundness proof follows an execution step by step, and each step uses the
bound (C3) at the node the execution moves to. So the proof needs every node an
execution visits to be solved. The solver does not aim for that. It solves only
what the query, the result of `main`, depends on. An unknown pairs a node with
a context; the argument below works context by context, so we speak only of
nodes.

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
text. Liveness provides it: the code that no `return` cuts off. A command _can
complete normally_ if it can end without executing a `return`. Assignments and
calls can, `return` cannot, an `if` can when one of its branches can, and a
loop always counts as completing normally. A statement is _live_ if, in each
sequence that encloses it, every command before it can complete normally. In
@fig:cert-forward, `return b` cannot complete normally, so lines 3 to 6 are not
live.

// The markers tie lines of the listing to points of the diagram beside it.
#let _badge(n, col, solved, r: 0.6em) = box(baseline: 20%, circle(
  radius: r,
  stroke: (paint: col, thickness: 0.6pt, dash: if solved { none } else { "densely-dashed" }),
  fill: if solved { col.lighten(80%) } else { white },
  inset: 0pt,
  align(center + horizon, text(size: 5.5pt, fill: col, weight: "bold", str(n))),
))

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
        mark(6, 3, vb.unproved, false),
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
        lab((sx * w * 0.5, h * 0.15), [empty])
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
      lab((1.3, 2.5), [solved], col: vb.accent)
      content(
        (w * 0.6 + 0.15, h * 0.4),
        text(size: 6.5pt, fill: vb.proved)[reached\ from entry],
        anchor: "west",
      )
      lab((0, 0.85), [live], col: vb.proved)
      let (p1, p2, p3) = ((0, 1.8), (-1.35, 2.45), (-2.3, 1.65))
      // Stop the arrow at the markers' rims.
      let (dx, dy) = (p3.at(0) - p2.at(0), p3.at(1) - p2.at(1))
      let r = 0.27 / calc.sqrt(dx * dx + dy * dy)
      line(
        (p2.at(0) + r * dx, p2.at(1) + r * dy),
        (p3.at(0) - r * dx, p3.at(1) - r * dy),
        stroke: 0.6pt + vb.unproved,
        mark: (end: ">", fill: vb.unproved),
      )
      content(p1, _badge(1, vb.proved, true))
      content(p2, _badge(2, vb.unproved, true))
      content(p3, _badge(3, vb.unproved, false))
    })
    grid(
      columns: (auto, auto),
      column-gutter: 2.5em,
      align: horizon,
      box(width: 5cm, code), cones,
    )
  },
  placement: auto,
  kind: image,
  caption: [Live and solved nodes of `f`, schematic on the right. Blue: nodes
    from which the solved result is reachable. Dashed: nodes reachable from the
    entry; its grey corners are provably empty (see the text). Line 3 is dead
    but solved, and its successor on line 6 is not.],
) <fig:cert-forward>

Two facts make live code the region the proof needs. Every edge out of a live
node leads to a live node, and the entry of a procedure is live, so executions
never leave live code. Every live node reaches its procedure's result along
steps that equations read, so a live node of a procedure whose result is solved
is itself solved. The proof therefore uses the _live unknowns_: the solved
nodes that are live in a procedure whose result is solved. The same facts empty
the grey corners of @fig:cert-forward.

A call needs one more condition. The solve demands the callee's result, and so
covers the callee's entry, only when the abstract state entering the callee is
not #ctor("Bot"), since a #ctor("Bot") entry contributes nothing. The proof
therefore follows a call into the callee only from a non-#ctor("Bot") entry
state. This
suffices for soundness: an execution that makes the call enters with a store
the entry state describes, so that state is not #ctor("Bot").

In Isabelle, completing normally is #isaconst("falls_through"), liveness is
#isaconst("prog_live"), whose two facts are #isathm("prog_live_reaches") and
#isathm("prog_live_intra") with #isathm("prog_live_calls"), and the restricted set is
#isaconst("dg_analysis.live_unknowns", thy: "DG_Live_Unknowns", display: "live_unknowns").
#isathm("dg_analysis.live_unknowns_cover", thy: "DG_Live_Unknowns", display: "live_unknowns_cover")
proves from a well-formed program and a terminating solve alone that this set
contains the entry and that executions cannot leave it
(#isaconst("ctx_vars_cover_live")). The final theorem therefore needs no
premise about which unknowns the solve visited.

=== The solver as a parameter <sec:cert-param>

The soundness argument never looks inside the solver. It uses three facts
about a solve. The result is a post-solution on the solved set: this is the
certificate. The solved set is finite, which lets @ch:results combine the
finitely many contexts solved at a node into one verdict. And a run of the
executable solver that returns lies in the domain on which the first two facts
hold, so no theorem about the analyzer has to assume that the solve terminates
(@sec:termination). Since the proof uses nothing else, the solver is a
parameter of the analysis. Another solver, for instance one with local side
effects (@sec:outlook-extending), attaches to Voblint by proving the same three
facts.

In Isabelle, the analysis locale #isalocale("dg_analysis") takes the solver,
its domain predicate and its executable form as parameters. It extends the
locale #isalocale("certified_solver"), which states the three facts. For the
vendored solver they are
#isathm("TD_side_upd_rule.partial_post_solution", thy: "TD_side_upd_rule"),
#isathm("finite_stabl_solve"), proved from the solver's stable-set invariant,
and #isathm("solve_dom_of_solve_c"). #isathm("td_certified_solver") combines
them into one interpretation of #isalocale("certified_solver") for every update
rule, and every analysis registered with #isalocale("dg_analysis") cites it.

The soundness theorem of @ch:equations still needs its premises met, with the
live unknowns of @sec:cert-forward as $V$. Two gaps separate the certificate
from those premises. The theorem needs only the bounds (C3) and (C4), and on a
subset of the solved set; the bounds hold on any subset that contains the
query. And the analyzer runs the buffered generator of @sec:eq-buffer, while
the theorem speaks about the direct generator, so the certificate must carry
over from one to the other. @tab:cert-premises lists how each premise is met.
In Isabelle,
#isathm(
  "dg_analysis.routed_analysis_from_live_unknowns",
  thy: "DG_Live_Unknowns",
  display: "routed_analysis_from_live_unknowns",
)
establishes the locale #isalocale("routed_analysis") for a terminating solve.
That locale joins the soundness theorem with the _check classifier_, the
function that turns the abstract state at a check into a verdict
(@sec:verdicts). #isathm("post_bounded_of_part_post_solution") keeps the bounds
without the closure (C2), #isathm("part_post_solution_routed_node_rhs_buffered")
carries a certificate from the buffered to the direct generator, and
#isathm("dg_analysis.pp_routed", thy: "DG_Analysis", display: "pp_routed")
applies it to the analysis locale's equations.

#figure(
  table(
    columns: (auto, auto),
    align: (left, center),
    stroke: none,
    table.hline(),
    [*premise of the soundness theorem*], [*met by*],
    table.hline(stroke: 0.5pt),
    [inequalities #ineq(1) to #ineq(5) on $V$],
    [(C3) and (C4) on the direct generator],
    [program entry, executions stay in $V$], [(C1), (C2) and liveness (@sec:cert-forward)],
    [routing adequacy and totality on $V$], [the context policy (@sec:eq-routing)],
    [finitely many contexts per node], [the finiteness contract],
    table.hline(),
  ),
  placement: none,
  caption: [How a terminating solve meets the premises of
    #isalocale("routed_analysis") that depend on it, with $V$ the live
    unknowns. The first row uses the certificate's value bounds (C3) and (C4),
    the second its query and dependency closure (C1) and (C2), and the last two
    come from the context policy and the solver's finiteness. The remaining
    premises are discharged by the compiler, by assumptions of
    #isalocale("dg_analysis"), or trivially.],
) <tab:cert-premises>

Running the solver needs two further choices, neither of which changes the
certificate: how published contributions update global unknowns
(@sec:update-rules), and how abstract states are represented as executable
values (@sec:represented-function).

== One proof for five update rules <sec:update-rules>

A global unknown receives contributions from several places. The entry seed of
a procedure, for instance, receives the entry state of every call site that
enters the procedure in that context. The solver merges each new contribution
into the value it holds, and the merge decides both precision and termination.
Joining keeps every contribution exactly but may grow forever; widening stops
the growth but loses precision. Such a merge is an _update rule_. Stemmler et
al. proposed update rules @stemmler25[§3–4], and Tilscher et al. formalize a
generic interface for them and prove five rules sound against it @tilscher26.
Voblint exposes all five.

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
  switched from widening to narrowing. Once the count reaches a bound, a record
  in its narrowing phase ignores contributions below it, so each switch narrows
  only once.
@fig:update-rules runs all five on one sequence of contributions. In
#isaconst("run_voblint") the entry seeds receive contributions, and so does
the unknown of each program global when program globals are flow-insensitive
(@sec:mixed-flow). The rule therefore decides how a callee's entry state
accumulates across call sites, and how a flow-insensitive global accumulates
its writes.

No rule is more precise on every program. Per-origin warrowing helps when
several origins feed one global, as Seidl et al. show on a global that receives
one constant per location @seidl26[§1]. A recursive call that feeds its own
seed, however, is a single origin, so distinguishing origins gains nothing
there, and the rule can lose precision, as on the shrinking recursion of
@fig:rules-programs (@sec:eval-precision). The rules also differ in termination. The
two joining rules never widen a seed, so a recursion that enters with a growing
argument can keep the solve running (@sec:termination), while the three
warrowing rules widen it. On the growing recursion of @fig:rules-programs only
the warrowing rules answer, and each warrowing rule loses precision on a
program that the joining rules solve exactly.

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

No solver fact is proved per rule. Each rule meets the vendored interface
(#isathm("update_rule_update_global_of")), so one interpretation of the solver
locale, with the rule as a parameter, gives every solver fact, the certificate
included, for all five rules at once. In Isabelle, the datatype
#isatype("globals_rule") names the rules and #isaconst("update_global_of")
selects the vendored implementation. The solver runs on the state of bounded
narrowing, which keeps the counters beside the recorded contributions, and
#isaconst("lift_basic_rule") runs each of the other four rules on the
contributions alone. Only #isathm("update_rule_update_global_of") splits on the
rule and cites the five vendored interpretations.

The update rule fixes how values are combined. The values themselves still need
an executable representation, which @sec:represented-function supplies.


== Making abstract states executable <sec:represented-function>

The pointwise analyses of @ch:domains are specified over abstract states
$"Var" -> A$. The relational order analysis keeps its own state type, a set of
variable pairs (#isatype("relc")), and this section does not concern it.
For semantics and proofs this is the right representation: lookup is function
application, and the lattice operations are pointwise. It is not a
representation the solver can compute with. After every evaluation the solver
decides whether an unknown changed, and deciding $f = g$ or $f lle g$ for two
such functions means checking $forall x. f(x) = g(x)$ over infinitely many
variable names. The solver also has to compute joins, widenings, narrowings,
lookups and updates. Nipkow and Klein meet the same problem in the abstract
interpreter of Concrete Semantics and solve it by a data refinement
@nipkow14[§13.6]: a state is stored as a finite list of variables with their
values, and every unlisted name reads as #ltop, so two states can differ only
at the listed names and are compared on those. We call such an executable
representation of abstract states an _executable state carrier_, in this
chapter _carrier_ for short; it is distinct from the carrier of a domain, the
type of its domain elements (@ch:background). It works like a default dictionary, a finite dictionary that
answers every missing key with a default, and it represents a total function
exactly. It makes the existing abstraction computable and adds no new one.

One default for all names is not enough. VIMP initializes variables as C
does: globals start at zero and the locals of `main` are arbitrary
(@sec:vimp-vs-c, #c11("6.7.9p10")). The initial state must give every local
the value #ltop and every global the value $0^sharp$, the domain's abstract
value of the constant $0$, without listing the declared globals. Voblint's
carrier therefore keeps two default dictionaries: a local one for the names the
program treats as local and a global one for the globals. Each is a default
value paired with a finite list of overrides, pairs of a name and its value. As
in Isabelle, we write the state with local dictionary $(d_l, "ls")$ and global
dictionary $(d_g, "gs")$ as $⟪(d_l, "ls"), (d_g, "gs")⟫$. The initial state is
$⟪(ltop, []), (0^sharp, [])⟫$, and the least element that the solver's lattice
interface asks for is $⟪(lbot, []), (lbot, [])⟫$. The mixed-flow extension of
@sec:mixed-flow also stores states whose locals are all #lbot. In
#isaconst("run_voblint") the solver's values are lifted states, which start at
#ctor("Bot") below every carrier state. In Isabelle, a dictionary has type
#isatype("default_dict"), a carrier state #isatype("default_st_rep"), and the
notation is #isaconst("default_st_mk"). The initial state is
#isaconst("initial_default_st") (for Sign, #isaconst("cinit_sign_st")) and the
least element #isaconst("bot_default_st").

Different pairs of dictionaries can describe the same state: overrides of
distinct names may appear in any order, and an override equal to its default
changes nothing. A _quotient type_ (@sec:isabelle) makes these representations one
value. Its elements are the classes of representations that answer every lookup
alike:

#thy("default_st")

Two elements are therefore equal exactly when every lookup agrees
(#isathm("default_st_eq_iff")). A finite test decides this.
#isathm("le_default_st_rep_code_iff") shows that comparing the two defaults and
the finitely many listed names of each dictionary decides the order, and the executable
equality (#isaconst("equal_default_st")) tests the order in both
directions. An operation is defined on the finite representation and lifted to
the quotient once it is shown to give equal results on representations of the same element.

Such an element is used like a map. Looking up a variable reads the dictionary
of its partition: the variable's override if there is one, the dictionary's
default otherwise. Updating a variable records an override in the same
dictionary. Which partition a variable belongs to is decided by the program's
global-variable classifier $cal(G)$ (@sec:pstep), which assigns each name $x$
its _location_ $ell(x)$, local or global. We write $d⟨l⟩$ for the lookup at
location $l$ and $d⟨l := a⟩$ for the update. The function a state represents,
$rho_(cal(G))(d)$, looks up every variable at its location. It is the total
function on variable names that the specification uses. The same $rho_(cal(G))$
reads back a lifted state, pointwise under the lift, and a D/G state, component
by component. In Isabelle, locations have type #isatype("location"), lookup and
update are #isaconst("default_st_get") and #isaconst("default_st_set"),
$rho_(cal(G))$ is #isaconst("default_st_to_fun"), and one overloaded
#isaconst("readback") selects its instance by the argument's type.

A carrier state means what its represented function means. @sec:nonrel-state concretizes a
function state $f$ to the stores whose every variable lies in the
concretization of its value, $sem(f) = setcomp(s, forall x. s(x) in conc(f(x)))$
(#isaconst("gamma_state")). The carrier's concretization
(#isaconst("default_st_gamma")) is the concretization of its function:
$ sem(d) = sem(rho_(cal(G))(d)) = setcomp(s, forall x. s(x) in conc(d⟨ell(x)⟩)). $
It depends on $cal(G)$, which decides where each name's value is stored.
Within the refinement locale #isalocale("dg_domain_exec"), which fixes
$cal(G)$, Isabelle writes it $sem(d)$ like every other concretization of an
abstract state. Semantic statements about carrier states use it; the represented
function relates carrier operations to their counterparts on functions. The solver
never computes $sem(d)$; it uses only the executable lattice operations.

The solver needs a lattice of states: bottom to start every unknown, order and
equality to decide whether an unknown changed, join to combine contributions,
and widening and narrowing at loop heads and in the update rules. It is generic
in its value type and asks exactly for these operations
(#isalocale("bounded_semilattice_sup_bot"), #isalocale("warrowing"), and
executable equality for code generation). Function states get order, join and
bottom pointwise from HOL, as $"Var" -> A$ from $A$, but no widening or
narrowing. The carrier instantiates all of these classes on
#isatype("default_st") whenever the values do, so the solver runs on it
unchanged. The carrier lattice is infinite, since the overrides range over
infinitely many names. @fig:carrier-lattice shows its override-free
elements for one local and one global.

#figure(
  {
    set text(size: 7pt)
    // Parity values by level: bottom, the two constants, top.
    let lvl = ("⊥": 0, "e": 1, "o": 1, "⊤": 2)
    let vals = ("⊥", "e", "o", "⊤")
    let states = vals.map(x => vals.map(g => (x, g))).flatten().chunks(2)
    // Horizontal position within each level, chosen to keep edges short.
    let xpos = (
      "⊥⊥": 0,
      "e⊥": -1.5,
      "o⊥": -0.5,
      "⊥e": 1.5,
      "⊥o": 0.5,
      "⊤⊥": -2.5,
      "ee": -1.5,
      "eo": -0.5,
      "oe": 0.5,
      "oo": 1.5,
      "⊥⊤": 2.5,
      "⊤e": -1.5,
      "⊤o": -0.5,
      "e⊤": 0.5,
      "o⊤": 1.5,
      "⊤⊤": 0,
    )
    let key(st) = st.at(0) + st.at(1)
    let pos(st) = (xpos.at(key(st)), 4 - lvl.at(st.at(0)) - lvl.at(st.at(1)))
    let covers(a, b) = {
      // a is covered by b when one variable moves up one level.
      let up(u, v) = (u == "⊥" and (v == "e" or v == "o")) or ((u == "e" or u == "o") and v == "⊤")
      (a.at(0) == b.at(0) and up(a.at(1), b.at(1))) or (a.at(1) == b.at(1) and up(a.at(0), b.at(0)))
    }
    // The solver start and the initial state, each in its own colour.
    let mark = ("⊥⊥": vb.called, "⊤e": vb.accent)
    diagram(
      spacing: (11mm, 10mm),
      ..states.map(st => node(
        pos(st),
        {
          // The stores the state denotes: empty as soon as one variable is bottom.
          let spell(v) = if v == "e" { "even" } else if v == "o" { "odd" } else { v }
          let rem = ("e": "0", "o": "1")
          let cons = (("x", st.at(0)), ("g", st.at(1))).filter(((v, a)) => a in rem)
          let den = if "⊥" in st { $emptyset$ } else if cons.len() == 0 {
            ${s | "true"}$
          } else {
            let conds = cons.map(((v, a)) => $s(#v) "is" #spell(a)$)
            if conds.len() == 1 { ${s | #conds.first()}$ } else {
              // Conditions stacked on the & so both start in the same column.
              $
                {s | & #conds.at(0) and \
                     & #conds.at(1)}
              $
            }
          }
          align(center, text(
            size: 6.5pt,
          )[⟪(#spell(st.at(0)), []), \ (#spell(st.at(1)), [])⟫ \ #text(
              size: 6pt,
              fill: vb.muted,
              den,
            )])
        },
        name: label("cl-" + key(st)),
        shape: rect,
        stroke: 0.6pt + mark.at(key(st), default: vb.muted),
        fill: if key(st) in mark { mark.at(key(st)).lighten(88%) } else { white },
        corner-radius: 3pt,
        inset: 2.5pt,
      )),
      // A state with two overrides, beside the lattice: its set is over all
      // names, since the overrides pin two names and the defaults the rest.
      node(
        (4.0, 2),
        align(center, text(size: 6.5pt)[
          ⟪(even, [($x$, odd)]), #linebreak() (⊤, [($g$, even)])⟫ \
          #text(size: 6pt, fill: vb.muted)[
            $
              {s | & s(x) "is odd" and s(g) "is even" and \
                   & forall y != x "local". med s(y) "is even"}
            $
          ]]),
        name: <cl-ov>,
        stroke: 0.6pt + vb.muted,
        fill: white,
        corner-radius: 3pt,
        inset: 2.5pt,
      ),
      // Order, not covering: infinitely many override states lie in between.
      ..((label("cl-⊥e"), -15deg), (label("cl-⊤⊤"), 20deg)).map(((other, bend)) => edge(
        other,
        <cl-ov>,
        bend: bend,
        stroke: (paint: vb.muted, thickness: 0.4pt, dash: "dashed"),
      )),
      ..states
        .map(a => states
          .filter(b => covers(a, b))
          .map(b => edge(
            label("cl-" + key(a)),
            label("cl-" + key(b)),
            stroke: 0.4pt + vb.muted,
          )))
        .flatten(),
    )
  },
  kind: image,
  placement: auto,
  caption: [The override-free carrier states over Parity, part of an infinite
    lattice. A node shows its representation (the local dictionary, then the
    global one, each a default and its overrides) and, below it, its concretization $sem(d)$ restricted to
    one local $x$ and one global $g$. Edges are the carrier order. Purple is the
    least element $⟪(lbot, []), (lbot, [])⟫$; blue is the initial state
    $⟪(ltop, []), ("even", [])⟫$ (#isaconst("cinit_parity_st")), which the
    quotient also identifies with $⟪(ltop, []), ("even", [(g, "even")])⟫$. Right: a state
    with two overrides, its set written over all names. The overrides pin $x$
    and $g$, every other local takes the local default, and the other globals
    are unconstrained. Its dashed edges are order, not covering: infinitely
    many override states lie between it and its neighbours.],
) <fig:carrier-lattice>


The figure shows two ways in which states can be alike. The quotient
identifies representations that answer every lookup alike, such as
$⟪(ltop, []), ("even", [])⟫$ and $⟪(ltop, []), ("even", [(g, "even")])⟫$. Distinct carrier
elements can still denote the same stores: every node with a #lbot component
has $sem(d) = emptyset$. These nodes represent distinct functions, so the quotient keeps them apart, and a higher node denotes at least
the stores of a lower one.

Each operation is computed with the value domain's operation on the two
defaults and on each listed name, so under lookup it agrees with the
pointwise operation on functions: for the join,
#isathm("default_st_get_sup") states
$(d union.sq e)⟨l⟩ = d⟨l⟩ union.sq e⟨l⟩$, and
#isathm("default_st_get_bot"), #isathm("le_default_st_iff"),
#isathm("default_st_get_widen") and #isathm("default_st_get_narrow")
state the same for bottom, order, widening and narrowing. Point update is not a
lattice operation; the transfer functions use it for assignments.

The transfer functions must commute with taking the represented function,
$ rho_(cal(G))("op"_"exec" (d)) = "op"_"abs" (rho_(cal(G))(d)), $
and since $sem(d) = sem(rho_(cal(G))(d))$, the soundness facts of
@ch:analysis-interface for the abstract operation then transport to the
executable one. The locale #isalocale("dg_analysis_exec") states this
commutation as its commute contract, stated through the represented
function, for the transfer on nonempty states and
for procedure entry. For primitives proved sound both hold without a
per-domain proof, because the abstract and executable steps are derived from
the same operations (#isathm("sound_nonrelational_ops.tf_st_for_commute"),
#isathm("sound_nonrelational_ops.enter_st_for_commute"),
@sec:instances-supply).

Emptiness, on which `DEAD` rests, is a condition over all names (@ch:domains).
Unlike the lattice operations, it is not decided by the listed overrides
alone: an unlisted variable can make the state empty through its default.
The carrier decides it with a finite test. The test inspects the local
default, the overrides that the represented function reads, and each declared global. The
globals are listed explicitly because a program has finitely many of them, so
the global default may describe no variable at all.
#isathm("default_st_is_bot_for_gamma_iff") proves the test exact,
$ #isaconst("default_st_is_bot_for") space "globals" space d <==> sem(d) = emptyset, $
provided the supplied list enumerates exactly the globals of the
global-variable classifier.

The carrier uses the equivalence in both directions. The specification
collapses exactly the empty states to #lbot, and because the test is exact the
executable collapse commutes with taking the represented function. A state the test keeps is nonempty
(#isaconst("live_default_st")), which is where the numeric transfer
commutes with taking the represented function.

The solver can now compute every operation it needs on finite carrier values.
Whether the recursive solve returns is the remaining question.

== Why termination is not proved <sec:termination>

The analyzer answers only when the solver returns, and we do not prove that it
always does. In a proof assistant termination is a question
of the logic itself. HOL is a
logic of total functions, so a recursive definition is admitted only when its
recursion terminates; otherwise one could define $f(n) = f(n) + 1$ and derive
$0 = 1$ @nipkow14[§2.3.4]. The vendored solver's termination is not known in
general, so Isabelle defines it with a domain predicate
(#isaconst("solve_dom", thy: "TD_side_upd_rule")), the arguments on which
the recursion is well founded, and the certificate of @sec:certificate holds on
that domain. The
analyzer never assumes domain membership. It runs the executable form of the
solver, #isaconst("solve_c", thy: "TD_side_upd_rule"), which returns only when
the recursion finishes, and #isathm("solve_dom_of_solve_c") turns a returned
run into domain membership of the query. #isaconst("run_voblint") answers with a
report only after that run returned, so every report carries the membership the
certificate needs, and the theorems about the analyzer have no termination
premise.

Under the unit context the solved unknowns are finite
(#isathm("compiled_unit_vars_finite")), and bounded call strings over a
compiled program form a finite space (#isathm("compiled_call_strings_finite")).
Under entry-state contexts we expect termination to fail for some programs.
With Interval, a recursion that changes its argument at every level demands a
fresh context at every level, and widening bounds the values of existing
unknowns but not their number (#fixture(
  "21-context-sensitivity/01-unbounded_context_chain_diverges.vimp",
  label: "01-unbounded_context_chain_diverges",
)). Finitely many unknowns do not suffice either: without contexts, the
interval recursion `f(x) { f(x + 1) }` entered with $x = 0$ publishes
$[0, 0], [0, 1], [0, 2], dots$ to the one seed of `f`, and the joining update
rules never widen this chain (#fixture(
  "24-site-figures/01-recursion_grows_join_diverges.vimp",
  label: "01-recursion_grows_join_diverges",
), @fig:rules-programs). Both programs exceed their time limits, but the arguments above, which are
not machine-checked, are why we expect divergence (@sec:trust-boundary).

The vendored termination theorems cover top-down solvers without side effects
over a finite type of unknowns @tilscher26. They further require monotone
right-hand sides and the ascending chain condition for plain TD, which says
that every strictly ascending chain $a_0 llt a_1 llt dots$ is finite,
well-founded widening chains for TD with widening, and monotone right-hand sides with
well-founded widening and narrowing chains for TD with warrowing. Voblint's
unknowns pair a graph node, whose type is infinite, with a context, so these
theorems apply to no analysis configuration. Seidl and Vogler prove on paper that
their side-effecting solver terminates on every system as long as only
finitely many unknowns are encountered @seidl21[§9, Thm. 5], for widening and
narrowing operators whose iterations always stabilize @seidl21[§3]. That solver widens at a target once one origin increases it a second time
@seidl21[§9]. The joining update rules never widen, so the result does not
carry over to them. Mechanizing such a result for the vendored solver is future work, so the
end-to-end theorem (@sec:headline) is a partial-correctness result about every
report the analyzer returns.
