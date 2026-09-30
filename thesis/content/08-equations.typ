#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/math.typ": *
#import "../lib/theorems.typ": theorem
#import "../lib/figures.typ": call-edge, entry-node, intra-edge
#import "../lib/claims.typ": claim-snapshot, snapshot-cluster-of, snapshot-verdict
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
    let result(from, to, lab, side) = edge(
      from,
      to,
      "-|>",
      stroke: (paint: vb.called, thickness: 0.8pt, dash: "dashed"),
      label: text(size: 0.62em, font: "DejaVu Sans Mono", fill: vb.called, lab),
      label-side: side,
      label-pos: 0.45,
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
      scale(90%, reflow: true, diagram(
        spacing: (14mm, 4.5mm),
        entry-node((0, 0), text(size: 7pt, raw("entry_main"))),
        pt((0, 1), raw("pp2"), ""),
        pt((0, 2), raw("pp3"), ""),
        pt((0, 3), raw("pp4"), ""),
        pt((0, 4), [], "pp5"),
        pt((0, 5), [], "pp6"),
        entry-node((1.7, 0.6), text(size: 7pt, raw("entry_bump"))),
        pt((1.7, 1.8), [], "pp0"),
        entry-node((1.7, 3), text(size: 7pt, raw("exit_bump"))),
        intra-edge((0, 0), (0, 1)),
        intra-edge((0, 3), (0, 4), label: [check(a == 6)], label-side: left),
        intra-edge((0, 4), (0, 5), label: [check(b == 5)], label-side: left),
        intra-edge((1.7, 0.6), (1.7, 1.8)),
        intra-edge((1.7, 1.8), (1.7, 3), label: [return n + 1], label-side: left),
        call-edge((0, 1), (1.7, 0.6), label: [bump(5)], label-side: left, label-pos: 0.4),
        call-edge((0, 2), (1.7, 0.6), label: [bump(4)], label-side: right, label-pos: 0.35),
        result((1.7, 3), (0, 2), [a := bump(5)], right),
        result((1.7, 3), (0, 3), [b := bump(4)], left),
        resume((0, 1), (0, 2)),
        resume((0, 2), (0, 3)),
      )),
    )
  },
  kind: image,
  placement: none,
  caption: [The running example of this chapter. The call at `pp2` enters `bump`
    with argument 5 and resumes at `pp3`, which makes the second call. It
    enters `bump` with 4 and resumes at `pp4`. The two checks follow as local
    edges. Every execution passes them, and whether the analysis proves them
    depends on its contexts (@sec:eq-unknowns, @sec:eq-example). Blue dashed arrows
    are call edges, dotted ones connect a call with its continuation. Purple
    dashed arrows are the result reads: a call is not a pair of edges, and each
    continuation reads the exit of `bump` in its own equation.],
) <fig:eq-running>

== Context-indexed unknowns <sec:eq-unknowns>

The intraprocedural recipe of @ch:background keeps one unknown per graph node.
Extended naively to calls, the entry of `bump` joins both call sites and holds
$n in {4, 5}$ at best, the return at $italic("pp3")$ assigns $a in {5, 6}$, and the check
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
  placement: auto,
  scale(80%, reflow: true, diagram(
    spacing: (18mm, 8mm),
    _seed((0, 0), $italic("Seed")(#_b, c_1)$),
    _loc((0, 1), $(ctor("FunctionEntry") thin #_b, c_1)$),
    _loc((0, 2), $(ctor("FunctionResult") thin #_b, c_1)$),
    _loc((1.3, 0), $(italic("pp2"), c_0)$),
    _loc((1.3, 2), $(italic("pp3"), c_0)$),
    _loc((1.3, 5), $(italic("pp4"), c_0)$),
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
  )),
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
entry in $c'$, reads the callee's result $r$ directly from its exit unknown
$(ctor("FunctionResult") thin p, c')$ in the context it just computed, and
returns the combined value to $(k, c)$. The caller treats the callee as a black
box: its equation touches only the callee's entry and result, never the body.
The body's unknowns have their own equations, and the solver evaluates them
when the caller first reads the result. In @fig:eq-unknowns the continuation
$(italic("pp3"), c_0)$ reads $(italic("pp2"), c_0)$, computes $c_1$ from the entry value $n = 5$,
publishes that value to the seed of `bump` in $c_1$, and reads
$(ctor("FunctionResult") thin #_b, c_1)$.

When the entry value is bottom, no store enters the callee. The call then
publishes nothing, reads no result, and combines $q$ with a bottom callee
result. Apinis et al. add the same test so that procedures which are not called
are not analyzed @apinis12[§7], and Goblint's
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
  scale(80%, reflow: true, diagram(
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
  )),
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
The seed thus collects every entry value routed to $(p, c')$. Since a call
never enters the callee's body, recursion needs no special case.

== Relating routing to concrete activations <sec:eq-routing>

The equations route each call to a callee context. Soundness requires this
routing to agree with the contexts the collecting semantics uses.

The concrete side is the relation $R$ of @sec:contexts. It is the context
policy's rule for concrete calls: given the call site $u$, the caller's
context $c$, the caller's store $s$ and the entered store $s'$, it says which
callee contexts $c'$ the new activation gets. We write "$R$ admits $c'$" when
$R(u, c, s, s', c')$ holds. The trace semantics applies $R$ at every call, and
the stores of the activation belong to the bucket of each admitted $c'$. Under
call strings of length one, for instance, $R$ admits exactly $[italic("pp2")]$ for the
call `bump(5)` from `main`. The analyzer never sees $s'$. It computes an abstract entry value $e$,
chooses a context from $e$, and publishes $e$ to the callee's entry unknown for
that context. The two must meet:
$
  R "admits" c' quad ==> quad e "is routed to" c'.
$
With the soundness of the entry transfer, every concrete entered store in the
bucket of $c'$ is then covered by the value published to the entry unknown at
$c'$. Two properties make this precise.

- _Totality_: $R$ admits at least one context for every concrete call, so no
  activation is missing from the context-indexed collecting semantics.
- _Adequacy_: whenever $R$ admits $c'$ for a concrete call from a store that
  the caller's value covers, the caller's entry pair $(q, e)$ covers that store
  and the entered one (@sec:calls), $e$ routes to $c'$, and the entry unknown
  at $c'$ is among the solved unknowns.

Both are assumptions of the routed soundness theorem (@sec:eq-discharge),
proved once for each context policy. Adequacy gives #oblig("CALL"), and
totality gives #oblig("TOTAL") of @sec:contract.

#figure(
  {
    table(
      columns: (auto, auto, auto, auto),
      align: (left, left, left, left),
      inset: (x: 5pt, y: 4pt),
      stroke: none,
      table.hline(),
      [*policy*], [*$R$ admits $c'$ iff*], [*routed to*], [*why equal*],
      table.hline(stroke: 0.5pt),
      [unit], [$c' = ()$], [$()$], [both constant],
      [call strings], [$c' = "take"_k (u dot c)$], [$"take"_k (u dot c)$], [the same term],
      [entry states],
      [$c' = e|_"formals"$, $(q, e)$ covers $(s, s')$],
      [$e|_"formals"$],
      [$R$ reads the routing],
      table.hline(),
    )
  },
  placement: none,
  caption: [For a call at site $u$ from caller context $c$ with caller store
    $s$ and entered store $s'$: the contexts $R$ admits, where the equations
    route the entry value $e$, and why the two agree. $u dot c$ prepends the
    site, $e|_"formals"$ lists the formals' values in $e$, and an entry pair
    $(q, e)$ of the caller's solved value covers $(s, s')$ when
    $s in conc(q)$ and $s' in conc(e)$. Unit and call
    strings are _functional_: the context ignores abstract values.],
) <tab:eq-policies>

For unit and call strings the correspondence is direct, as the last column
shows. $R$ admits exactly the context the analyzer's own context function
computes for the concrete call (#isaconst("call_context_rel_of_fun")), so
totality is immediate. The rest of adequacy is the entry coverage of
@sec:calls and the routed entry unknown being solved.

== Routing by abstract entry state <sec:eq-entry-routing>

Unit and call-string contexts are determined by the call site and the caller
context, so the concrete call alone fixes its context. Entry-state contexts are
different: the context is part of the abstract analysis result.

Recall from @sec:calls that entry turns the caller's value into a pair
$(q, e)$: the resume value $q$ and the entry value $e$, an abstract state of
the callee. The entry-state policy takes as context the abstract values that
$e$ gives the callee's formal parameters, written $e|_"formals"$. For
`bump(n)` with $e = {n |-> [4, 5]}$, the context is $e|_"formals" = [[4, 5]]$,
a list with one entry per formal. Which context a call gets therefore depends
on the entry value computed from the caller's solved value.

This value cannot be reconstructed from one concrete call. Suppose the
caller's solved value maps $x$ to $[4, 5]$ and the program calls `bump(x)`.
Entry produces $e = {n |-> [4, 5]}$, and the equations route the call to the
context $[[4, 5]]$. One concrete execution described by this call has $x = 4$
and enters `bump` with $n = 4$:
$
  underbrace(s' = {n |-> 4}, "one concrete entered store")
  quad in quad
  underbrace(conc(e) "with" e = {n |-> [4, 5]}, "the abstract entry value")
  quad --> quad
  underbrace(c' = [[4, 5]], "the context it is routed to").
$
Abstracting this single store on its own would give $[[4, 4]]$. The equations
never publish to that context, so an activation filed there would land in an
unknown nothing fills. Entry-state contexts therefore cannot be defined by
abstracting each concrete entered store independently.

Instead, the concrete call is assigned the context of the abstract entry value
that covers it. For a call from caller store $s$ with entered store $s'$, the
relation #isaconst("routed_entry_context_rel") admits $c'$ when the entry pair
$(q, e)$ computed from the caller's solved value satisfies
$
  s in conc(q), quad s' in conc(e), quad c' = e|_"formals".
$
In the example the execution with $n = 4$ is assigned $[[4, 5]]$: the entry
value $e = {n |-> [4, 5]}$ covers $n = 4$, and $[[4, 5]]$ is where the
equations published $e$.

Adequacy is then immediate: whenever $R$ admits a context $c'$, it does so
through a covering entry value that the equations route to exactly $c'$.
Totality follows from entry coverage (@sec:calls): every concrete call covered
by the caller's value has a covering entry pair and therefore an admitted
context.

The consequence is that $R$ depends on the solved analysis, and so do the
buckets: whether a concrete call belongs to the context $[[4, 5]]$ is decided
by the entry value computed from the caller's solved value. This is not
circular. The proof first fixes a post-solution $sol$, then defines $R$ from
$sol$, and finally proves that $sol(v, c)$ covers the bucket this $R$ induces.

The dependence is necessary for entry-state contexts. Taking the context
directly from the concrete entered store gives $[[4, 4]]$ in the example,
although the equations published only to $[[4, 5]]$. Admitting every context
whose concretization contains the entered store does not help: it also admits
$[[4, 4]]$ and $[[top]]$. Adequacy would then demand coverage at unknowns the
equations never fill.

The dependence disappears in the source-level result. By totality, the union of
the buckets at a node is exactly the context-free collecting semantics there
(#isathm("ltr_collect_eq_Union_activation_collect")). The source-level theorem
of @ch:results uses only this union, so it does not depend on how concrete
calls were split into contexts: every reachable store is covered in some
context.

The policy still affects precision, because it decides which calls share an
unknown (@fig:eq-policies). A call string of length one separates the two
calls of `wrap` but merges them again in `scale`, where both arrive from the
same call site. Length two and entry-state routing keep them apart through
`scale`. @sec:eval-rq4 gives an evaluated strict separation of this kind
between call-string lengths one and two.

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
      spacing: (14mm, 4.5mm),
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
      row-gutter: 6pt,
      _policy("ctx-demo-none", [no contexts]), _policy("ctx-demo-entry", [entry states]),
      _policy("ctx-demo-k1", [call strings, length 1]),
      _policy("ctx-demo-k2", [call strings, length 2]),
    )
  },
  kind: image,
  placement: none,
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

The construction is designed so that every post-solution covers the
context-indexed collecting semantics. The theorem is independent of the
abstract domain and of the context policy: it uses only the analysis
soundness contract and the routing properties of @sec:eq-routing.

#theorem(name: [Routed collecting soundness], isa: "activation_collect_dg_sound")[
  Let $sol$ be a post-solution of the generated equations. Suppose the solved
  set contains the program entry in the initial context and is closed under
  local edges and call continuations, the initial abstract state covers the
  initial stores, the analysis satisfies #isalocale("analysis_contract"), the
  callee list at each call site contains every callee a covered call can
  enter, and routing is adequate and total. Then for every node $v$ and
  context $c$,
  $
    #isai("\<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v c") subset.eq conc_(M)(sol(v, c)).
  $
]

The solved value at $(v, c)$ thus covers every concrete store that reaches $v$
in context $c$. Since $conc_(M)$ is empty outside the solved set, no concrete
activation reaches an unknown outside it either. @tab:eq-obligations shows how
the proof meets each obligation of @ch:traces.

The proof reads the obligations off the equations. A post-solution satisfies
$italic("rhs")(v, c) lle sol(v, c)$ at every solved unknown and bounds every
publication. Unfolding the right-hand side of @sec:eq-call gives one inequality
per term. Write $v_0$ for the program entry and $c_0$ for the initial context. For a
local edge $u ->^a v$, and for a call at $u$ in context $c$ to $p$ with entry
pair $(q, e) = italic("enter")^sharp (sol(u, c))$, routed context
$c' = ctxh(u, c, e)$ and continuation $k$, a post-solution satisfies
#[
  #show math.equation: set block(breakable: true)
  $
    sol(v_0, c_0) & gt.eq d_0 & wide (1) \
    sol(v, c) & gt.eq sh(f)_a (sol(u, c)) & wide (2) \
    sol(italic("Seed")(p, c')) & gt.eq e & wide (3) \
    sol(ctor("FunctionEntry") thin p, c') & gt.eq sol(italic("Seed")(p, c')) & wide (4) \
    sol(k, c) & gt.eq italic("combine")^sharp (q, sol(ctor("FunctionResult") thin p, c')) & wide (5) \
    forall s in conc_(M)(sol(u, c)). & med exists c'. med R(u, c, s, s', c') & wide (6)
  $
]
Line (6) is not an inequality of the system but the totality premise of
@sec:eq-routing, where $s'$ is the store the call enters from $s$.
Lines (3) and (4) are #isathm("routed_seed_publish_bound_seed") and
#isathm("routed_seed_read_bound"). Each obligation follows from one line by the
same step: the line holds, and
the operation on its right is sound, so the concrete step lands in the
concretization of its left side.

#figure(
  table(
    columns: (auto, auto, 1fr),
    align: (left, left, left),
    stroke: none,
    table.hline(),
    [*obligation*], [*uses*], [*and the soundness fact*],
    table.hline(stroke: 0.5pt),
    [#oblig("INIT")], [(1)], [$d_0$ covers the initial stores],
    [#oblig("INTRA")], [(2)], [the edge transfer is sound (the contract's #oblig("INTRA"))],
    [#oblig("CALL")], [(3), (4)], [$e$ covers the entered store, and $R$ admits $c'$ (adequacy)],
    [#oblig("RETURN")], [(5)], [the return stages are sound (the contract's #oblig("RETURN"))],
    [#oblig("TOTAL")], [(6)], [none beyond the premise itself],
    table.hline(),
  ),
  placement: none,
  caption: [How #isathm("activation_collect_dg_sound") discharges the five
    obligations of @ch:traces: the inequality of the displayed system each
    one uses, and the soundness fact that turns it into coverage. Here
    $italic("combine")^sharp$ stands for the two return stages of
    @sec:calls.],
) <tab:eq-obligations>

In Isabelle the lemma is proved inside the locale
#isalocale("routed_context_base_hetero"), which carries the analysis and
routing assumptions. The lemma itself adds only the program entry and the
initial stores:
#proved("activation_collect_dg_sound")
A post-solution bounds the solved set only (#isaconst("post_bounded")), with
closure a separate premise. The locale's remaining premises hold for every
compiled program: a sound bottom test, well-formed generated programs,
finitely many edges, one call edge per call node, and seeds distinct from the
analysis global. The analyzer reaches the theorem through
#isathm("dg_spec_of_contract") and, per policy,
#isathm("fun_route_activation_collect_sound") and
#isathm("entry_state_activation_collect_sound").

== Encoding the equations for the TD solver <sec:eq-encoding>

@sec:eq-unknowns to @sec:eq-discharge say which equations we want solved and
prove every post-solution sound. Voblint solves them with the verified top-down
solver for side-effecting systems of Tilscher et al. @tilscher26 (@sec:td).
Its interface is
narrower than the equations, so Voblint adapts the equations to it. No
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
learn the entry value $n = 5$ and with it the context $c_1$, and only then
does it know which result to read, $(ctor("FunctionResult") thin #_b, c_1)$.
The second unknown depends on the value of the first, so the equation cannot
be handed to the solver as a function of a fixed list of arguments.

A strategy tree states exactly this. It queries one unknown, receives its
value, and decides from it what to do next. A call becomes the tree
$
  & #ctor("QueryL") (u, c) --> #ctor("Side") (italic("Seed")(p, c'), e) \
  & --> #ctor("QueryL") (ctor("FunctionResult") thin p, c')
    --> #ctor("Answer") (italic("combine")^sharp (q, r)),
$
where each arrow hands the value just read to the rest of the tree:
$(q, e) = italic("enter")^sharp$ of the caller's value, $c' = ctxh(u, c, e)$,
and $r$ is the value of the second query. These are lines (3) and (5) of
@sec:eq-discharge in an order the solver can execute
(#isaconst("routed_callee_call_program"), plus the bottom test of
@sec:eq-call). The analyzer runs the buffered form of this tree
(@sec:eq-buffer), which moves the #ctor("Side") behind the result query, so a
newly routed callee is first queried with an empty seed (@sec:eq-example).

=== Publishing to local entries through activation seeds <sec:eq-seed-global>

Line (4) of @sec:eq-discharge lets the callee's entry take in the entry value
$e$ the call computed. The natural encoding is a side effect of the call into
the entry unknown $(ctor("FunctionEntry") thin p, c')$, as Apinis et al. write
it @apinis12[§6] and as Goblint does with its local side effect `sidel`
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L244")[`constraints.ml`]). The entry is a
local unknown, though, and the vendored solver's #ctor("Side") accepts only
global unknowns. Allowing local targets would mean changing the solver and
redoing its correctness proof.

Voblint therefore passes the value through a mailbox. For each callee entry
and context there is a global unknown $italic("Seed")(p, c')$, the activation
seed. The call publishes $e$ to the seed with #ctor("Side"), and the entry
equation of $(ctor("FunctionEntry") thin p, c')$ reads the seed with
#ctor("QueryG"). In the running example `bump(5)` publishes ${n |-> 5}$ to
$italic("Seed")(#_b, c_1)$, and $(ctor("FunctionEntry") thin #_b, c_1)$ reads it
back (@fig:eq-unknowns). Publishing alone does not demand `bump`, since the
solver solves only unknowns that some tree queries. The result query does:
solving $(ctor("FunctionResult") thin #_b, c_1)$ reaches the entry, which
queries its seed. In the buffered analyzer this first query sees the old seed
value. The publication is flushed afterwards and, since it grows the seed,
destabilizes the entry for another evaluation (@sec:eq-buffer).

Because seeds are global unknowns, they inherit the update rule for globals:
without contexts, warrowing widens the one seed of `bump` to the lower bound
$-infinity$ reported in @sec:eq-unknowns.

=== One value type for all unknowns <sec:global-unknowns>

An analysis works with two kinds of value. A local unknown holds an abstract
state of its local domain, and an analysis global holds a value of its global
domain (@sec:analysis-globals). The vendored solver has a single value type
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
    [#isaconst("Activation_Seed"), global], [an entry value published by a call], [$(e, lbot)$],
    [#isaconst("Analysis_Global"), global], [a fact an analysis shares], [$(lbot, g)$],
    table.hline(),
  ),
  placement: auto,
  caption: [Which half of #isatype("dg_state") each kind of unknown uses. The
    global unknowns are named by #isatype("global_unknown").],
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

A node all of whose incoming edges publish the analysis global writes the same
global unknown $kappa$ twice (@sec:mixed-flow). Declaratively the two writes
mean one bound:
$
  #ctor("Side") (kappa, a); #ctor("Side") (kappa, b)
  quad "means" quad
  sol(kappa) gt.eq a union.sq b.
$
The solver's per-origin update rules keep one record per publishing equation
(@sec:update-rules), so the second write updates the record of the first, and
under warrowing repeated evaluations may alternate between the two recorded
contributions instead of converging.
#isaconst("buffer_sides") restores the declarative meaning: it collects the
publications of one right-hand side, joins those to the same target, and
issues one $#ctor("Side") (kappa, a union.sq b)$ when the right-hand side has
answered. This also delays every publication behind the queries of its
equation. In the running example a new callee context is therefore first
read with an empty seed, and the flush destabilizes it for a second pass
(@sec:eq-example). Goblint's per-origin update rule does
the same join inside the solver
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/solver/td3UpdateRule.ml#L113-L116")[`td3UpdateRule.ml`]).
The analyzer runs the buffered generator, and #isathm("part_post_solution_routed_node_rhs_buffered")
transfers the post-solution certificate to the direct one the proof speaks
about. A verified solver with local side effects and per-evaluation joining,
as Goblint's solvers provide, would make seeds and buffering unnecessary
(@sec:outlook-extending).

== The running example, solved <sec:eq-example>

We close with the running example of @fig:eq-running under entry-state
contexts: the part of the equation system a solve reaches, and the order in
which the solver reaches it. The generator defines a right-hand side for every
unknown. The solver does not enumerate them. Which context-indexed unknowns it
demands depends on values it computes: $c_1 = [[5, 5]]$ and $c_2 = [[4, 4]]$
become known only after the caller values at `pp2` and `pp3` have been read. We
therefore write out the finite fragment this run reaches. The calls have the
entry pairs $(q_1, e_1) = italic("enter")^sharp (sol(italic("pp2"), c_0))$ with
$e_1 = {n |-> [5, 5]}$ and $(q_2, e_2) = italic("enter")^sharp (sol(italic("pp3"), c_0))$
with $e_2 = {n |-> [4, 4]}$. With $c_0$ the initial context, every post-solution
satisfies
#[
  #show math.equation: set block(breakable: true)
  #set text(size: 10pt)
  $
    sol(italic("entry")_"main", c_0) & gt.eq d_0 union.sq sol(italic("Seed")(italic("main"), c_0)) & quad & "initial state and seed" \
    sol(italic("pp2"), c_0) & gt.eq sh(f)_("body(main)") (sol(italic("entry")_"main", c_0)) & & "local edge" \
    sol(italic("Seed")(#_b, c_1)) & gt.eq e_1 & & "call 1 publishes" \
    sol(ctor("FunctionEntry") thin #_b, c_1) & gt.eq sol(italic("Seed")(#_b, c_1)) & & "entry reads its seed" \
    sol(italic("pp0"), c_1) & gt.eq sh(f)_("body(bump)") (sol(ctor("FunctionEntry") thin #_b, c_1)) & & "local edge" \
    sol(ctor("FunctionResult") thin #_b, c_1) & gt.eq sh(f)_("return n + 1") (sol(italic("pp0"), c_1)) & & "local edge" \
    sol(italic("pp3"), c_0) & gt.eq italic("combine")^sharp (q_1, sol(ctor("FunctionResult") thin #_b, c_1)) & & "call 1 returns" \
    sol(italic("Seed")(#_b, c_2)) & gt.eq e_2 & & "call 2 publishes" \
    sol(ctor("FunctionEntry") thin #_b, c_2) & gt.eq sol(italic("Seed")(#_b, c_2)) & & "entry reads its seed" \
    sol(italic("pp0"), c_2) & gt.eq sh(f)_("body(bump)") (sol(ctor("FunctionEntry") thin #_b, c_2)) & & "local edge" \
    sol(ctor("FunctionResult") thin #_b, c_2) & gt.eq sh(f)_("return n + 1") (sol(italic("pp0"), c_2)) & & "local edge" \
    sol(italic("pp4"), c_0) & gt.eq italic("combine")^sharp (q_2, sol(ctor("FunctionResult") thin #_b, c_2)) & & "call 2 returns" \
    sol(italic("pp5"), c_0) & gt.eq sh(f)_("check(a == 6)") (sol(italic("pp4"), c_0)) & & "local edge" \
    sol(italic("pp6"), c_0) & gt.eq sh(f)_("check(b == 5)") (sol(italic("pp5"), c_0)) & & "local edge" \
    sol(italic("exit")_"main", c_0) & gt.eq sh(f)_("return") (sol(italic("pp6"), c_0)) & & "local edge"
  $
]
Each local edge gives one inequality, each call two (its publication and its
return), and each procedure entry one that reads its seed. The entry of `main`
reads a seed as every entry does. No call publishes to it, so it stays $lbot$
and the initial state $d_0$ supplies the value. The bottom test is omitted.

@tab:eq-trace shows how the solver reaches this fragment, condensed into
phases, and @fig:eq-walk draws the same phases on the unknowns. Both are
recorded from an instrumented run of the generated solver (Interval, the
warrowing update rule). Two things stand out. The seed of a new context is read
before anything is published to it, because the analyzer runs the buffered
form of the call (@sec:eq-buffer): the publication is flushed only after the
result query has returned. The first pass through `bump` therefore reads
$lbot$ and returns $lbot$. The flush then destabilizes the entry, and a second
pass computes the real result.

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
      [1],
      [#raw("exit_main") to `pp2`],
      [the root query at #raw("exit_main") queries back through `pp6`, `pp5`, `pp4` and `pp3` to `pp2`],
      [2],
      [#raw("entry_main")],
      [#ctor("QueryG") reads $italic("Seed")(italic("main"), c_0) = lbot$, joins $d_0$],
      [3],
      [`pp3`],
      [computes $e_1$ and routes to the new context $c_1$, queries $(ctor("FunctionResult") thin #_b, c_1)$, which queries back to the entry, which reads $italic("Seed")(#_b, c_1) = lbot$: the result is $lbot$],
      [4],
      [`pp3`],
      [flushes #ctor("Side") $(italic("Seed")(#_b, c_1), e_1)$: the seed grows and its reader, the entry, is destabilized],
      [5],
      [`pp3`, again],
      [re-reads `pp2` and the result, whose entry now reads $e_1$: $a = 6$. The second flush changes nothing],
      [6],
      [`pp4`],
      [as phase 3 for the second call: routes to $c_2$, reads $italic("Seed")(#_b, c_2) = lbot$],
      [7], [`pp4`], [flushes $e_2$ to $italic("Seed")(#_b, c_2)$, destabilizing its entry],
      [8],
      [`pp4`, again],
      [second pass: $b = 5$. The answers then propagate up through `pp5` and `pp6` to #raw("exit_main")],
      table.hline(),
    ),
    placement: none,
    caption: [The solve of the running example under entry-state contexts,
      condensed into phases. Recorded from an instrumented run of the generated
      solver. Each phase evaluates the right-hand side of the unknown in the
      second column.],
  ) <tab:eq-trace>
]

At `pp4` the two checks read the solution: the analyzer reports
#_cli("pg-contexts-entry", "a == 6", 3) for `a == 6` with
#_cli("pg-contexts-entry", "a == 6", 4) and
#_cli("pg-contexts-entry", "b == 5", 3) for `b == 5` with
#_cli("pg-contexts-entry", "b == 5", 4). Without contexts, $c_1 = c_2$, both
calls publish to one seed, and `bump` is solved once for both.

#figure(
  {
    set text(size: 7pt)
    let wnode(pos, name, body, color: vb.neutral) = node(
      pos,
      body,
      name: name,
      stroke: 0.7pt + color,
      fill: color.lighten(92%),
      corner-radius: 5pt,
      inset: 3pt,
    )
    let cfg(a, b, lab: none, side: left) = edge(
      a,
      b,
      "-|>",
      stroke: 0.6pt + vb.muted,
      label: if lab == none { none } else {
        text(size: 6pt, font: "DejaVu Sans Mono", fill: vb.muted, lab)
      },
      label-side: side,
    )
    let step(a, b, n, bend: 30deg, side: left, pos: 0.5) = edge(
      a,
      b,
      "-|>",
      stroke: (paint: vb.accent, thickness: 0.8pt, dash: "dashed"),
      bend: bend,
      label: box(
        fill: white,
        inset: 1pt,
        text(size: 6.5pt, weight: "bold", fill: vb.accent, if type(n) == str { n } else { str(n) }),
      ),
      label-side: side,
      label-pos: pos,
    )
    diagram(
      spacing: (17mm, 7mm),
      wnode((0, 0), <m-e>, raw("entry_main")),
      wnode((-1.0, 0), <sm>, [$italic("Seed")(italic("main"))$], color: vb.called),
      wnode((0, 1), <m-u1>, raw("pp2")),
      wnode((0, 2), <m-k1>, raw("pp3")),
      wnode((0, 3), <m-k2>, raw("pp4")),
      wnode((0, 4), <m-p5>, raw("pp5")),
      wnode((0, 5), <m-p6>, raw("pp6")),
      wnode((0, 6), <m-x>, raw("exit_main")),
      wnode((1.6, 0), <s1>, [$italic("Seed")(c_1)$], color: vb.called),
      wnode((1.6, 1), <b1e>, [entry, $c_1$]),
      wnode((1.6, 2), <b1p>, [#raw("pp0"), $c_1$]),
      wnode((1.6, 3), <b1x>, [result, $c_1$]),
      wnode((-1.6, 1.8), <s2>, [$italic("Seed")(c_2)$], color: vb.called),
      wnode((-1.6, 2.8), <b2e>, [entry, $c_2$]),
      wnode((-1.6, 3.8), <b2p>, [#raw("pp0"), $c_2$]),
      wnode((-1.6, 4.8), <b2x>, [result, $c_2$]),
      cfg(<m-e>, <m-u1>, lab: [body(main)], side: right),
      cfg(<m-k2>, <m-p5>, lab: [check(a == 6)], side: left),
      cfg(<m-p5>, <m-p6>, lab: [check(b == 5)], side: left),
      cfg(<m-p6>, <m-x>, lab: [return], side: left),
      cfg(<s1>, <b1e>, lab: [seed read], side: right),
      cfg(<b1e>, <b1p>, lab: [body(bump)], side: right),
      cfg(<b1p>, <b1x>, lab: [return n + 1], side: right),
      cfg(<s2>, <b2e>, lab: [seed read], side: left),
      cfg(<b2e>, <b2p>, lab: [body(bump)], side: left),
      cfg(<b2p>, <b2x>, lab: [return n + 1], side: left),
      step(<m-x>, <m-p6>, "1", bend: 45deg),
      step(<m-p6>, <m-p5>, "1", bend: 45deg),
      step(<m-p5>, <m-k2>, "1", bend: 45deg),
      step(<m-k2>, <m-k1>, "1, 8", bend: -45deg, side: right, pos: 0.25),
      step(<m-k1>, <m-u1>, "1, 5", bend: -45deg, side: right),
      step(<m-u1>, <m-e>, "1", bend: -45deg, side: right),
      step(<m-e>, <sm>, "2", bend: 0deg),
      step(<m-k1>, <s1>, "4", bend: 25deg),
      step(<m-k1>, <b1x>, "3, 5", bend: -20deg, side: right),
      step(<b1x>, <b1p>, "3, 5", bend: -45deg, side: right),
      step(<b1p>, <b1e>, "3, 5", bend: -45deg, side: right),
      step(<b1e>, <s1>, "3, 5", bend: -45deg, side: right),
      step(<m-k2>, <s2>, "7", bend: -25deg, side: right),
      step(<m-k2>, <b2x>, "6, 8", bend: 40deg),
      step(<b2x>, <b2p>, "6, 8", bend: 45deg),
      step(<b2p>, <b2e>, "6, 8", bend: 45deg),
      step(<b2e>, <s2>, "6, 8", bend: 45deg),
    )
  },
  kind: image,
  placement: none,
  caption: [The solve of @tab:eq-trace drawn on the unknowns. Grey arrows are
    the edges of the graph, including a seed feeding its entry. Blue dashed
    arrows are the solver's queries and publications, labelled with the
    phases of the table. Arrows labelled with two phases are taken twice: the
    first pass through a copy of `bump` reads an empty seed, the flush (4, 7)
    fills it, and the second pass (5, 8) repeats the queries. The solve runs
    backwards from the exit of `main` and demands the copies of `bump` for
    $c_1$ (right) and $c_2$ (left) as those contexts are discovered. Recorded from an
    instrumented run],
) <fig:eq-walk>

By the soundness theorem of @sec:eq-discharge, every post-solution of this
system covers the buckets of the running example. @ch:solving proves that a terminating solve returns one.
