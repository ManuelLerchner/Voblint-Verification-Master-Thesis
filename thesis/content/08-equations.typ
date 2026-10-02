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

The goal is a solution $sol$ that over-approximates the activation collecting
semantics of @sec:contexts: for every node $v$ and context $c$,
$
  #isai("\<A>\<^bsub>\<G>,R,c₀,g,S\<^esub> v c") subset.eq conc_(M)(sol(v, c)),
$
where $conc_(M)$ is the concretization $conc_(D G)(d, g)$ of @sec:sound-core applied to
the local half $d$ of $sol(v, c)$ and the global half $g$ of the analysis
global's unknown (@sec:global-unknowns), and the empty set for unknowns
outside the solved set. The main result (#isathm("activation_collect_dg_sound"),
@sec:eq-discharge) shows that every post-solution of the equations meets this
goal, for every domain and context policy, provided the analysis is sound and
routing agrees with the concrete semantics: every callee context the concrete
semantics admits for a covered call is one the equations route that call to,
and every covered call is admitted in some context (@sec:eq-routing). Whether
a solve terminates is a separate question (@sec:termination). The running
example is the program of @fig:program-to-equations, repeated in
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
        entry-node((0, 6), text(size: 7pt, raw("exit_main"))),
        entry-node((1.7, 0.6), text(size: 7pt, raw("entry_bump"))),
        pt((1.7, 1.8), [], "pp0"),
        entry-node((1.7, 3), text(size: 7pt, raw("exit_bump"))),
        intra-edge((0, 0), (0, 1)),
        intra-edge((0, 3), (0, 4), label: [check(a == 6)], label-side: left),
        intra-edge((0, 4), (0, 5), label: [check(b == 5)], label-side: left),
        intra-edge((0, 5), (0, 6), label: [return], label-side: left),
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
    continuation reads the result node of `bump` in its own equation. The entry
    node and result node of a procedure $p$ are the nodes $ctor("FunctionEntry") thin p$ and
    $ctor("FunctionResult") thin p$, printed #raw("entry_p") and #raw("exit_p").],
) <fig:eq-running>

== Context-indexed unknowns <sec:eq-unknowns>

The intraprocedural recipe of @ch:background keeps one unknown per graph node.
Extended naively to calls, the entry of `bump` joins both call sites and holds
$n in {4, 5}$ at best, the return at $italic("pp3")$ assigns $a in {5, 6}$, and the check
`a == 6` fails although every execution satisfies it. With the update rule
that joins every contribution (@sec:td) the analyzer without contexts reports exactly this, with the verdicts of
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
    _seed((0, 0), $ctor("Activation_Seed") thin #_b space c_1$),
    _loc((0, 1), $(ctor("FunctionEntry") thin italic("bump"), c_1)$),
    _loc((0, 2), $(ctor("FunctionResult") thin italic("bump"), c_1)$),
    _loc((1.3, 0), $(italic("pp2"), c_0)$),
    _loc((1.3, 2), $(italic("pp3"), c_0)$),
    _loc((1.3, 5), $(italic("pp4"), c_0)$),
    _seed((2.6, 3), $ctor("Activation_Seed") thin #_b space c_2$),
    _loc((2.6, 4), $(ctor("FunctionEntry") thin italic("bump"), c_2)$),
    _loc((2.6, 5), $(ctor("FunctionResult") thin italic("bump"), c_2)$),
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
    different contexts $c_1 != c_2$ (`main` runs in $c_0$). Rounded purple
    nodes are seeds, the global unknowns through which a call hands its entry
    value to the callee (@sec:eq-call). A solid arrow: the
    right-hand side at its head reads the unknown at its tail. A dashed arrow:
    the right-hand side at its tail publishes to the global unknown at its head.
    Under the unit context the two copies coincide and one seed receives both
    publications. Drawn from the equation definitions.],
) <fig:eq-unknowns>

== Interprocedural equations <sec:eq-call>

For a post-solution to cover the activation collecting semantics at $(v, c)$, the right-hand side of
$(v, c)$ must join everything that can reach $v$ in context $c$
(#isaconst("routed_node_rhs")). Schematically,
$
  italic("rhs")(v, c) = italic("init")(v) union.sq
  lJoin_(u ->^a v) sh(f)_a (sol(u, c)) union.sq
  lJoin_(u in italic("calls")(v)) italic("call")_u (c) union.sq
  italic("seed")(v, c):
$
the initial abstract state $d_0$ of the analysis (@sec:sound-core) if $v$ is
the program entry, the transfer along each incoming local edge, the
contribution $italic("call")_u (c)$ of each call node $u$ whose continuation
is $v$ (the set $italic("calls")(v)$), and the seed if $v$ is a callee entry.
The names $italic("rhs")$, $italic("init")$, $italic("call")_u$ and
$italic("calls")$ are our notation for the parts of
#isaconst("routed_node_rhs"), not constants of the formalization.
A transfer that uses analysis globals also reads and publishes them
(@sec:manager).

Local edges keep the context. An activation keeps its context from entry to
return (@sec:contexts), so a local edge never changes it, and #oblig("INTRA")
follows from edge-transfer soundness before any context
policy is chosen.

Calls are where contexts change, and the callee context depends on a value.
The context policy supplies a function $ctxh$ that maps the call node $u$, the
caller context $c$ and the abstract entry value $e$ to the callee context
$c' = ctxh(u, c, e)$. Since $e$ is computed from the caller's value, the
equations cannot wire callers to callee entries in advance, and the entry
unknown $(ctor("FunctionEntry") thin p, c')$ cannot list its contributors:
which call sites route to $c'$ is known only once their callers are solved.
Side-effecting systems reverse the direction: each caller contributes to the
callee's entry while it evaluates its own equation (@ch:background). Voblint
adds one global unknown per callee entry and context, the _seed_
$ctor("Activation_Seed") thin p space c'$ (a #isatype("global_unknown"), keyed
by the callee's entry node, which we name by its procedure $p$), which
receives these contributions
(@sec:eq-seed-global explains why they do not target the entry directly). Every call routed to $(p, c')$ publishes its entry
value to the seed, and the entry reads the seed back, so the seed collects
every entry value routed to $(p, c')$.

A call follows the protocol of @sec:calls (@fig:eq-protocol). Its contribution
reads the caller's value at $(u, c)$ and applies enter, which
yields a list of entry pairs, each a resume value $q$ and an entry value $e$.
Each pair is routed separately, so we follow one. The call computes
$c' = ctxh(u, c, e)$, publishes $e$ to $ctor("Activation_Seed") thin p space c'$, reads the
callee's result $r$ directly from the unknown of its result node
$(ctor("FunctionResult") thin p, c')$ in the context it just computed, and
returns the combined value to $(k, c)$. The caller treats the callee as a
black box: its equation touches only the callee's seed and result, never the
body. The body's unknowns have their own equations, and the solver evaluates
them when the caller first reads the result. Since a call never enters the
callee's body, recursion needs no special case. In @fig:eq-unknowns the
continuation $(italic("pp3"), c_0)$ reads $(italic("pp2"), c_0)$, computes
$c_1$ from the entry value $n = 5$, publishes that value to the seed of `bump`
in $c_1$, and reads $(ctor("FunctionResult") thin italic("bump"), c_1)$.

When the entry value is bottom, no store enters the callee. The call then
publishes nothing, reads no result, and combines $q$ with a bottom callee
result. Apinis et al. use a similar test so that procedures which are not
called are not analyzed, but their call constraint then contributes bottom
without combining @apinis12[§7]. Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L244",
)[call handling]
applies the test as Voblint does. It needs one assumption of the routed
locale: a value the test classifies as bottom concretizes to the empty set.

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
    _seed((1.2, 2), $ctor("Activation_Seed") thin #_p space c'$),
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
    continuation $(k, c)$. Enter turns the caller value into a
    resume value $q$ and an entry value $e$, and $e$ selects the callee context
    $c'$. The call publishes $e$ to the seed of $(#_p, c')$ (dashed) and reads
    the callee's result $r$ at $c'$. All steps except the callee body belong to
    the right-hand side of $(k, c)$. The callee's unknowns have their own
    equations.],
) <fig:eq-protocol>

== Relating routing to concrete activations <sec:eq-routing>

The equations route each call to a callee context. Soundness requires this
routing to agree with the contexts the collecting semantics uses.

The concrete side is the relation $R$ of @sec:contexts. It is the context
policy's rule for concrete calls: given the call site $u$, the caller's
context $c$, the caller's store $s$ and the entered store $s'$, it says which
callee contexts $c'$ the new activation gets. We write "$R$ admits $c'$" when
$R(u, c, s, s', c')$ holds. The Isabelle relation also receives the call's
static description (#isatype("call_info")), which we leave implicit. The trace semantics applies $R$ at every call, and
the activation collecting semantics files the stores of the activation under
each admitted $c'$. Under
call strings of length one, for instance, $R$ admits exactly $[italic("pp2")]$ for the
call `bump(5)` from `main`. The analyzer never sees $s'$. It computes an abstract entry value $e$,
chooses a context from $e$, and publishes $e$ to the callee's seed for that
context. The two must meet:
$
  R "admits" c' quad ==> quad e "is routed to" c'.
$
With the soundness of enter, every concrete entered store filed under $c'$ is
then covered by the value published for $c'$. Two properties
make this precise.

- _Totality_ (#isathm("routed_context.routed_entry_total", thy: "Routed_Context", display: "routed_entry_total")):
  $R$ admits at least one context for every concrete call from a
  store that the caller's solved value covers, so no such activation is
  missing from the context-indexed collecting semantics.
- _Adequacy_ (#isathm("routed_context.routed_entry_cover", thy: "Routed_Context", display: "routed_entry_cover")):
  whenever $R$ admits $c'$ for a concrete call from a store that
  the caller's value covers, the caller's entry pair $(q, e)$ covers that store
  and the entered one (@sec:calls), $e$ routes to $c'$, and the entry unknown
  at $c'$ is among the solved unknowns.

Both are assumptions of the routed soundness theorem (@sec:eq-discharge),
proved once for each context policy. Adequacy gives #oblig("CALL") and
#oblig("RETURN"), since the call's continuation reads the callee's result at
the same $c'$, and totality gives #oblig("TOTAL") of @sec:contract.

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

Recall from @sec:calls that enter turns the caller's value into entry pairs
$(q, e)$: a resume value $q$ and an entry value $e$, an abstract state of
the callee. The entry-state policy takes as context the abstract values that
$e$ gives the callee's formal parameters, written $e|_"formals"$. For
`bump(n)` with $e = {n |-> [4, 5]}$, the context is $e|_"formals" = [[4, 5]]$,
a list with one entry per formal. Which context a call gets therefore depends
on the entry value computed from the caller's solved value.

This value cannot be reconstructed from one concrete call. Suppose the
caller's solved value maps $x$ to $[4, 5]$ and the program calls `bump(x)`.
Enter produces $e = {n |-> [4, 5]}$, and the equations route the call to the
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

So $R$ depends on the solved analysis, as @sec:contexts anticipated, and so does
the activation collecting semantics. This is not circular: the proof first fixes a post-solution
$sol$, then defines $R$ from $sol$, and finally proves that $sol(v, c)$ covers
the activation collecting semantics this $R$ induces.

The dependence is necessary for entry-state contexts. Taking the context
directly from the concrete entered store gives $[[4, 4]]$ in the example,
although the equations published only to $[[4, 5]]$. Admitting every context
whose concretization contains the entered store does not help: it also admits
$[[4, 4]]$ and $[[top]]$. Adequacy would then demand coverage at unknowns the
equations never fill.

The dependence disappears in the source-level result, which uses only the
union over all contexts of the activation collecting semantics at a node. By totality this union is the context-free
collecting semantics (@sec:consequences), whatever the split into contexts.

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
  caption: [Procedure copies under four context policies. The running example
    has no nested call, so this figure uses a small program of the explainer:
    `scale(v)` returns `2 * v`, `wrap(w)`
    returns `scale(w)` from #_site("scale(w)"), and `main` calls `a = wrap(1)`
    at #_site("wrap(1)") and `b = wrap(4)` at #_site("wrap(4)"), then checks
    `a == 2`. Boxes are procedure copies labelled with their contexts as the
    analyzer prints them (`root` is the initial context of `main`), arrows
    calls labelled with their sites. Read from
    the analyzer's solved graph (Interval, claims #claim-ref("ctx-demo-*")).],
) <fig:eq-policies>

== Soundness of the generated system <sec:eq-discharge>

The construction is designed so that every post-solution covers the
context-indexed collecting semantics. The theorem is independent of the
abstract domain and of the context policy: it uses only the analysis
soundness contract and the routing properties of @sec:eq-routing.

#theorem(name: [Routed collecting soundness], isa: "activation_collect_dg_sound")[
  Let $sol$ be a post-solution of the generated equations. Suppose the solved
  set contains the program entry in the initial context and is closed under
  local edges out of unknowns whose value describes some store and under call
  continuations, the initial abstract state covers the
  initial stores, the analysis satisfies #isalocale("analysis_contract"), the
  callee list at each call site contains every callee a covered call can
  enter, and routing is adequate and total. Then for every node $v$ and
  context $c$,
  $
    #isai("\<A>\<^bsub>\<G>,R,c₀,g,S\<^esub> v c") subset.eq conc_(M)(sol(v, c)).
  $
]

The solved value at $(v, c)$ thus covers every concrete store that reaches $v$
in context $c$. In particular, no concrete activation reaches an unknown
outside the solved set. @tab:eq-obligations shows how
the proof meets each obligation of @ch:traces.

The proof reads the obligations off the equations. A post-solution satisfies
$italic("rhs")(v, c) lle sol(v, c)$ at every solved unknown and bounds every
publication. Unfolding the right-hand side of @sec:eq-call gives one inequality
per term. Write $v_0$ for the program entry and $c_0$ for the initial context. For a
local edge $u ->^a v$, and for a call at $u$ in context $c$ to $p$ with entry
pair $(q, e) = enterh (sol(u, c))$, routed context
$c' = ctxh(u, c, e)$ and continuation $k$, a post-solution satisfies
#[
  #show math.equation: set block(breakable: true)
  $
    sol(v_0, c_0) & gt.eq d_0 & wide #ineq-tag(1) \
    sol(v, c) & gt.eq sh(f)_a (sol(u, c)) & wide #ineq-tag(2) \
    sol(ctor("Activation_Seed") thin p space c') & gt.eq e & wide #ineq-tag(3) \
    sol(ctor("FunctionEntry") thin p, c') & gt.eq sol(ctor("Activation_Seed") thin p space c') & wide #ineq-tag(4) \
    sol(k, c) & gt.eq sh("combine") (q, sol(ctor("FunctionResult") thin p, c')) & wide #ineq-tag(5) \
    forall s in conc_(M)(sol(u, c)). & med exists c'. med R(u, c, s, s', c') & wide #ineq-tag(6)
  $
]
Line #ineq(6) is not an inequality of the system but the totality premise of
@sec:eq-routing, where $s'$ is the store the call enters from $s$.
Lines #ineq(3) and #ineq(4) are #isathm("routed_seed_publish_bound_seed") and
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
    [#oblig("INIT")], [#ineq(1)], [$d_0$ covers the initial stores],
    [#oblig("INTRA")], [#ineq(2)], [the edge transfer is sound (the contract's #oblig("INTRA"))],
    [#oblig("CALL")],
    [#ineq(3), #ineq(4)],
    [$e$ covers the entered store, and $R$ admits $c'$ (adequacy)],
    [#oblig("RETURN")],
    [#ineq(5)],
    [the combine stages are sound (the contract's #oblig("RETURN")), and $R$ admits $c'$ (adequacy)],
    [#oblig("TOTAL")], [#ineq(6)], [none beyond the premise itself],
    table.hline(),
  ),
  placement: none,
  caption: [How #isathm("activation_collect_dg_sound") discharges the five
    obligations of @ch:traces: the inequality of the displayed system each
    one uses, and the soundness fact that turns it into coverage. Here
    $sh("combine")$ stands for the two combine stages of
    @sec:calls.],
) <tab:eq-obligations>

In Isabelle the lemma is proved inside the locale
#isalocale("routed_context"), which carries the analysis and
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

Line #ineq(4) of @sec:eq-discharge lets the callee's entry take in the entry value
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

One right-hand side can publish to the same seed twice. The generator already
folds the node's own publications to the analysis global into one, but two
call edges that resume at the same node are separate contributions, and when
both are routed to the same callee context they write the same seed
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

== The running example, solved <sec:eq-example>

We close with the running example of @fig:eq-running under entry-state
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
// A value as the trace prints it: bottom, a routed entry value e_i, or the
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
system covers the activation collecting semantics of the running example. @ch:solving proves that a terminating solve returns one.
