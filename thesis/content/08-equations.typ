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

@ch:traces reduced soundness to five local obligations on a claim
#isai("cover v c"), and the analyses part showed what one analysis or a
combination of analyses supplies and proves. None of it mentioned contexts or
equations. For a program without procedures, one abstract state per graph node
suffices. Procedures break this, because the same node is reached by different
activations and merging them loses facts. Voblint therefore keeps one unknown
per node and _context_. A call chooses the callee's context, possibly from its abstract entry state,
which is known only once the caller is solved. We call this choice
_routing_. It must agree with the context policy of @sec:contexts, which
assigns contexts to concrete activations.

This chapter builds the equations over these unknowns and shows that solving
them is sound. The goal is a solution $sol$ that over-approximates the
activation collecting semantics of @sec:contexts at every node $v$ and context
$c$:
$
  #isai("\<A>\<^bsub>\<G>,adm,c₀,g,S\<^esub> v c") subset.eq conc_(M)(sol(v, c)),
$
where $conc_(M)$ is the concretization of the analysis (@sec:sound-core). The
main result (#isathm("activation_collect_dg_sound"), @sec:eq-discharge) shows
that every post-solution of the equations meets this goal, for every domain
and context policy, provided the analysis is sound and routing agrees with the
concrete semantics. The running example is the program of
@fig:program-to-equations, repeated in @fig:eq-running.

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
that joins every contribution (@sec:update-rules), the analyzer without
contexts reports exactly this, in the verdicts of @fig:intro-answers:
#_cli("pg-contexts-none-join", "a == 6", 3) with
#_cli("pg-contexts-none-join", "a == 6", 4). The concrete semantics does not
merge the two calls. Each activation of `bump` is a trace of its own, and the
activation collecting semantics of @sec:contexts files it under the contexts
its policy admits. Voblint indexes the unknowns by the same contexts.

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
    _loc((0, 1), $(ctor("FunctionEntry") thin italic("bump"), c_1)$),
    _loc((0, 2), $(ctor("FunctionResult") thin italic("bump"), c_1)$),
    _loc((1.3, 0), $(italic("pp2"), c_0)$),
    _loc((1.3, 2), $(italic("pp3"), c_0)$),
    _loc((1.3, 4), $(italic("pp4"), c_0)$),
    _loc((2.6, 3), $(ctor("FunctionEntry") thin italic("bump"), c_2)$),
    _loc((2.6, 4), $(ctor("FunctionResult") thin italic("bump"), c_2)$),
    _read((1.3, 0), (1.3, 2), [caller]),
    _read((1.3, 2), (1.3, 4), [caller], side: right),
    _read((0, 1), (0, 2), [local], side: right),
    _read((0, 2), (1.3, 2), [result], side: right),
    _read((2.6, 3), (2.6, 4), [local]),
    _read((2.6, 4), (1.3, 4), [result]),
    _pub((1.3, 2), (0, 1), $n = 5$, side: right),
    _pub((1.3, 4), (2.6, 3), $n = 4$),
  )),
  caption: [Unknowns around the calls of the running example when the two
    calls reach different contexts $c_1 != c_2$ (`main` runs in $c_0$). A solid
    arrow means that the right-hand side at its head reads the unknown at its
    tail. A dashed arrow means that the call whose continuation is at its tail
    contributes its entry state to the callee entry at its head, through the
    seed of @sec:eq-call, which is not drawn. Under the unit context the two
    copies of `bump` coincide. Drawn from the equation definitions.],
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
is $v$ (the set $italic("calls")(v)$), and, if $v$ is a procedure entry, the
value of its seed, which this section defines below. The names
$italic("rhs")$, $italic("init")$, $italic("call")_u$, $italic("calls")$ and
$italic("seed")$ are our notation for the parts of
#isaconst("routed_node_rhs"), not constants of the formalization.
A transfer that uses analysis globals also reads and publishes them
(@sec:shared-facts).

Local edges keep the context. An activation keeps its context from entry to
return (@sec:contexts), so a local edge never changes it, and #oblig("INTRA")
follows from edge-transfer soundness before any context
policy is chosen.

Calls are where contexts change, and the callee context depends on a value.
The analyzer routes a call with a function $ctxh$ that maps the call node $u$,
the caller context $c$ and the abstract entry state $e$ to the callee context
$c' = ctxh(u, c, e)$. Each context policy comes with such a function, and
@sec:eq-routing states how the two must agree. Since $e$ is computed from the
caller's value, the equations cannot wire callers to callee entries in
advance. The entry unknown $(ctor("FunctionEntry") thin p, c')$ therefore
cannot list its contributors, because which call sites route to $c'$ is known
only once their callers are solved. Side-effecting systems reverse the
direction. Each call contributes its entry state to the callee's entry while
its own equation is evaluated (@sec:side-effects). In Voblint's equations this contribution passes through one
more unknown per callee entry and context, the _seed_
$ctor("Activation_Seed") thin p space c'$ (a #isatype("global_unknown") keyed by
the callee's entry node, which we name by its procedure $p$). Every call routed
to $(p, c')$ publishes its entry state to the seed, and the entry reads the
seed, so the seed collects every entry state routed to $(p, c')$. The seed is
the entry's inbox, and @sec:eq-seed-global explains why the equations need it
instead of contributing to the entry directly.

A call follows the protocol of @sec:calls (@fig:eq-protocol). Its contribution
reads the caller's value at $(u, c)$ and joins one part for each procedure
$p$ the call may enter. For VIMP's direct calls this is the callee named by
the call edge, which the analyzer reads off the graph. For each callee the
contribution applies enter, which yields a list of entry pairs, each a resume
state $q$ and an entry state $e$, an abstract state of the callee. Each pair
is routed separately, so we follow one. The call computes
$c' = ctxh(u, c, e)$, publishes $e$ to $ctor("Activation_Seed") thin p space c'$, reads the
callee's result $r$ directly from the unknown of its result node
$(ctor("FunctionResult") thin p, c')$ in the context it just computed, and
returns the combined value to $(k, c)$. The caller treats the callee as a
black box. Its equation touches only the callee's seed and result, never the
body. The body's unknowns have their own equations, and the solver evaluates
them when the caller first reads the result. Since a call never enters the
callee's body, recursion needs no special case. In @fig:eq-unknowns the
continuation $(italic("pp3"), c_0)$ reads $(italic("pp2"), c_0)$, computes
$c_1$ from the entry state $n = [5, 5]$, publishes that value to the seed of
`bump` in $c_1$, and reads $(ctor("FunctionResult") thin italic("bump"), c_1)$.

When the entry state is bottom, no store enters the callee. The call then
publishes nothing, reads no result, and combines $q$ with a bottom callee
result, as Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L244-L245",
)[call handling]
does. Soundness then needs one assumption about the test, that a value it
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
    resume state $q$ and an entry state $e$, and $e$ selects the callee context
    $c'$. The call publishes $e$ to the seed of $(#_p, c')$ (dashed) and reads
    the callee's result $r$ at $c'$. All steps except the callee body belong to
    the right-hand side of $(k, c)$. The callee's unknowns have their own
    equations.],
) <fig:eq-protocol>

== Routing and context policies <sec:eq-routing>

The equations route each call to a callee context. Soundness requires this
routing to agree with the contexts the collecting semantics uses.

The concrete side is the context policy $italic("adm")$ of @sec:contexts.
Given the call site $u$, the caller's context $c$, the caller's store $s$ and
the entered store $s'$, it returns the set of callee contexts that the new
activation may get. We write "$italic("adm")$ admits $c'$" when
$c' in italic("adm")(u, c, s, s')$. The Isabelle policy also receives the call's
static description (#isatype("call_info")), which we leave implicit. The trace semantics applies $italic("adm")$ at every call, and
the activation collecting semantics files the stores of the activation under
each admitted $c'$. Under
call strings of length one, for instance, $italic("adm")$ admits exactly $[italic("pp2")]$ for the
call `bump(5)` from `main`. The analyzer never sees $s'$. It computes an abstract entry state $e$,
chooses a context from $e$, and publishes $e$ to the callee's seed for that
context. The two must meet:
$
  italic("adm") "admits" c' quad ==> quad e "is routed to" c'.
$
With the soundness of enter, every concrete entered store filed under $c'$ is
then covered by the value published for $c'$. Two properties
make this precise.

- _Totality_ (#isathm("routed_context.routed_entry_total", thy: "Routed_Context", display: "routed_entry_total")):
  $italic("adm")$ admits at least one context for every concrete call from a
  store that the caller's solved value covers, so no such activation is
  missing from the context-indexed collecting semantics.
- _Adequacy_ (#isathm("routed_context.routed_entry_cover", thy: "Routed_Context", display: "routed_entry_cover")):
  whenever $italic("adm")$ admits $c'$ for a concrete call from a store that
  the caller's value covers, some entry pair $(q, e)$ of the caller's value
  covers that store and the entered one (@sec:calls), $e$ routes to $c'$, and
  the entry unknown at $c'$ is among the solved unknowns.

Both are assumptions of the routed soundness theorem (@sec:eq-discharge),
proved once for each context policy. #oblig("CALL") and #oblig("RETURN") need adequacy, since the call publishes its
entry state and its continuation reads the callee's result at the same $c'$.
Totality gives #oblig("TOTAL") of @sec:contract.

#figure(
  {
    table(
      columns: (auto, auto, auto, auto),
      align: (left, left, left, left),
      inset: (x: 5pt, y: 4pt),
      stroke: none,
      table.hline(),
      [*policy*], [*$italic("adm")$ admits $c'$ iff*], [*routed to*], [*why equal*],
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
  caption: [For a call at site $u$ from caller context $c$ with caller store
    $s$ and entered store $s'$: the contexts $italic("adm")$ admits, where the equations
    route the entry state $e$, and why the two agree. $u dot c$ prepends the
    site, $e|_"formals"$ lists the formals' values in $e$, and an entry pair
    $(q, e)$ of the caller's solved value covers $(s, s')$ when
    $s in conc(q)$ and $s' in conc(e)$. Unit and call strings are
    _functional_ policies, since their context ignores abstract states.],
) <tab:eq-policies>

For unit and call strings the correspondence is direct, as the last column
shows. $italic("adm")$ admits exactly the context the analyzer's own context function
computes for the concrete call (#isaconst("context_policy_of_fun")), so
totality is immediate. The rest of adequacy is the entry coverage of
@sec:calls and the routed entry unknown being solved.

Unit and call-string contexts are determined by the call site and the caller
context, so the concrete call alone fixes its context. An entry-state
context, in contrast, is part of the abstract analysis result. The
entry-state policy takes as context the abstract values that the entry state
$e$ of an entry pair $(q, e)$ gives the callee's formal parameters, written
$e|_"formals"$. For
`bump(n)` with $e = {n |-> [4, 5]}$, the context is $e|_"formals" = [[4, 5]]$,
a list with one entry per formal. Which context a call gets therefore depends
on the entry state computed from the caller's solved value.

This value cannot be reconstructed from one concrete call. Suppose the
caller's solved value maps $x$ to $[4, 5]$ and the program calls `bump(x)`.
Enter produces $e = {n |-> [4, 5]}$, and the equations route the call to the
context $[[4, 5]]$. One concrete execution described by this call has $x = 4$
and enters `bump` with $n = 4$:
$
  underbrace(s' = {n |-> 4}, "one concrete entered store")
  quad in quad
  underbrace(conc(e) "with" e = {n |-> [4, 5]}, "the abstract entry state")
  quad --> quad
  underbrace(c' = [[4, 5]], "the context it is routed to").
$
Abstracting this single store on its own would give $[[4, 4]]$. The equations
never publish to that context, so an activation filed there would land in an
unknown nothing fills. Entry-state contexts therefore cannot be defined by
abstracting each concrete entered store independently.

Instead, the concrete call is assigned the context of the abstract entry state
that covers it. For a call from caller store $s$ with entered store $s'$, the
relation #isaconst("routed_entry_context_rel") admits $c'$ when some entry pair
$(q, e)$ computed from the caller's solved value satisfies
$
  s in conc(q), quad s' in conc(e), quad c' = e|_"formals".
$
In the example the execution with $n = 4$ is assigned $[[4, 5]]$, because the
entry value $e = {n |-> [4, 5]}$ covers $n = 4$ and $[[4, 5]]$ is where the
equations published $e$.

Adequacy is then immediate. Whenever $italic("adm")$ admits a context $c'$, it
does so through a covering entry state that the equations route to exactly
$c'$. Totality follows from entry coverage (@sec:calls), since every concrete
call covered by the caller's value has a covering entry pair and therefore an
admitted context.

So $italic("adm")$ depends on the solved analysis, as @sec:contexts
anticipated, and so does the activation collecting semantics. The argument is
not circular. The proof first fixes a post-solution $sol$, then defines
$italic("adm")$ from $sol$, and finally proves that $sol(v, c)$ covers the
activation collecting semantics this $italic("adm")$ induces.

The dependence is necessary. Admitting every context whose concretization
contains the entered store would also admit $[[4, 4]]$ and $[[top]]$, and
adequacy would then demand coverage at unknowns the equations never fill.

The dependence disappears in the source-level result, which uses only the
union over all contexts of the activation collecting semantics at a node. By
totality this union is the node collecting semantics, whatever the split into
contexts (#isathm("node_collect_eq_Union_activation_collect"), @sec:contract).

The policy affects only precision, because it decides which calls share an
unknown. @sec:eval-precision compares the policies on one program.

== Soundness of the generated system <sec:eq-discharge>

The construction is designed so that every post-solution covers the
context-indexed collecting semantics. The theorem holds for every abstract
domain and context policy, because it uses only the analysis contract and the
routing properties of @sec:eq-routing.

#theorem(name: [Routed collecting soundness], isa: "activation_collect_dg_sound")[
  Let $sol$ be a post-solution of the generated equations on a set of local
  unknowns, the _solved set_. Suppose the solved set contains the program
  entry in the initial context and is closed under local edges out of unknowns
  whose value describes some store and under call continuations. Suppose
  further that the initial abstract state covers the initial stores in an
  environment of analysis globals below the solved one, the analysis satisfies
  #isalocale("analysis_contract"), the bottom test is sound, every callee a
  covered call can enter is among the callees its call site joins, and routing
  is adequate and total. Then for every node $v$ and context $c$,
  $
    #isai("\<A>\<^bsub>\<G>,adm,c₀,g,S\<^esub> v c") subset.eq conc_(M)(sol(v, c)).
  $
]

Here $conc_(M)$ applies the concretization $conc_(D G)(d, e)$ of
@sec:sound-core to the local half $d$ of $sol(v, c)$ and to the environment
$e$ that reads each analysis global off its unknown in $sol$, and it gives the
empty set outside the solved set. The solved value at $(v, c)$ thus covers
every concrete store that reaches $v$ in context $c$. In particular, no concrete activation reaches an unknown
outside the solved set. @tab:eq-obligations shows how
the proof meets each obligation of @ch:traces.

The proof reads the obligations off the equations. A post-solution satisfies
$italic("rhs")(v, c) lle sol(v, c)$ at every solved unknown and bounds every
publication of these right-hand sides. Unfolding the right-hand side of @sec:eq-call gives one inequality
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
    forall s in conc_(M)(sol(u, c)). & med italic("adm")(u, c, s, s') != emptyset & wide #ineq-tag(6)
  $
]
Line #ineq(6) is not an inequality of the system but the totality premise of
@sec:eq-routing, where $s'$ is the store the call enters from $s$.
Lines #ineq(3) and #ineq(4) are #isathm("routed_seed_publish_bound_seed") and
#isathm("routed_seed_read_bound"). Each obligation follows from its lines in
the same way. The line holds and the operation on its right is sound, so the
concrete step lands in the concretization of its left side.

#figure(
  table(
    columns: (auto, auto, 1fr),
    align: (left, left, left),
    stroke: none,
    table.hline(),
    [*obligation*], [*uses*], [*and the soundness fact*],
    table.hline(stroke: 0.5pt),
    [#oblig("INIT")], [#ineq(1)], [$d_0$ covers the initial stores],
    [#oblig("INTRA")],
    [#ineq(2)],
    [the edge transfer is sound (the analysis contract's #oblig("INTRA"))],
    [#oblig("CALL")],
    [#ineq(3), #ineq(4)],
    [$e$ covers the entered store, and $italic("adm")$ admits $c'$ (adequacy)],
    [#oblig("RETURN")],
    [#ineq(5)],
    [the combine stages are sound (the analysis contract's #oblig("RETURN")), and $italic("adm")$ admits $c'$ (adequacy)],
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
routing assumptions. The lemma itself adds only the program entry, the
initial stores, and that the initial environment of analysis globals lies
below the solved one:
#proved("activation_collect_dg_sound")
Of the locale's remaining premises, the soundness of the bottom test concerns
the analysis. The others, finitely many call edges, at most one call per call
node and seed keys distinct from all other keys, are structural and hold for
every compiled program. The analyzer reaches the theorem through
#isathm("dg_spec_of_contract") and, per policy,
#isathm("fun_route_activation_collect_sound") and
#isathm("entry_state_activation_collect_sound").

In the running example, the entry-state policy routes `bump(5)` to
$c_1 = [[5, 5]]$ and `bump(4)` to $c_2 = [[4, 4]]$. The two copies of `bump`
keep their results apart, which is why the analyzer proves both checks
(@sec:eq-unknowns). By the theorem above, the solved states at the checks
cover every store that reaches them in these contexts. @ch:solving shows how the equations are solved and why a terminating
solve returns a post-solution.
