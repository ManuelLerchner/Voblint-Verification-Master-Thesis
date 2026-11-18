#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "@preview/cetz:0.5.2"
#import "../lib/code.typ": fixture, isaconst, isai, isalocale, isathm, isatype, listing, thy-badge
#import "../lib/sources.typ": thy, update-rule-steps
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/claims.typ": claim-check, claim-ref, claim-snapshot, claim-text
#import "../lib/figures.typ": verdict
#import "../lib/theorems.typ": theorem

#let _b = $italic("bump")$

= Post-Solutions from the Verified Solver <ch:solving>

@ch:equations showed that a post-solution of the generated equations is
sound. At every node and context, its abstract state describes every store that
an execution reaches there in that context
(#isathm("activation_collect_dg_sound")). The TD solver, however, is
local (@sec:side-effects). It starts from a query and solves only the unknowns
that the query transitively reads, its solved set (@sec:td). On this set its valuation
satisfies the inequalities, and about all other unknowns it says nothing. An
execution that reached an unknown outside the solved set would have no
abstract state describing its store. The theorem therefore requires the solved
set to contain the program entry and every unknown that an execution can reach
from it. This chapter shows that every solve that terminates provides such a
solved set and post-solution.

== Solver encoding of the equations <sec:eq-encoding>

Voblint reuses the verified TD solver of @sec:td unchanged, through a copy of
its theories in the repository, the _vendored_ solver. This solver accepts a
right-hand side only as a strategy tree, uses one
value type for all unknowns, and allows side effects only to global unknowns. A
direct encoding of the equations, as in Apinis et al. @apinis12 and Goblint,
needs features this interface lacks. Voblint closes each gap with an
adapter on the equations and leaves the solver and its proof as they are
(@tab:eq-adapters). @ch:equations already stated the equations in the adapted
form; buffering (@sec:update-rules) is applied after a right-hand side is built.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    stroke: none,
    table.hline(),
    [*the equations need*], [*the solver provides*], [*adapter*],
    table.hline(stroke: 0.5pt),
    [value-dependent reads], [strategy trees], [strategy tree (@sec:eq-trees)],
    [publish to local unknowns], [publish to globals only], [seed (@sec:eq-seed-global)],
    [two value types], [one value type], [product (@sec:global-unknowns)],
    [publish twice to one target],
    [updates that may not stabilize],
    [buffering (@sec:update-rules)],
    table.hline(),
  ),
  placement: none,
  caption: [Requirements of the equations of Apinis et al. and Goblint, the
    corresponding feature of the vendored TD solver, and the adapter that closes
    each gap.],
) <tab:eq-adapters>

=== Value-dependent reads as strategy trees #thy-badge("Voblint_Framework", "Routed_Call_Programs") <sec:eq-trees>

A local edge always reads the same unknown, its predecessor. A call, in
contrast, chooses what to read from values it has already read. In the running
example (@fig:eq-unknowns), the continuation $(italic("pp3"), c_0)$ first
reads the caller $(italic("pp2"), c_0)$. From that value, it computes the entry
state, which binds $n$ to $absval(ivl(5, 5))$. This state determines the context
$c_1$ and thus the result it reads next,
$(ctor("FunctionResult") thin italic("bump"), c_1)$.
The strategy trees of @sec:td express these value-dependent reads through
continuations. Consider a call at $u$ in context $c$ with a single callee $p$
whose enter function returns a single entry pair. Writing $d$ for the caller's
state at $u$, the enter function yields the entry pair $(q, e) = enterh(d)$ and
the context policy yields the callee context $c' = ctxh(u, c, e)$. The call's
right-hand side (#isaconst("rhs_call")) is then the tree
$
  t_"call" = #ctor("QueryL") ( & (u, c), lambda d. \
                               & #ctor("Side") ( ctor("Activation_Seed") thin p space c', e, \
                               & quad #ctor("QueryL") ( (ctor("FunctionResult") thin p, c'), lambda r.
                                   #ctor("Answer", thy: "Basics_side") (sh("combine") (q, r)) ) ) ).
$
The tree performs the steps of @fig:eq-unknowns in order. The general tree
(#isaconst("routed_call_program")) runs them for every callee and entry pair
and joins the answers.

=== Entry states as global seeds <sec:eq-seed-global>

In $t_"call"$, the #ctor("Side") step publishes the entry state to the seed of
the callee in $c'$, the global unknown that the callee's entry reads
(@sec:eq-call). Apinis et al. push the entry state directly into the callee's
entry $(ctor("FunctionEntry") thin p, c')$ @apinis12[§6], and Goblint does the
same with its local side effect `sidel`
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L244")[`constraints.ml`]).
That entry, however, is a local unknown, and the vendored TD solver's
#ctor("Side") accepts only global unknowns. Rather than change the solver and redo its
proof, Voblint adds the seed as an intermediate global unknown.

Compared with a side effect into the local entry, a seed can lose precision.
As global unknowns, seeds are merged by the update rule for globals
(@sec:td), which may widen an entry state even when no loop or
recursion is involved. Without contexts, both calls of the running example
publish to the one seed of `bump`, and warrowing widens it. The analyzer then
reports #verdict(claim-check("pg-contexts-none", "a == 6").at(3)) for `a == 6` with
#absval(raw(claim-check("pg-contexts-none", "a == 6").at(4))), whose lower bound $-infinity$ comes
from this widening.

=== Local and global values in one product #thy-badge("Voblint_Framework", "DG_State") <sec:global-unknowns>

A local unknown holds an abstract state of the analysis's local domain, and an
analysis global holds a value of its global domain (@sec:shared-facts). The
vendored TD solver, however, has a single value type $'d$ for all unknowns, so Voblint
uses the product type of both domains as that value type. Every unknown holds a pair #isatype("dg_state") of
a local and a global half, #isaconst("dg_local") and #isaconst("dg_global"),
uses one half and leaves the other at $lbot$ (@tab:eq-carrier). Order and join
on pairs work componentwise, so the solver's requirements on the value type
follow from those on the two halves. The half an unknown uses depends on what
it stores. A seed, for example, is a global unknown, because calls publish to
it, but it stores an entry state and therefore uses the local half.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    stroke: none,
    table.hline(),
    [*unknown*], [*holds*], [*value*],
    table.hline(stroke: 0.5pt),
    [local unknown $(v, c)$], [abstract state $d$ at node $v$ in context $c$], [$(d, lbot)$],
    [seed #isaconst("Activation_Seed") $p$ $c'$],
    [entry state $e$ published to $p$ in context $c'$],
    [$(e, lbot)$],
    [#isaconst("Analysis_Global") $x$], [value $g$ of the analysis global $x$], [$(lbot, g)$],
    table.hline(),
  ),
  placement: auto,
  caption: [Which half of the pair #isatype("dg_state") each kind of unknown
    uses. The other half stays $lbot$. Seeds and analysis globals are the global
    unknowns, named by #isatype("global_unknown").],
) <tab:eq-carrier>

== Update rules for global unknowns #thy-badge("TD", "Update_rules") <sec:update-rules>

A global unknown, such as a seed, receives contributions from several places.
Its update rule (@sec:td) merges each new contribution into the value the
unknown holds and thereby decides both precision and termination. Tilscher et
al. state the solver's requirements on an update rule as the locale
#isalocale("update_rule") and prove that five rules satisfy it @tilscher26,
so the analyzer offers all five as a setting
(#isathm("update_rule_update_global_of")). @fig:update-rules compares them.

The rules differ in what they keep per origin, the right-hand side that
published a contribution (@sec:td), and in whether they widen. Of the two
_joining rules_, _join_ joins every contribution into the value, and _join per
origin_ joins each origin's latest contribution. Of the three _warrowing rules_,
_warrow_ and _warrow per origin_ warrow toward the same join or per origin, and
_bounded narrowing_ also limits how often an origin may switch from widening to
narrowing. In #isaconst("run_voblint"), the rule governs how a callee's entry
state and a flow-insensitive program global (@sec:mixed-flow) accumulate their
contributions. No rule is more precise on every program (@sec:eval-precision).

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
        text(fill: vb.unstable, weight: "bold", [#absval(raw(v))#super[$nabla$]])
      } else { absval(raw(v)) }
    }
    let r(v) = absval(raw(v))
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
      [*rule*, vendored update], [*1:* A publishes #r("[0,3]")], [*2:* B publishes #r("[4,4]")],
      [*3:* A publishes #r("[1,1]")], [*4:* A publishes #r("[0,8]")],
      table.hline(stroke: 0.4pt),
      ..names.zip(_rule-steps).map(((n, row)) => (n, ..row.map(cell))).flatten(),
      table.hline(stroke: 0.5pt),
    )
  },
  kind: table,
  placement: none,
  caption: [One global unknown under each update rule, from #absval(raw("⊥")), after
    four interval contributions from origins A and B, which separate the rules
    and come from no program. Widened bounds are bold and marked $nabla$. The
    cells are computed by #isathm("update_rules_example") from the vendored
    rules.],
) <fig:update-rules>

One right-hand side can publish to the same global unknown twice, for example,
when two calls that resume at the same node are routed to the same callee
context and publish to the same seed. The equations read two publications to one target
$g$ as one bound:
$
  #ctor("Side") (g, a); #ctor("Side") (g, b)
  quad "means" quad
  sol(g) lge a ljoin b.
$
The vendored TD solver, however, applies the update rule at every #ctor("Side").
A per-origin rule (@sec:td) therefore records first $a$ and then
$a union.sq b$, so in every re-evaluation the recorded contribution shrinks
and grows back. Under warrowing, the shrinking step narrows, the growing step
widens again, and the solver may not stabilize. The update rules of Stemmler
et al. assume one joined contribution per target and evaluation
@stemmler25[§3], and Goblint, when `narrow-globs` is enabled, joins the side
effects of an evaluation before its per-origin update
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/solver/td3UpdateRule.ml#L113-L228")[`td3UpdateRule.ml`]).

Voblint joins them as well. A buffer collects the publications of a right-hand
side and joins those to the same target until a flush point
(#isaconst("buffer_sides")). Where several calls return at a node, it flushes only when the
right-hand side answers. Elsewhere, it flushes before every local read, so that
an entry state reaches the callee before the callee's exit state is demanded, as
in Goblint's normal-call transfer
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L242-L245")[`constraints.ml`]).
The analyzer runs these buffered right-hand sides, which compute the same join
as the right-hand sides of @sec:eq-call
(#isaconst("routed_node_rhs_buffered")). Under warrowing rules, the timing can change the computed
result, though not the equations it solves. @sec:outlook-extending discusses a
solver extension that would make seeds and buffering unnecessary.

== Solver certificates and partial correctness <sec:certificate>

Theorem 8.1 needs a post-solution on a set of unknowns that contains the
program entry and is closed under execution steps. A solve that terminates
provides a valuation #sol and a solved set $V$ on which #sol is a
post-solution, but $V$ is closed under the reads of right-hand sides, starting
from the result of `main`. The solver thus works backward from that result,
whereas executions run forward from the entry.

Backward and forward meet because every node of a procedure reaches the
procedure's result, since the compiler ends every body with a return edge
(@sec:compile). Under this property, the unknowns on which the query for
`main` depends account for every reachable state, for every solution
@seidl00[§9.1, Thm. 7(2), Thm. 9(2)]. Voblint mechanizes this argument and
extends it to side effects, seeds, dependences discovered during solving, and
context policies given as relations
(#isathm("dg_analysis.live_unknowns_cover", thy: "DG_Live_Unknowns", display: "live_unknowns_cover")).
The final theorem therefore needs no premise about which unknowns the solve
visited.

The argument applies to a solve that terminates, a property that is not
proved for the solver (@sec:td). It discovers contexts as it goes, and under
entry-state contexts a recursion can demand unboundedly many
(@sec:eval-precision). Isabelle defines the solver on the arguments for which
its recursion terminates (@sec:isabelle). Every run of the executable solver
that returns lies in this domain (#isathm("solve_dom_of_solve_c")), so the
theorems about the analyzer carry no separate termination premise.

#theorem(
  name: [States of a terminating solve],
  isa: "entry_state_activation_collect_sound_of_terminates",
)[
  Let $p$ be a well-formed program whose solve terminates under one of the
  context policies of @tab:eq-policies, and let $sol(v, c)$ be the state the
  solve returns for $(v, c)$. Then for every node $v$ and context $c$,
  $ cal(A)(v,c) subset.eq conc_(M)(sol(v, c)). $
]

The inclusion is proved once per kind of policy. The cited theorem covers
entry-state contexts. For unit and call strings, whose routing ignores the
entry state, a companion theorem proves it
(#isathm("fun_route_activation_collect_sound_of_terminates")).

Together, these results close the gap left by Theorem 8.1. The verified TD
solver solves any equation system given as strategy trees, and whenever a solve
terminates, its valuation is a post-solution on its solved set
(#isathm("td_certified_solver")). For the equations of @ch:equations, this
solved set contains the program entry and every unknown that an execution
reaches. The returned valuation therefore forms a valid cover for $cal(A)$
(Theorem 9.1). The inclusion of the collecting semantics in the analyzer's states is the next
step of the soundness chain in @fig:intro-nest. @ch:results collects these
states into the report and derives the verdicts from them.
