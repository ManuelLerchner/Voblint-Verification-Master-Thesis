#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "@preview/cetz:0.5.2"
#import "../lib/code.typ": fixture, isaconst, isai, isalocale, isathm, isatype, listing, thy-badge
#import "../lib/sources.typ": thy, update-rule-steps
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/claims.typ": claim-ref, claim-snapshot, claim-text

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

@ch:equations showed that a post-solution of the generated equations is
sound. At every node and context, its abstract state describes every store that
an execution reaches there in that context
(#isathm("activation_collect_dg_sound")). The solver, however, makes the
valuation a post-solution only on its solved set, so the theorem requires this
set to contain the program entry and every unknown that an execution can reach
from it. This chapter shows that the analyzer obtains such a solved set and
post-solution. Voblint solves the equations with the
verified top-down solver of Tilscher et al. @tilscher26, which is proved
partially correct. To use it, we first bring the equations into the form the
solver accepts and then derive the premises about the solved set from the
solver's correctness theorem.

== Adapting the equations to the solver <sec:eq-encoding>

The solver accepts a right-hand side only as a strategy tree, uses one value
type for all unknowns, and allows side effects only to global unknowns. A direct encoding of the equations, along the lines of Apinis et al.
and Goblint, needs four things this interface does not offer
(@tab:eq-adapters). @ch:equations already stated the equations in the adapted
form, and this section explains why each adaptation is needed. Buffering is the
only adapter applied to a right-hand side after it is built. It changes when
publications are issued but not what the right-hand side computes, publishes,
or reads (@sec:eq-buffer). The adapters change the equations, not the solver.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    stroke: none,
    table.hline(),
    [*the equations need*], [*the solver provides*], [*adapter*],
    table.hline(stroke: 0.5pt),
    [value-dependent reads], [strategy trees], [call tree (@sec:eq-trees)],
    [a write to a local unknown], [writes to globals only], [seed (@sec:eq-seed-global)],
    [two value types], [one value type], [product (@sec:global-unknowns)],
    [two writes to one target], [updates that may not stabilize], [buffering (@sec:eq-buffer)],
    table.hline(),
  ),
  placement: none,
  caption: [What the equations of Apinis et al. and Goblint require, what the
    vendored solver provides instead, and the adapter that closes each gap. A
    call chooses the result it reads from the caller's state, writes the
    callee's entry state to a local unknown, keeps local states and analysis
    globals in different domains, and may write one seed twice in one
    evaluation. The solver accepts such writes but updates after each one,
    and under warrowing these updates may not stabilize.],
) <tab:eq-adapters>

=== Dynamic reads #thy-badge("Voblint_Framework", "Routed_Call_Programs") <sec:eq-trees>

A local edge always reads the same unknown, its predecessor. A call, in
contrast, chooses what to read from values it has already read. In the running
example, the continuation $(italic("pp3"), c_0)$ first reads the caller
$(italic("pp2"), c_0)$. From that value it computes the entry state
$n = [5, 5]$, which determines the context $c_1$ and thus the result it reads
next, $(ctor("FunctionResult") thin italic("bump"), c_1)$.
The vendored solver accepts a right-hand side only as a strategy tree, which
issues one read at a time and passes each value read to a continuation
(@sec:td). Every right-hand side of Voblint is such a tree. For a local edge
the tree reads the predecessor and applies the transfer. For a call it chains reads whose
continuations choose the next read from the value received. In the notation of
@sec:td, the contribution of
a call at $u$ in context $c$ (#isaconst("rhs_call")) is the value of the tree
$t_"call"$,
$
  t_"call" = #ctor("QueryL") ( & (u, c), lambda d. \
                               & #ctor("Side") ( ctor("Activation_Seed") thin p space c', e, \
                               & quad #ctor("QueryL") ( (ctor("FunctionResult") thin p, c'), lambda r.
                                   #ctor("Answer", thy: "Basics_side") (sh("combine") (q, r)) ) ) ),
$
The tree first reads the caller's state $d$ at the call site and computes the
entry pair $(q, e) = enterh(d)$ and the callee context $c' = ctxh(u, c, e)$.
It then publishes the entry state $e$ for the callee's entry in $c'$, reads
the callee's result $r$, and answers $sh("combine")(q, r)$, the abstract state
of the caller once the call has returned. #isaconst("routed_call_program") implements
this tree and additionally handles bottom entry states and several callees or
entry pairs.

=== Local entries <sec:eq-seed-global>

In $t_"call"$ the caller pushes the entry state to the callee with a
#ctor("Side") step. Otherwise, the equation of the callee's entry would have
to read every call routed to it. Under entry-state contexts, however, these
calls depend on the entry states, which are known only while the equations are
solved (@sec:eq-call).
Apinis et al. push the entry state directly into the callee's entry
$(ctor("FunctionEntry") thin p, c')$ @apinis12[§6], and Goblint does the same
with its local side effect `sidel`
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L244")[`constraints.ml`]).
That entry, however, is a local unknown, and the vendored solver's
#ctor("Side") accepts only global unknowns. Allowing local targets would mean
changing the solver and redoing its correctness proof.

Voblint therefore publishes the entry state to the callee's seed, a global
unknown that the entry reads (@sec:eq-call).

Seeds have a known disadvantage compared with a side effect into the local
entry. As global unknowns, they are merged by the update rule for globals
(@sec:update-rules), which may widen an entry state even when no loop or
recursion is involved. Without contexts, both calls of the running example
publish to the one seed of `bump`, and warrowing widens it. The analyzer then
reports #_cli("pg-contexts-none", "a == 6", 3) for `a == 6` with
#_cli("pg-contexts-none", "a == 6", 4), whose lower bound $-infinity$ comes
from this widening.

=== One value type #thy-badge("Voblint_Framework", "DG_State") <sec:global-unknowns>

A local unknown holds an abstract state of the analysis's local domain, and an
analysis global holds a value of its global domain (@sec:shared-facts). The
vendored solver, however, has a single value type $'d$ for all unknowns, so Voblint
stores both kinds in their product: every unknown holds a pair #isatype("dg_state") of
a local and a global half, #isaconst("dg_local") and #isaconst("dg_global"),
uses one half and leaves the other at $lbot$ (@tab:eq-carrier). Order and join
on pairs work componentwise, so the solver's requirements on the value type
follow from those on the two halves. The half an unknown uses depends on what it stores, not on
whether the solver treats it as global. A seed, for example, is a global
unknown, because calls publish to it, but it stores an entry state, which is a
local value.

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
  placement: auto,
  caption: [Which half of #isatype("dg_state") each kind of unknown uses. The
    global unknowns are named by #isatype("global_unknown").],
) <tab:eq-carrier>

Transfers never see the pair or the seeds. Goblint combines the two kinds of value in a
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/constraint/translators.ml#L30-L32",
)[lifted sum]
instead, in which each unknown holds a value of exactly one of the two kinds.
Voblint uses the product because its componentwise lattice structure keeps
the Isabelle proofs simple, at the price of an unused #lbot half in every
unknown.

== Merging contributions to global unknowns #thy-badge("TD", "Update_rules") <sec:update-rules>

A global unknown such as a seed receives contributions from several places.
The solver merges each new contribution into the value it holds, and this
merge, the _update rule_, decides both precision and termination. Stemmler et
al. compare existing update rules and propose new ones @stemmler25[§3–4], and Tilscher et al. formalize a
generic interface for them and prove five rules sound against it
@tilscher26.

The rules differ in what they keep per _origin_, the right-hand side that
sent a contribution (@sec:td), and in whether they widen. _Join_ joins every
contribution into the value, and _join per origin_ reports the join of each
origin's latest contribution. _Warrow_ and _warrow per origin_ warrow toward
the same join or per origin, and _bounded narrowing_ additionally limits how
often an origin may switch from widening to narrowing. @fig:update-rules runs
all five on one sequence of contributions. In #isaconst("run_voblint") the rule
decides how a callee's entry state accumulates across call sites and how a
flow-insensitive program global (@sec:mixed-flow) accumulates its writes. No
rule is more precise on every program, and @sec:eval-precision compares them.

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
    four interval contributions from origins A and B, which separate the rules
    and come from no program. Widened bounds are bold and marked $nabla$. The
    cells are computed by #isathm("update_rules_example") from the vendored
    rules.],
) <fig:update-rules>

=== Repeated publications #thy-badge("Voblint_Solver", "Strategy_Tree_Side_Buffering") <sec:eq-buffer>

One right-hand side can publish to the same global unknown twice, for example
when two calls that resume at the same node are routed to the same callee
context and write the same seed. The equations read two writes to one target
$g$ as one bound:
$
  #ctor("Side") (g, a); #ctor("Side") (g, b)
  quad "means" quad
  sol(g) lge a ljoin b.
$
The vendored solver, however, applies the update rule at every #ctor("Side").
A per-origin rule (@sec:td) therefore records first $a$ and then
$a union.sq b$, so in every re-evaluation the recorded contribution shrinks
and grows back. Under warrowing the shrinking step narrows, the growing step
widens again, and the solver may not stabilize. The update rules of Stemmler
et al. assume one joined contribution per target and evaluation
@stemmler25[§3], and Goblint, when `narrow-globs` is enabled, joins the side
effects of an evaluation before its per-origin update
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/solver/td3UpdateRule.ml#L113-L228")[`td3UpdateRule.ml`]).

Voblint joins them as well. #isaconst("buffer_sides") collects the
publications of a right-hand side and joins those to the same target until a
flush point. Where several calls return at a node, it flushes only when the
right-hand side answers. Elsewhere it flushes before every local read, so that
an entry state reaches the callee before the callee's result is demanded, as
in Goblint's normal-call transfer
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L242-L245")[`constraints.ml`]).
The buffered generator #isaconst("routed_node_rhs_buffered"), which the
analyzer runs, answers the same join as the direct generator of
@sec:eq-call. Under widening update rules the timing can change the computed
result, though not the equations it solves. @sec:outlook-extending discusses a
solver extension that would make seeds and buffering unnecessary.

== What a terminating solve guarantees <sec:certificate>

The soundness theorem of @sec:eq-discharge needs a post-solution on a set of
unknowns that contains the program entry and is closed under execution steps.
A solve that returns provides something different. It gives a valuation #sol
and a set $V$ of local unknowns on which #sol is a post-solution, and $V$ is
closed under the reads of right-hand sides, starting from the result of
`main`. The solver thus works backward from that result, whereas the theorem
follows executions forward from the entry. The two directions meet because
every node of a procedure reaches the procedure's result, even code after a
`return`, since the compiler ends every body with a return edge
(@sec:compile). Once a procedure's result is solved in a context, closure under
reads makes all its nodes solved in that context. Executions from the entry of
`main` stay among these nodes, which
#isathm("dg_analysis.live_unknowns_cover", thy: "DG_Live_Unknowns", display: "live_unknowns_cover")
proves from a well-formed program and a returned solve alone. The final theorem
therefore needs no premise about which unknowns the solve visited.

The solver is not proved to terminate. HOL admits only terminating recursion,
so Isabelle defines the solver with a domain predicate
(#isaconst("solve_dom", thy: "TD_side_upd_rule"), @sec:isabelle), the
arguments on which its recursion terminates, and proves its correctness on that
domain. The analyzer runs the executable form
#isaconst("solve_c", thy: "TD_side_upd_rule"), which returns only when the
recursion finishes, and #isathm("solve_dom_of_solve_c") turns a returned run
into domain membership. The theorems about #isaconst("run_voblint") therefore
have no termination premise. The solve starts from one query, the result of
`main` in the initial context
(#isaconst("dg_pipeline.root_query", thy: "DG_Analysis", display: "root_query"),
as in @apinis12[§3]), and evaluates an unknown only when a right-hand side it
is solving reads it @seidl21 @tilscher26. It thus discovers contexts as it
goes, and whether it returns depends on how many unknowns it reaches. Under
entry-state contexts a recursion can demand unboundedly many
(@sec:eval-precision). The existing termination theorems do
not apply to Voblint (@sec:rel-solvers), so the end-to-end theorem
(@sec:headline) is a partial-correctness result about every report the
analyzer returns.

The rest of the soundness proof never looks inside the solver. It needs the
returned valuation to be a post-solution on the solved set, which is the
certificate below, and the solved set to be finite, so that
@ch:results can join the finitely many contexts solved at a node into one
verdict. Two further facts connect the analyzer's run with the solver of the
proof. The certificate holds only on the solver's domain, so every run that
returns must lie in it, and the executable code must compute the same result
as the solver defined in the logic. Voblint therefore keeps the
solver as a parameter of the analysis. The analysis locale
#isalocale("dg_analysis") extends #isalocale("certified_solver"), which states
the four facts, and #isathm("td_certified_solver") proves them for the vendored
solver under every update rule.

The verified solver states its guarantee as the certificate
#isaconst("part_post_solution", thy: "Basics_side") of @sec:side-effects, over
the equation system $T$, the valuation #sol and the solved set `vars`:

#thy("part_post_solution")

$T$ (#isatype("eqsT", thy: "Basics_side")) maps each unknown $u$ to its
strategy tree $T med u$. Evaluating a tree under the final valuation #sol
determines three things: the answer it returns, the local unknowns it reads,
and the contributions it publishes. In Isabelle these are
$#isaconst("eq", thy: "Basics_side") med T med u med sol$,
$#isaconst("dep\<^sub>L") med T med sol med u$, and
#isaconst("sides_of_rhs"), which joins the published values per target and is
#lbot where the tree publishes nothing.  With them the
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
pointwise. These are all the solver guarantees about #sol.

The certificate supplies what @sec:eq-discharge assumes about the solve. (C3)
and (C4) make #sol a post-solution for the local and the global unknowns. (C1)
and (C2), through the closure argument above, give a solved set that contains
the program entry and is closed under execution steps. The remaining premises
of the theorem there concern the analysis and the routing, which earlier
chapters discharge. For every solve that returns, the solved states therefore
cover the context-indexed collecting semantics
(#isathm("entry_state_activation_collect_sound_of_terminates")), and the five
obligations of @ch:traces hold as @tab:eq-obligations shows. @ch:results turns
these states into verdicts.
