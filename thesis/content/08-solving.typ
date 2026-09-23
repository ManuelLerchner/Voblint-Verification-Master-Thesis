#import "../lib/code.typ": isaconst, isalocale, isathm, isatype
#import "../lib/sources.typ": thy
#import "../lib/math.typ": conc, lbot, lle, ltop, sol
#import "../lib/theme.typ": vb
#import "../lib/claims.typ": claim-snapshot

= Solving and the Executable Carrier <ch:solving>

The equation-soundness theorem of @ch:equations,
#isathm("activation_collect_dg_sound"), holds for any valuation that satisfies
the generated constraints. For RQ3 the solver should enter the argument only
through such a statement, so that replacing its algorithm or update rule
leaves the rest of the proof unchanged. The obvious statement has two problems. A
bound on every unknown's local result allows a valuation that claims a called
procedure never runs, and a bound over all unknowns cannot come from a solver
that evaluates only the unknowns its query demands (@sec:certificate). A third
obstacle is executability: the proofs speak about states on infinitely many
variable names, which a solver cannot compare. This chapter fixes the
certificate, shows that one proof covers every update rule, gives the finite
carrier the solver computes on, and explains why termination of the solve
remains a premise.

== The certificate between solver and semantics <sec:certificate>

@ch:background explained why a post-solution suffices. Widening can go above the
least solution by design, so it also makes a post-solution necessary. It
remains to decide which inequalities the certificate states, and for which
unknowns.

The solver has to accept side contributions. A callee's entry equation cannot
enumerate its contributors (@sec:eq-seed): under entry-state routing it would
join over every call site and every caller context whose entered state selects
the callee's context. Such a right-hand side reads unboundedly many unknowns,
and a local solver cannot evaluate it @apinis12. Voblint therefore reuses the
side-effecting top-down solver of Tilscher et al., which is proved partially
correct for such systems @tilscher26.

Write $T(u)$ for the right-hand side of an unknown $u$: the strategy tree of
@sec:eq-call, which reads unknowns, emits side contributions and returns a
local result $"eval"(T(u), sol)$. Bounding only that result,
$"eval"(T(u), sol) lle sol(u)$, fails at the first call. The caller publishes
the callee's entry state as a side contribution to the seed key of
@ch:equations, and the callee's entry equation reads that seed back. A
valuation that sets the seed and every unknown of the callee $f$ to #lbot, and
everything else to #ltop, satisfies every local bound: $f$'s entry reads #lbot,
and the transfers map #lbot to itself. Yet it claims that $f$ never runs. Only
the side contribution at the call site exceeds its target, so the certificate
must bound side contributions too.

The certificate also cannot range over all unknowns. The equation system is
total: it has an equation at every pair of a graph node and a context,
including contexts no call produces, and under entry-state routing the contexts
range over the abstract carrier. A top-down solver evaluates only the finite
part its query demands @seidl21 @tilscher26. Voblint poses a single query, the
exit of `main` in the root context (#isaconst("root_query")). Equations read
their predecessors, so a demand-driven solve evaluates the unknowns its query
transitively reads. From the exit of `main` these include every node from which
the exit can be reached, in each context the solve discovers for it. So one solve
replaces one query per program point. Apinis
et al. start local solving from the same unknown @apinis12. Keys that cannot
reach the exit, such as code after a `return`, are the subject of
@sec:live-keys. The certificate names the set $V$ of local unknowns the solve
reached:

#thy("part_post_solution")

It requires the query $x$ to lie in $V$ and, for every $u in V$, three facts.
The local dependencies of $u$ under the final valuation stay inside $V$, so
every value a certified equation reads is itself certified. Without this
conjunct a certified equation could read an unknown outside $V$ whose value is
arbitrary, for instance #lbot, and the bound on its result would say nothing
about the executions that pass through the unknown it read. The local result of
$T(u)$ is bounded by $sol(u)$. The side contributions of $T(u)$, joined per
target key, are bounded by #sol pointwise. Global unknowns are constrained only
in this way.

@fig:td-trace shows where $V$ comes from. The solver starts from the query,
evaluates a right-hand side only when some evaluation reads its unknown, and
marks a loop point when a read reaches an unknown that is still being computed.
Among local unknowns only loop points are widened and narrowed; contributions to
global unknowns are merged by the update rule of @sec:update-rules. The
unknowns the solver stabilized form $V$.

#let _td = (
  // (evaluating, event, pp0, pp1, pp2, pp3, being computed, loop points),
  // transcribed from query/iterate of TD_side_upd_rule for this system.
  ("pp3", [put on $c$; its equation reads `pp1`], "⊥", "⊥", "⊥", "⊥", "pp3", ""),
  ("pp1", [not on $c$: computed now; reads `pp0`, then `pp2`], "⊥", "⊥", "⊥", "⊥", "pp3 pp1", ""),
  ("pp0", [reads nothing; stable at once], "⊤", "⊥", "⊥", "⊥", "pp3 pp1", ""),
  (
    "pp2",
    [reads `pp1`, which is on $c$: gets its current value; `pp1` becomes a loop point],
    "⊤",
    "⊥",
    "⊥",
    "⊥",
    "pp3 pp1 pp2",
    "pp1",
  ),
  ("pp2", [evaluates to its current value; done], "⊤", "⊥", "⊥", "⊥", "pp3 pp1", "pp1"),
  (
    "pp1",
    [evaluates to `[0,0]`; the round began before the loop point was found, so no widening; `pp2` is destabilized],
    "⊤",
    "[0,0]",
    "⊥",
    "⊥",
    "pp3 pp1",
    "pp1",
  ),
  ("pp2", [recomputed from `pp1`], "⊤", "[0,0]", "[0,0]", "⊥", "pp3 pp1", "pp1"),
  (
    "pp1",
    [equation gives `[0,1]`; a loop point that grew is widened],
    "⊤",
    "[0,+∞]",
    "[0,0]",
    "⊥",
    "pp3 pp1",
    "pp1",
  ),
  ("pp2", [`i < 5` filters `[0,+∞]`], "⊤", "[0,+∞]", "[0,4]", "⊥", "pp3 pp1", "pp1"),
  (
    "pp1",
    [equation gives `[0,5]`, below the value: narrowed],
    "⊤",
    "[0,5]",
    "[0,4]",
    "⊥",
    "pp3 pp1",
    "pp1",
  ),
  ("pp1", [one more round changes nothing; stable], "⊤", "[0,5]", "[0,4]", "⊥", "pp3", ""),
  ("pp3", [`i >= 5` filters `[0,5]`; every unknown stable], "⊤", "[0,5]", "[0,4]", "[5,5]", "", ""),
)
// The rows the figure prints: loop-point detection, widening, narrowing and the
// final state. The full run is kept so the numbering stays that of the solver.
#let _shown = (0, 3, 5, 7, 9, 11)
// The trace is transcribed by hand; its end state must be the analyzer's.
#let _loop = claim-snapshot("counting-loop-snapshot")
#for (i, point) in ("pp0", "pp1", "pp2", "pp3").enumerate() {
  let n = _loop.nodes.values().find(n => n.label == point)
  assert(
    n.lines.first() == "i=" + _td.last().at(2 + i),
    message: "solver trace ends off the analyzer's value at " + point,
  )
}

#figure(
  {
    set par(first-line-indent: 0pt, justify: false)
    set text(size: 8pt)
    show raw: set text(size: 7.5pt)
    let eq(l, r) = (raw(l), [$=$], r)
    align(center, grid(
      columns: 3,
      column-gutter: 4pt,
      row-gutter: 5pt,
      align: (right, center, left),
      ..eq("pp0", [#raw("⊤") #h(4pt) #text(fill: vb.muted)[(the stores entering `main`)]]),
      ..eq("pp1", [`[i := 0] pp0` $union.sq$ `[i := i + 1] pp2`]),
      ..eq("pp2", [`assume (i < 5) pp1`]),
      ..eq("pp3", [`assume (¬ i < 5) pp1`]),
    ))
    v(4pt)
    let val(v) = if v == "⊥" { text(fill: vb.muted, raw(v)) } else { raw(v) }
    table(
      columns: (auto, auto, 1fr, auto, auto, auto, auto, auto, auto),
      align: (right, left, left, center, center, center, center, left, left),
      stroke: none,
      inset: (x: 3pt, y: 2.2pt),
      table.hline(stroke: 0.5pt),
      [*\#*],
      [*runs*],
      [*event*],
      [*`pp0`*],
      [*`pp1`*],
      [*`pp2`*],
      [*`pp3`*],
      [*on $c$*],
      [*loop pts*],
      table.hline(stroke: 0.4pt),
      .._td
        .enumerate()
        .filter(((i, r)) => i in _shown)
        .map(((i, r)) => (
          [#(i + 1)],
          raw(r.at(0)),
          r.at(1),
          ..r.slice(2, 6).map(val),
          raw(r.at(6)),
          raw(r.at(7)),
        ))
        .flatten(),
      table.hline(stroke: 0.5pt),
    )
    v(3pt)
    align(center, grid(
      columns: 2,
      column-gutter: 6pt,
      row-gutter: 4pt,
      align: (right, left),
      text(fill: vb.muted)[post-solution:],
      $[i := 0] top union.sq [i := i + 1] [0, 4] = [0, 5] subset.eq.sq sigma(#raw("pp1"))$,

      [], $"assume"(i < 5) [0, 5] = [0, 4] subset.eq.sq sigma(#raw("pp2"))$,
      [], $"assume"(i >= 5) [0, 5] = [5, 5] subset.eq.sq sigma(#raw("pp3"))$,
    ))
  },
  kind: image,
  placement: auto,
  caption: [The top-down solver on the counting loop of @fig:source-morph,
    simplified to four local unknowns without contexts or side effects. Each row
    is one evaluation of a right-hand side, numbered in run order (six
    bookkeeping evaluations are omitted), with the values $sigma$ after it,
    the unknowns being computed ($c$, in call order) and the loop points, as in
    the vendored solver. A loop point is warrowed: widened while it
    grows, narrowed once it shrinks. Transcribed by hand; the final values are
    checked against the analyzer and form a post-solution (last line).],
) <fig:td-trace>

The collecting-soundness argument uses no other fact about the solver. It
assumes the bounds on any set containing the query, so replacing the solver
leaves that argument unchanged. The vendored theorem
#isathm("partial_post_solution") derives the certificate for the stabilized set
from membership of the query in the domain of definition of the solver's
recursion. Publishing a result needs one further fact, proved once for the
solver locale from its stable-set invariant: by #isathm("finite_stabl_solve") a
terminating solve returns a finite key set. The `DEAD` verdict of
@sec:verdicts aggregates over all contexts of a node and relies on it. Domain
membership for the program's query is the termination premise, and
@sec:termination explains why it stays a premise.

== One proof for four update rules <sec:update-rules>

The solver merges each side contribution into its global unknown, and the
merge affects both precision and termination. Voblint offers several merges
and proves the solver sound for all of them at once. A merge is an _update
rule_.
Stemmler et al. proposed such rules @stemmler25, and Tilscher et al. formalize a
generic update-rule interface and prove five of them sound against it
@tilscher26. Every rule records each origin's latest contribution, where the
origin is the unknown whose equation published it, and a newer contribution
replaces the older one from the same origin. The rules differ in how they form
the new value of the global. Voblint exposes four of them: join the
contribution into the value, join the recorded contributions, warrow the value
toward that join, or warrow the origin's own record and then join the records.
The fifth vendored rule, which bounds narrowing by a counter, is not selectable.
In #isaconst("run_voblint") the entry seeds are the only global unknowns that
receive contributions (@sec:mixed-flow), so the rule decides how a callee's
entry state accumulates across call sites (@fig:update-rules).

Per-origin warrowing targets a global that receives one constant from each of
several locations. Seidl et al. show on such a global that widening the
accumulated interval loses both bounds, while per origin each record holds a
single value and nothing is widened @seidl26. The gain is limited to the case where
several origins feed one unknown. A recursive call that feeds a growing value back
into the seed it reads is a single origin, and warrowing one origin separately
from itself changes nothing.

The choice of rule also affects termination. The two joining rules never widen
a seed. On the interval domain, the recursion `f(x) { f(x + 1) }` entered with
$x = 0$ contributes the entries $[0, 0], [0, 1], [0, 2], dots$ to the one seed of
`f`, a strictly ascending chain. Under join and per-origin the solve does not
finish within the 5 s limit of @fig:rules-programs, while both warrowing rules
widen the entry to $[0, +infinity]$ and return. Either kind of rule can be more
precise: the same table contains a program on which the joining rules are exact
and warrowing is not.

No solver fact is proved per rule. The datatype #isatype("globals_rule")
names the four rules, #isaconst("update_global_of") selects the vendored
implementation, and one interpretation of the solver locale takes the rule as a
parameter, so every solver fact, the certificate included, holds for all four
at once. Only #isathm("update_rule_update_global_of"), which shows that the
selected function meets the update-rule interface, splits on the rule and cites
the four vendored interpretations.

#figure(
  {
    set text(size: 8.5pt)
    show raw: set text(size: 8pt)
    // Bold and a nabla as well as colour, so the mark survives greyscale.
    let w(v) = text(fill: vb.unstable, weight: "bold", [#raw(v)#super[$nabla$]])
    let r(v) = raw(v)
    let rule(name, c) = [#name \ #text(size: 8pt, c)]
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
      rule([join], isaconst("update_global_always_join")),
      r("[0,3]"),
      r("[0,4]"),
      r("[0,4]"),
      r("[0,8]"),
      rule([join per origin], isaconst("update_global_per_origin")),
      r("[0,3]"),
      r("[0,4]"),
      r("[1,4]"),
      r("[0,8]"),
      rule([warrow], isaconst("update_global_warrowing_apinis")),
      r("[0,3]"),
      w("[0,+∞]"),
      r("[0,4]"),
      w("[0,+∞]"),
      rule([warrow per origin], isaconst("update_global_warrowing_per_origin")),
      r("[0,3]"),
      r("[0,4]"),
      r("[0,4]"),
      w("[0,+∞]"),
      table.hline(stroke: 0.5pt),
    )
  },
  kind: table,
  caption: [One global unknown under each update rule, from #raw("⊥"), after
    four interval contributions from origins A and B. Join per origin reports
    the join of each origin's latest contribution, so at step 3 A's
    #raw("[1,1]") replaces #raw("[0,3]"). Warrow widens at step 2, because
    #raw("[0,4]") is not below #raw("[0,3]"), and narrows at step 3; warrow per
    origin widens only when A's own contribution grows. A widened bound is set
    bold and marked $nabla$. Computed by hand from the vendored update rules
    with Voblint's interval operators #isaconst("widen_ivl_core") and
    #isaconst("narrow_ivl_td")\; the contributions separate the rules and come
    from no program.],
) <fig:update-rules>

== A finite state with two defaults

Soundness is stated over states $"Var" -> A$, functions on an infinite set of
names whose equality is not executable, while the solver compares values at
every update. A sparse map that reads every unlisted variable as #ltop is the
smaller representation, but three states the analysis uses do not fit it. The
solver starts every unknown at the everywhere-#lbot state, which such a map
cannot represent at all. The initial state maps every global to the abstraction
of zero and every local to #ltop. The initial stores constrain every name the
classifier calls global, with no finiteness hypothesis, so a map with default #ltop
could express this state only by listing each declared global. The entry state
would then depend on the declaration list, and so would every soundness
statement that mentions it. The global half of a published state sets its
locals to #lbot, which makes it a unit for joining publications from several
call sites. With #ltop there, it would not be a unit. The executable carrier
#isatype("resolved_st_q") therefore stores two defaults and a list of
overrides indexed by _locations_, which tag a name as local or global:

#thy("lookup_resolved_st")

Reading a variable looks up the location the program's classifier assigns to
it (#isaconst("fun_of_resolved_st_q_for")), so an override under the other tag
is invisible. The start state is $(lbot, lbot, [])$, the initial state
$(ltop, 0^sharp, [])$, and a published global half $(lbot, d_g,
  italic("ps")_g)$. The type is a quotient that identifies representations with
equal lookups.

== Computing on one state, proving on the other

Instead of reproving the transfer soundness of @ch:analysis-interface for the
carrier, we show that each carrier operation commutes with readback $rho$:
$ rho("op"_"exec" (s)) = "op"_"abs" (rho(s)). $
For the generic numeric transfer this is #isathm("generic_tf_st_for_commute"),
with the branch filter as the one per-domain premise, and concretizing a
carrier state as $conc(rho(s))$ transports every soundness fact. A
carrier-level proof per domain would repeat every transfer argument for each
representation.

Emptiness, on which `DEAD` rests, is a condition over all names (@ch:domains)
and needs a finite test: it inspects the local default, the overrides at the
locations the classifier selects, and the declared globals, enumerated
explicitly because a fresh global need not exist.
#isathm("resolved_st_q_is_bot_for_iff") proves the test equivalent to semantic
emptiness, provided the supplied list enumerates exactly the classifier's
globals. Collapsing a state to #lbot is sound as soon as the test implies
emptiness, but both directions are used. The specification collapses exactly
the empty states, so only an exact test lets the executable collapse commute
with readback. A state the test keeps is then known to be nonempty
(#isaconst("live_resolved_st_q")), and the numeric transfer commutes with
readback only on such states.

== Why termination stays a premise <sec:termination>

The vendored solver is a recursive HOL function whose termination is not known
in general, so Isabelle defines it together with a domain predicate, the set of
arguments on which the recursion is well founded. The certificate of
@sec:certificate holds on that domain. For a configuration and a program,
#isaconst("config_terminates") states that the query of the program lies in it.
The premise cannot be replaced by the premise that the analyzer answered. HOL
functions are total, so outside the domain the solver still denotes some
value, only an unspecified one, and #isaconst("run_voblint") may formally
return an answer that no execution of the code computes. The generated code
runs the executable form of the solver instead, which returns only when the
recursion finishes, and #isathm("solve_dom_of_solve_c") turns a finished run
into domain membership. A premise of this shape can therefore be discharged by
evaluating the solve for one program.

A theorem that discharges the premise for every program cannot hold in the
present design, because termination fails for some configurations. Under
entry-state contexts on the interval domain, a recursion that changes its
argument at every level meets a fresh context at every level, and widening
bounds the values of existing unknowns without bounding how many are created
(@sec:eq-finite). Under the joining update rules, the growing recursion of
@sec:update-rules contributes a strictly ascending chain of entry states that no
rule widens. Neither divergence is machine-checked. Their regression programs
do not finish within their time limits, and the argument above is why we expect
divergence. A timeout alone would not prove it (@sec:trust-boundary).

The vendored development also offers no restricted theorem to reuse. The
side-effecting solver is proved partially correct only. The vendored
termination theorems cover top-down variants without side effects and assume a
finite type of unknowns @tilscher26. Voblint's unknowns pair a graph node
with a context, and the node type alone is infinite, since a statement node
carries any natural number. This already excludes the finite domains and
finite context spaces, where a restricted theorem would be plausible. Seidl
and Vogler prove termination of their side-effecting variant on paper whenever
only finitely many unknowns are encountered @seidl21. Mechanizing a result of
that kind for the vendored solver, relative to the keys a program creates, is
future work. The end-to-end theorem is therefore a partial-correctness result
with a per-program premise (@sec:headline).

The chapter gives the solver's share of RQ3 and K3. The solver enters the
argument only through #isaconst("part_post_solution") on the stabilized set,
which the vendored #isathm("partial_post_solution") derives from the premise
that the solver's recursion is defined on the query, and through the finite key
set of #isathm("finite_stabl_solve"). One interpretation of the solver locale,
parameterized by the rule, makes both hold for all four update rules at once
(#isathm("update_rule_update_global_of")). The certificate idea itself is
established practice, as in CompCert's dataflow-solver interface @compcertKildall.
Its use for side-effecting, context-indexed systems is part of K3. The executable
carrier transports every soundness fact by commuting with readback
(#isathm("generic_tf_st_for_commute")), and its finite emptiness test is exact
(#isathm("resolved_st_q_is_bot_for_iff")). Termination is the one solver fact
that is not proved: it fails for some configurations, so the source-level
theorem of @ch:results assumes it per program, and
#isathm("solve_dom_of_solve_c") lets a finished run discharge it.
