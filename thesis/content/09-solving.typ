#import "../lib/code.typ": fixture, isaconst, isalocale, isathm, isatype
#import "../lib/sources.typ": thy
#import "../lib/math.typ": lbot, lle, ltop, sem, sol
#import "../lib/theme.typ": vb
#import "../lib/claims.typ": claim-snapshot

= Solving and the Executable Carrier <ch:solving>

This chapter answers what the solver must guarantee so that the rest of the
proof can use its result, and how an executable solver provides it. The
equation-soundness theorem of @ch:equations holds for any valuation that
satisfies the generated constraints (#isathm("activation_collect_dg_sound")). For a compositional proof the solver
should enter the argument only through such a statement, so that replacing its
algorithm or update rule leaves the rest of the proof unchanged. The obvious
statement has two problems. A bound on every unknown's local result allows a
valuation that claims a called procedure never runs, and a bound over all
unknowns cannot come from a solver that evaluates only the unknowns its query
demands (@sec:certificate). A third obstacle is executability: the proofs speak
about states on infinitely many variable names, which a solver cannot compare
(@sec:readback). Termination of the solve remains a premise
(@sec:termination).

== The certificate between solver and semantics <sec:certificate>

@ch:background explained why a post-solution suffices. Widening can go above the
least solution by design, so it also makes a post-solution necessary. It
remains to decide which inequalities the certificate states, and for which
unknowns.

The solver has to accept side contributions, because a callee's entry equation
cannot enumerate its contributors (@sec:eq-call). Voblint therefore reuses the
side-effecting top-down solver of Tilscher et al., which is proved partially
correct for such systems @tilscher26.

Write $T(u)$ for the right-hand side of an unknown $u$: the strategy tree of
@sec:eq-trees, which reads unknowns, emits side contributions and returns a
local result $"eval"(T(u), sol)$. Bounding only that result,
$"eval"(T(u), sol) lle sol(u)$, fails at the first call. The caller publishes
the callee's entry state as a side contribution to the seed of
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
the exit can be reached, in each context the solve discovers for it. A single
solve therefore takes the place of one query per program point. Apinis
et al. start local solving from the same unknown @apinis12[§3]. Unknowns that cannot reach the exit, such as code after a `return`, are the subject of
@sec:live-keys. The certificate names the set $V$ of local unknowns the solve
reached:

#thy("part_post_solution")

It requires the query $x$ to lie in $V$ and, for every $u in V$, three facts.
Which unknowns a right-hand side reads can depend on the values it reads
(@sec:eq-trees), so the dependencies are taken under the final valuation. The
local dependencies of $u$ stay inside $V$, so
every value a certified equation reads is itself certified. Without this
conjunct a certified equation could read an unknown outside $V$ whose value is
arbitrary, for instance #lbot, and the bound on its result would say nothing
about the executions that pass through the unknown it read. The local result of
$T(u)$ is bounded by $sol(u)$. The side contributions of $T(u)$, joined per target global unknown, are bounded by #sol pointwise. Global unknowns are constrained only
in this way.

$V$ is the set of unknowns the solver stabilized, starting from the query
(@sec:td, @fig:td-trace). Among local unknowns only loop points are widened and
narrowed. Contributions to global unknowns are merged by the update rule of
@sec:update-rules.

The collecting-soundness argument uses no other fact about the solver. It
assumes the bounds on any set containing the query, so replacing the solver
leaves that argument unchanged. The pipeline locale #isalocale("dg_analysis")
therefore takes the solver as a parameter and states three contracts about it.
First, a solve whose recursion is defined on the query returns a
post-solution on its stabilized set. The vendored theorem
#isathm("partial_post_solution") provides this. Second, such a solve returns a
finite set of unknowns. Voblint proves this once for the solver locale from its
stable-set invariant (#isathm("finite_stabl_solve")). The `DEAD` verdict of
@sec:verdicts aggregates over all contexts of a node and relies on it. Third, a
run of the executable solver that returns a result lies in that domain
(#isathm("solve_dom_of_solve_c"), @sec:termination). Every registration of an
analysis with the pipeline discharges the three contracts by citing these
facts at its update rule. Domain membership for the program's query is the
termination premise, and @sec:termination explains why it stays a premise.

== One proof for four update rules <sec:update-rules>

The solver merges each side contribution into its global unknown, and the
merge affects both precision and termination. Voblint offers several merges
and proves the solver sound for all of them at once (#isathm("update_rule_update_global_of")). A merge is an _update
rule_.
Stemmler et al. proposed such rules @stemmler25 (TODO: check locator), and Tilscher et al. formalize a
generic update-rule interface and prove five of them sound against it
@tilscher26. Every rule keeps one record per origin, the unknown whose equation
published the contribution. Most rules store the origin's latest contribution
there; per-origin warrowing stores the old record warrowed with the new
contribution. The rules differ in what they record and in how they form the
new value of the global. Voblint exposes four of them: join the
contribution into the value, join the recorded contributions, warrow the value
toward that join, or warrow the origin's own record and then join the records.
The fifth vendored rule, which bounds narrowing by a counter, is not selectable.
Voblint also proves sound a keyed combination that joins at entry seeds and
warrows elsewhere; only examples use it.
In #isaconst("run_voblint") the entry seeds are the only global unknowns that
receive contributions, because the selectable analyses use no analysis globals
(@sec:coop-limits). The rule therefore decides how a callee's entry state
accumulates across call sites (@fig:update-rules).

Per-origin warrowing helps when several origins feed one global, as Seidl et
al. show on a global that receives one constant per location @seidl26[§1]. A recursive call that feeds a growing value back into its own
seed is a single origin, where the rule gains nothing and can lose precision
(@sec:eval-rq4).

The choice of rule also affects termination. The two joining rules never widen
a seed, so a recursion that enters with a growing argument can keep the solve
running (@sec:termination), while both warrowing rules widen the entry and
return. Either kind of rule can be more precise: @fig:rules-programs contains a
program on which the joining rules are exact and warrowing is not.

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

No solver fact is proved per rule. The datatype #isatype("globals_rule")
names the four rules, #isaconst("update_global_of") selects the vendored
implementation, and one interpretation of the solver locale takes the rule as a
parameter, so every solver fact, the certificate included, holds for all four
at once. Only #isathm("update_rule_update_global_of"), which shows that the
selected function meets the update-rule interface, splits on the rule and cites
the four vendored interpretations.


== An executable state with two defaults <sec:readback>

The pointwise numeric analyses state soundness over states $"Var" -> A$,
functions on an infinite set of names whose equality is not executable, while
the solver compares values at every update. A sparse map that reads every unlisted variable as #ltop is the
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

Instead of reproving the transfer soundness of @ch:analysis-interface for the
carrier, we show that each carrier operation commutes with readback $rho$:
$ rho("op"_"exec" (s)) = "op"_"abs" (rho(s)). $
Concretizing a carrier state as $sem(rho(s))$ then transports every soundness
fact. A carrier-level proof per domain would repeat every transfer argument for
each representation. The locale #isalocale("dg_analysis_exec") states the
commutation as its readback contract, for the transfer on nonempty states and
for procedure entry. For a certified operation bundle both hold without a
per-domain proof: the abstract and executable steps are derived from the same
operations (#isathm("sound_nonrelational_ops.tf_st_for_commute"),
@sec:instances-supply).

Emptiness, on which `DEAD` rests, is a condition over all names (@ch:domains)
and needs a finite test: it inspects the local default, the overrides at the
locations the classifier selects, and the declared globals, enumerated
explicitly because a fresh global need not exist.
#isathm("resolved_st_q_is_bot_for_iff") proves the test equivalent to semantic
emptiness, provided the supplied list enumerates exactly the classifier's
globals. Soundness of collapsing a state to #lbot needs only that the test
implies emptiness. The carrier uses both directions. The specification collapses exactly
the empty states, so only an exact test lets the executable collapse commute
with readback. A state the test keeps is then known to be nonempty
(#isaconst("live_resolved_st_q")), and the numeric transfer commutes with
readback only on such states.

The relational order analysis keeps its own state type, a set of variable pairs
(#isatype("relc")), so this section does not apply to it.

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

We do not expect a theorem that discharges the premise for every program,
because we expect termination to fail for some configurations. A terminating
solve visits finitely many unknowns, and whether the space of unknowns is
finite depends on the context policy. Under the unit context the solved unknowns are finite as soon
as their nodes belong to the compiled program
(#isathm("compiled_unit_vars_finite")). Call strings of length at most $k$ over
a compiled program form a finite space (#isathm("compiled_call_strings_finite")),
which bounds the solved unknowns if they lie in it, a hypothesis of
#isathm("compiled_call_string_vars_finite"). An entry-state context is a list of
abstract values at the callee's arity. For Sign and Parity that space is
finite, an argument we have not mechanized. For Interval, Congruence and the
Int product it is not: under entry-state contexts, a recursion that changes its
argument at every level meets a fresh context at every level,
and widening bounds the values of existing unknowns without bounding how many
are created (#fixture(
  "21-context-sensitivity/01-unbounded_context_chain_diverges.vimp",
  label: "01-unbounded_context_chain_diverges",
)). A finite space of unknowns does not force termination either. Without
contexts, the interval recursion `f(x) { f(x + 1) }` entered with $x = 0$
contributes the entries $[0, 0], [0, 1], [0, 2], dots$ to the one seed of `f`,
and under the joining update rules this strictly ascending chain is never
widened (@fig:rules-programs). Neither
divergence is machine-checked. Their regression programs
do not finish within their time limits, and the argument above is why we expect
divergence. A timeout alone would not prove it (@sec:trust-boundary).

The vendored development also offers no restricted theorem to reuse. The
side-effecting solver is proved partially correct only. The vendored
termination theorems cover top-down variants without side effects and assume a
finite type of unknowns @tilscher26. Voblint's unknowns pair a graph node
with a context, and the node type alone is infinite, since a statement node
carries any natural number. This already excludes the case where a restricted theorem would be most
plausible, even Sign under the unit context. The
paper result of Seidl and Vogler (@sec:side-effects) needs only finitely many
encountered unknowns. Mechanizing a result of that kind for the vendored solver, relative to the unknowns a program creates, is
future work. The end-to-end theorem is therefore a partial-correctness result
with a per-program premise (@sec:headline).

The solver thus enters the argument only through the three contracts of
#isalocale("dg_analysis") in @sec:certificate, discharged once for all four
update rules. @ch:results chains them with equation soundness into the
source-level theorem.
