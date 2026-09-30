#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/code.typ": c11, fixture, isaconst, isalocale, isathm, isatype
#import "../lib/sources.typ": thy, update-rule-steps
#import "../lib/math.typ": conc, ctor, ineq, lbot, lle, ltop, sem, setcomp, sh, sol
#import "../lib/theme.typ": vb
#import "../lib/claims.typ": claim-ref, claim-snapshot, claim-text

= Solver Certificates and Executable States <ch:solving>

@ch:equations stopped at post-solutions: a valuation that satisfies the
generated constraints on a suitably closed set of unknowns covers the
context-indexed collecting semantics (#isathm("activation_collect_dg_sound")).
This chapter connects that theorem to a run of the executable solver. The
solver enters the proof through three facts about its result (@sec:cert-param).
The main one is a _certificate_: the valuation it returns is a post-solution on
the set of unknowns it evaluated (@sec:certificate). The other two state that
this set is finite and that a finished run of the executable solver lies in the
domain on which the certificate holds. The proof uses nothing else about the
solver, so its algorithm and its update rule (@sec:update-rules) can change
without touching the proof. The solver runs on an executable representation of
abstract states, and @sec:represented-function shows that this representation computes the
same values as the functions over variable names the analyses are specified
with. Termination of the solve is a premise, checked per program
(@sec:termination).

Chaining the two results gives the statement @ch:results builds on: whenever
the executable solver returns for a program, the valuation it returns covers
every store that reaches each solved unknown in its context. The chapter
isolates the certificate (@sec:certificate), fixes the two choices needed to
run the solver, an update rule (@sec:update-rules) and an executable state
representation (@sec:represented-function), and accounts for the remaining termination
premise (@sec:termination).

== The certificate between solver and semantics <sec:certificate>

=== What a solve computes <sec:cert-solve>

Voblint solves the equations with the side-effecting top-down solver of
Tilscher et al., which is proved partially correct @tilscher26. Side effects
are how a call reaches its callee: the caller publishes the entry value to the
callee's seed, and the callee's entry equation reads the seed back
(@sec:eq-call). The solver returns a valuation #sol together with the set $V$
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
  placement: none,
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
  + puts the query into the solved set. In the running example the query is
    $(italic("exit")_"main", c_0)$.
  + closes $V$ under reading: every local unknown that the equation of a solved
    unknown reads is itself solved. Which unknowns a right-hand side reads can depend on the
    values it reads (@sec:eq-trees), so the dependencies are taken under the
    final valuation. In the running example $V$ holds the #_local-unknowns local
    unknowns the solve of @sec:eq-example reached, and the tree of
    $(italic("pp3"), c_0)$ reads $(italic("pp2"), c_0)$ and, in the context
    $c_1$ it computes from that value, $(italic("exit")_"bump", c_1)$; both
    lie in $V$.
  + is the post-solution inequality of @ch:background for local unknowns: the
    value #sol stores at $u$ is at least what the right-hand side of $u$
    computes from the values #sol stores for the unknowns it reads. That
    right-hand side joins everything that reaches $u$: the initial state, the
    transfer along each incoming edge, the seed read at a callee entry and each
    call's combined result. So $sol(u)$ over-approximates each of them; these
    are the inequalities #ineq(1), #ineq(2), #ineq(4) and #ineq(5) of
    @sec:eq-discharge. In the running example, (C3) at $(italic("pp3"), c_0)$
    requires $sh("combine")(q_1, sol(italic("exit")_"bump", c_1)) lle
    sol(italic("pp3"), c_0)$, the value with $a = [6, 6]$.
  + carries a call into its callee: it makes the callee's seed hold every
    entry value routed there, and global unknowns receive their values only
    through it. It gives the seed inequality #ineq(3) of
    @sec:eq-discharge. In the running example, (C4) at $(italic("pp3"), c_0)$ and at
    $(italic("pp4"), c_0)$ requires
    ${n |-> [5, 5]} lle sol(ctor("Activation_Seed") thin italic("bump") space c_1)$ and
    ${n |-> [4, 4]} lle sol(ctor("Activation_Seed") thin italic("bump") space c_2)$, the entry
    values of `a = bump(5)` and `b = bump(4)` (@sec:eq-example).
]

Among local unknowns the solver widens and narrows only at loop points
(@sec:td, @fig:td-trace). The returned #sol may therefore lie above the least
solution, and (C1) to (C4) state all the solver guarantees about it. The
collecting-soundness theorem of @ch:equations needs the bounds (C3) and (C4)
on a set $V$ that is closed forward and contains the program entry, together
with premises on entry and routing. @sec:cert-forward obtains such a set from
(C1) and (C2) by restricting $V$ to its live unknowns.

=== From backward to forward closure <sec:cert-forward>

Equation soundness bounds only the unknowns in the solved set $V$. A
concrete execution may visit any node in any admitted context, so the proof
needs $V$ to be closed _forward_: along intraprocedural edges, from a call site
to its continuation, and into the callee's entry under the context the call
selects. The certificate provides the opposite closure. An equation reads its
predecessors, so by (C2) $V$ is closed _backward_ from the query at the result node
of `main`.
Code after a `return` shows why backward closure alone does not suffice: such
an unknown may be solved, yet its successors need not lie on any dependency
path back from the procedure's result.

The fix restricts attention to _live_ unknowns
(#isaconst("dg_analysis.live_unknowns", thy: "DG_Live_Unknowns", display: "live_unknowns")): solved unknowns whose
node is live in a procedure whose result is solved in the same context.
Liveness (#isaconst("prog_live")) is defined on the program text: a statement
is live if every command before it in its sequence can fall through to the
next, as a `return` cannot. This syntactic notion has the two properties the
argument needs. Every live node reaches the procedure's result
along the steps an equation reads backwards, and every edge out of a live node
lands on a live node. A successor of a live unknown therefore reaches a solved
result, and backward closure from that result puts the successor into $V$.

The call case has one more condition. The callee's entry is covered only when
the abstract entry state of the callee is not #ctor("Bot"), because only then does the
solve select a callee context and demand its result. An execution that makes
the call enters with a store that this state describes, so the state is not
#ctor("Bot") in the cases the proof needs.
#isathm("dg_analysis.live_unknowns_cover", thy: "DG_Live_Unknowns", display: "live_unknowns_cover")
derives the forward closure from well-formedness and termination alone, so
coverage is not a premise of the final theorem.

=== The solver as a parameter <sec:cert-param>

The analysis locale #isalocale("dg_analysis") takes the solver as a
parameter, together with its domain predicate, the arguments on which its
recursion terminates (@sec:termination), and its executable form. It extends
the locale #isalocale("certified_solver"), which states three contracts about
them. First, a solve whose recursion is defined on the query returns a
post-solution on the set of unknowns it solved; the vendored theorem
#isathm("TD_side_upd_rule.partial_post_solution", thy: "TD_side_upd_rule") provides this.
Second, such a solve returns a finite set of unknowns
(#isathm("finite_stabl_solve"), proved once from the solver's stable-set
invariant). Finiteness lets @ch:results combine the results of the finitely
many contexts solved at a node into one verdict. Third, a run of the
executable solver that returns a result lies in that domain
(#isathm("solve_dom_of_solve_c")). #isathm("td_certified_solver") composes
these facts into one interpretation of #isalocale("certified_solver") for the
vendored solver at every update rule, and every registration of an analysis
with #isalocale("dg_analysis") cites it. Domain membership for the program's query is the
termination premise of @sec:termination. None of the contracts refers to how
the solver computes. Another solver, for instance one with local side effects
(@sec:outlook-extending), attaches to Voblint by interpreting
#isalocale("certified_solver").

The certificate is what the analysis locale hands to the soundness theorem of
@ch:equations. For a terminating solve,
#isathm(
  "dg_analysis.routed_analysis_from_live_unknowns",
  thy: "DG_Live_Unknowns",
  display: "routed_analysis_from_live_unknowns",
)
establishes the locale #isalocale("routed_analysis"), which joins that
theorem with the _check classifier_, the function that turns the abstract state
at a check into a verdict (@sec:verdicts). It takes as $V$ the live unknowns of
@sec:cert-forward, a subset of the solved set. @tab:cert-premises lists how the
premises that depend on the solve are met. The certificate supplies the
inequalities: #isathm("post_bounded_of_part_post_solution") keeps its bounds
(C3) and (C4) without the closure (C2), and the bounds restrict to any subset
that contains the query. The solver certifies the buffered generator of
@sec:eq-buffer, which the analyzer runs, while the soundness theorem speaks
about the direct generator. #isathm("part_post_solution_routed_node_rhs_buffered")
carries a certificate from the one to the other, and
#isathm("dg_analysis.pp_routed", thy: "DG_Analysis", display: "pp_routed") applies it to the analysis locale's
equations.

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
    [program entry, forward closure of $V$], [(C1), (C2) and liveness (@sec:cert-forward)],
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
certificate: how side contributions update global unknowns
(@sec:update-rules), and how abstract states are represented as executable
values (@sec:represented-function).

== One proof for five update rules <sec:update-rules>

The solver merges each side contribution into its global unknown, and the
merge affects both precision and termination. In the analyzer each right-hand
side's contributions to one target arrive already joined (@sec:eq-buffer). A
merge is an _update rule_. Stemmler et al. proposed such rules
@stemmler25[§3–4], and Tilscher et al. formalize a generic update-rule
interface and prove five of them sound against it @tilscher26. Every rule
keeps one record per origin (@sec:td), and Voblint exposes all five. They join
the contribution into the value, join the recorded contributions, warrow the
value toward that join, or warrow the origin's own record and then join the
records. The fifth, bounded narrowing, warrows the origin's record as the
fourth does but also counts how often that origin has switched from widening
to narrowing. Once the count has reached a bound, a record in its narrowing
phase ignores contributions below it, so each switch narrows only once. The first three rules record the origin's latest
contribution; the two per-origin warrowing rules record the old record warrowed
with the new contribution. Each rule meets the vendored interface
(#isathm("update_rule_update_global_of")), so the solver is sound for all of
them at once. In #isaconst("run_voblint") the entry seeds are the
only global unknowns that receive contributions (@sec:coop-limits). The rule
therefore decides how a callee's entry state accumulates across call sites
(@fig:update-rules).

Per-origin warrowing helps when several origins feed one global, as Seidl et
al. show on a global that receives one constant per location @seidl26[§1]. A
recursive call that feeds its own seed is a single origin. Distinguishing
contributions by origin gains nothing when the recursive call is the only
origin, and the rule can lose precision, as on the shrinking recursion of
@fig:rules-programs (@sec:eval-rq4).

The choice of rule also affects termination. The two joining rules never widen
a seed, so a recursion that enters with a growing argument can keep the solve
running (@sec:termination), while the three warrowing rules widen the entry seed.
No rule is more precise on every program. On the growing recursion of
@fig:rules-programs only the warrowing rules answer, and each warrowing rule
loses precision on a program that the joining rules solve exactly.

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

No solver fact is proved per rule. The datatype #isatype("globals_rule")
names the five rules, #isaconst("update_global_of") selects the vendored
implementation, and one interpretation of the solver locale takes the rule as a
parameter, so every solver fact, the certificate included, holds for all five
at once. The solver runs on the state of bounded narrowing, which keeps the
counters beside the recorded contributions, and #isaconst("lift_basic_rule")
runs each of the other four rules on the contributions alone. Only
#isathm("update_rule_update_global_of"), which shows that the selected function
meets the update-rule interface, splits on the rule and cites the five vendored
interpretations.

The update rule fixes how values are combined. The values themselves still need
an executable representation, which @sec:represented-function supplies.


== Executable abstract states <sec:represented-function>

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
type of its abstract values (@ch:background). It works like a default dictionary, a finite dictionary that
answers every missing key with a default, and it represents a total function
exactly. It makes the existing abstraction computable and adds no new one.

Voblint's carrier keeps one default dictionary per partition: a local
dictionary for the names the program treats as local and a global dictionary
for the globals. Each dictionary is a default value paired with a finite list
of overrides, pairs of a name and its value (#isatype("default_dict")), and a
carrier state is the pair of the two, local first (#isatype("default_st_rep")).
Isabelle writes the state with local dictionary $(d_l, "ls")$ and global
dictionary $(d_g, "gs")$ as $⟪(d_l, "ls"), (d_g, "gs")⟫$
(#isaconst("default_st_mk")), and so do we. A map over a fixed #ltop cannot
express two states the analysis needs. VIMP initializes variables as C does:
globals start at zero and the locals of `main` are arbitrary (@sec:vimp-vs-c,
#c11("6.7.9p10")). The initial state is $⟪(ltop, []), (0^sharp, [])⟫$
(#isaconst("initial_default_st"); for Sign, #isaconst("cinit_sign_st")),
where $0^sharp$ is the domain's abstract value of the constant $0$: every local
is #ltop and every global $0^sharp$, without listing the declared globals. The
solver's lattice interface also asks for a least element, here
$⟪(lbot, []), (lbot, [])⟫$ (#isaconst("bot_default_st")), and the mixed-flow
extension of @sec:mixed-flow stores states whose locals are all #lbot. In
#isaconst("run_voblint") the solver's values are lifted states, which start at
#ctor("Bot") below every carrier state.

Different pairs of dictionaries can describe the same state: overrides of
distinct names may appear in any order, and an override equal to its default
changes nothing. A _quotient type_ (@sec:isabelle) makes these descriptions one
value. Its elements are the classes of representations that answer every lookup
alike:

#thy("default_st")

Two elements are therefore equal exactly when every lookup agrees
(#isathm("default_st_eq_iff")). A finite test decides this.
#isathm("le_default_st_rep_code_raw_iff") shows that comparing the two defaults and
the finitely many listed names of each dictionary decides the order, and the executable
equality (#isaconst("equal_default_st")) tests the order in both
directions. An operation is defined on the finite representation and lifted to
the quotient once it is shown to give equal results on equal descriptions.

Such an element is used like a map. Lookup and update take a _location_, a
name tagged as local or global (#isatype("location")). The lookup $d⟨l⟩$
(#isaconst("default_st_get")) reads the dictionary of the partition $l$ names:
the override of its name, or that dictionary's default if there is none. The
update $d⟨l := a⟩$ (#isaconst("default_st_set")) records an override in the
same dictionary. The function a state represents, $rho_(cal(G))(d)$
(#isaconst("default_st_to_fun")), is lookup on every variable: the total
function on variable names that the specification uses. It looks each name $x$ up at its location $ell(x)$, the
local or global location that the program's global-variable classifier
$cal(G)$ (@sec:pstep) assigns to $x$.

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

The solver can now compute every operation its interface requires on finite
carrier values, with the update rule the analyzer selects. The solve is thus
executable; whether the recursive solve returns is the remaining premise.

== Why termination stays a premise <sec:termination>

In a proof assistant termination is a question of the logic itself. HOL is a
logic of total functions, so a recursive definition is admitted only when its
recursion terminates; otherwise one could define $f(n) = f(n) + 1$ and derive
$0 = 1$ @nipkow14[§2.3.4]. The vendored solver's termination is not known in
general, so Isabelle defines it with a domain predicate
(#isaconst("solve_dom", thy: "TD_side_upd_rule")), the arguments on which
the recursion is well founded, and the certificate of @sec:certificate holds on
that domain. Outside it the solver still denotes some unspecified value, so the
premise #isaconst("config_terminates") asks for domain membership of the
program's query, not for an answer. The generated code runs the executable
form of the solver, which returns only when the recursion finishes, and
#isathm("solve_dom_of_solve_c") turns a finished run into domain membership.
Evaluating the solve for one program therefore discharges the premise.

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
interval recursion `f(x) { f(x + 1) }` entered with $x = 0$ contributes
$[0, 0], [0, 1], [0, 2], dots$ to the one seed of `f`, and the joining update
rules never widen this chain (#fixture(
  "24-site-figures/01-recursion_grows_join_diverges.vimp",
  label: "01-recursion_grows_join_diverges",
), @fig:rules-programs). Both regression programs exceed their time limits;
the arguments above, not the timeouts, are why we expect divergence, and
neither is machine-checked (@sec:trust-boundary).

The vendored termination theorems cover top-down solvers without side effects
over a finite type of unknowns @tilscher26. They further require monotone
right-hand sides and the ascending chain condition for plain TD, well-founded
widening chains for TD with widening, and monotone right-hand sides with
well-founded widening and narrowing chains for TD with warrowing. Voblint's
unknowns pair a graph node, whose type is infinite, with a context, so these
theorems apply to no configuration. Seidl and Vogler prove on paper that
their side-effecting solver terminates on every system as long as only
finitely many unknowns are encountered @seidl21[§9, Thm. 5], for widening and
narrowing operators whose iterations always stabilize @seidl21[§3]. That solver
joins a side effect into its target until one origin increases the target a
second time, and from then on widens there @seidl21[§9]. The joining update
rules never widen, so the result does not carry over to them, as the growing
recursion above shows. Mechanizing such a result for the vendored solver is
future work. The end-to-end theorem is therefore a
partial-correctness result with a per-program premise, which @ch:results chains
with equation soundness into the source-level theorem (@sec:headline).
