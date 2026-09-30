#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/code.typ": c11, fixture, isaconst, isalocale, isathm, isatype
#import "../lib/sources.typ": thy, update-rule-steps
#import "../lib/math.typ": conc, ctor, ineq, lbot, lle, ltop, sem, setcomp, sh, sol
#import "../lib/theme.typ": vb
#import "../lib/claims.typ": claim-ref, claim-snapshot, claim-text

= Solver Certificates and Executable States <ch:solving>

@ch:equations stopped at post-solutions: every valuation that satisfies the
generated constraints covers the context-indexed collecting semantics
(#isathm("activation_collect_dg_sound")). This chapter connects that theorem
to a run of the executable solver. The solver enters the proof through one
statement about its result, a _certificate_: the valuation it returns is a
post-solution on the finite set of unknowns it evaluated (@sec:certificate).
Every other part of the proof uses only this statement, so the solver's
algorithm and its update rule (@sec:update-rules) can change without touching
it. The solver runs on an executable representation of abstract states, and
@sec:readback shows that this representation computes the same values as the
functions over variable names the analyses are specified with. Termination of
the solve is a premise, checked per program (@sec:termination).

Chaining the two results gives the statement @ch:results builds on: whenever
the executable solver returns for a program, the valuation it returns covers
every store that reaches each solved unknown in its context. The certificate
is the only fact about the solver in this chain. The chapter therefore has two
tasks: to isolate that logical fact (@sec:certificate), and to fix the choices
needed to run the solver, an update rule (@sec:update-rules) and an executable
state representation (@sec:readback), and account for the remaining
termination premise (@sec:termination).

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
single query, the exit of `main` in the root context (#isaconst("root_query")),
evaluates its right-hand side, and solves every unknown that right-hand side
reads, recursively @seidl21 @tilscher26. Starting from the exit of `main`, it
follows the predecessor and call dependencies that the evaluated right-hand
sides expose, in each context the solve discovers, and a terminating solve
reaches finitely many unknowns in total. Apinis et al.
start local solving from the same unknown @apinis12[§3]. @fig:solve-infinite
draws the system of a five-procedure program and marks the part one solve
reaches. Unknowns from which the exit cannot be reached, such as code after a
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
  image("/shared/generated/svg/infinite.svg", width: 70%),
  placement: none,
  caption: [The equation system of a five-procedure program as a grid: rows
    are program points grouped by procedure, columns are contexts, one cell
    per unknown. `main` calls `w` and `f(3)`, `f` calls itself twice and calls
    `g`, and `g` calls `h`; `w` calls itself with an unconstrained value.
    Under entry-state contexts with Interval, the filled cells are the
    unknowns one solve reaches, starting from the ringed query at the exit of
    `main`; hollow cells are read and answer #lbot.
    Dashed arrows are the publications to callee seeds, solid arrows the
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
reads. #isaconst("traverse_rhs", thy: "Basics_side") returns the value of the #ctor("Answer") at
the end of that path, the value the equation computes, and
$#isaconst("eq", thy: "Basics_side") med T med u med sol$ abbreviates
$#isaconst("traverse_rhs", thy: "Basics_side") med (T med u) med sol$.
#isaconst("sides_of_rhs") joins the values of the #ctor("Side") steps on the
path per target, #lbot where the tree publishes nothing.
$#isaconst("dep\<^sub>L") med T med sol med u$ is the set of local unknowns
the path queries.


Written out for the solved set $V$ (`vars`), the certificate requires
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
  + puts the query into the certified set. In the running example the query is
    $(italic("exit")_"main", c_0)$.
  + closes $V$ under reading: every local unknown a certified equation reads is
    itself certified. Which unknowns a right-hand side reads can depend on the
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
  + bounds what each equation publishes, joined per target, at every global
    unknown. It carries a call into its callee, because it makes the callee's
    seed hold every entry value routed there, and global unknowns receive
    their values only through it. It gives the seed inequality #ineq(3) of
    @sec:eq-discharge. In the running example, (C4) at $(italic("pp3"), c_0)$ and at
    $(italic("pp4"), c_0)$ requires
    ${n |-> [5, 5]} lle sol(italic("Seed")(italic("bump"), c_1))$ and
    ${n |-> [4, 4]} lle sol(italic("Seed")(italic("bump"), c_2))$, the entry
    values of `a = bump(5)` and `b = bump(4)` (@sec:eq-example).
]

Among local unknowns the solver widens and narrows only at loop points
(@sec:td, @fig:td-trace), so #sol may lie above the least solution; (C1) to (C4) describe exactly the
post-solution certificate it guarantees (@ch:background). The
collecting-soundness theorem of @ch:equations is stated for any $V$ and #sol
that meet them.

=== From backward to forward closure <sec:cert-forward>

Equation soundness bounds only the unknowns in the certified set $V$. A
concrete execution may visit any node in any admitted context, so the proof
needs $V$ to be closed _forward_: along intraprocedural edges, from a call site
to its continuation, and into the callee's entry under the context the call
selects. The certificate provides the opposite closure. An equation reads its
predecessors, so by (C2) $V$ is closed _backward_ from the query at the exit of
`main`.
Code after a `return` shows why backward closure alone does not suffice: such
an unknown may be solved, yet its successors need not lie on any dependency
path back from the procedure's result.

The fix restricts attention to _live_ unknowns (#isaconst("live_unknowns")): solved unknowns whose node is live in a procedure whose result is solved in the same
context. Liveness (#isaconst("prog_live")) is defined on the program text: a
statement is live if no command before it in its sequence cannot fall through.
The semantic alternative, that the node can still reach its procedure's result,
is not preserved along the edges of an arbitrary graph, and control after a
`return` can run into a node with no way out. The syntactic notion has the two
properties the argument needs. Every live node reaches the procedure's result
along the steps an equation reads backwards, and every edge out of a live node
lands on a live node. A successor of a live unknown therefore reaches a solved
result, and backward closure from that result puts the successor into $V$.

The call case has one more condition. The callee's entry is covered only when
the abstract entry state of the callee is not #ctor("Bot"), because only then does the
solve select a callee context and demand its result. An execution that makes
the call enters with a store that this state describes, so the state is not
#ctor("Bot") in the cases the proof needs. #isathm("live_unknowns_cover")
derives the forward closure from well-formedness and termination alone, so
coverage is not a premise of the final theorem.

=== The solver as a parameter <sec:cert-param>

The solver enters the pipeline in exactly one place. The pipeline locale
#isalocale("dg_analysis") takes the solver as a parameter, together with its
domain predicate and its executable form, and states three contracts about
it; no other part of the development assumes anything about the solver. First, a solve whose recursion is defined
on the query returns a post-solution on its stabilized set. The vendored
theorem #isathm("partial_post_solution") provides this. Second, such a solve returns a finite set of unknowns
(#isathm("finite_stabl_solve"), proved once from the solver's stable-set
invariant). Finiteness lets @ch:results combine the results of the finitely
many contexts solved at a node into one verdict. Third, a run of the executable solver that returns a result lies
in that domain (#isathm("solve_dom_of_solve_c"), @sec:termination). Every
registration of an analysis with the pipeline discharges the three contracts
by citing these facts at its update rule. Domain membership for the program's
query is the termination premise of @sec:termination. The interface is small on purpose:
each contract serves one purpose, soundness of the result, the join
over contexts, and the executable check of the termination premise, and none
refers to how the solver computes. Another solver, for instance one with
local side effects (@sec:outlook-extending), attaches to Voblint by proving
these three facts.

The certificate is what the pipeline hands to the soundness theorem of
@ch:equations. #isathm("routed_analysis_sound_of_live") establishes the locale
#isalocale("routed_analysis_sound"), which joins that theorem with the check
classifier, for a terminating solve, and @tab:cert-premises lists how each of its
premises is met. The certificate itself supplies the inequalities. The solver
certifies the buffered generator of @sec:eq-buffer, which the analyzer runs,
while the soundness theorem speaks about the direct generator.
#isathm("part_post_solution_routed_node_rhs_buffered") carries a certificate
from the one to the other, and #isathm("pp_routed") applies it to the
pipeline's equations.

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    stroke: none,
    table.hline(),
    [*premise of the soundness theorem*], [*met by*],
    table.hline(stroke: 0.5pt),
    [inequalities #ineq(1) to #ineq(5) on $V$], [(C3) and (C4), through #isathm("pp_routed")],
    [program entry, forward closure of $V$], [(C1), (C2) and liveness (@sec:cert-forward)],
    [routing adequacy and totality on $V$], [the context policy (@sec:eq-routing)],
    [finitely many contexts per node], [the finiteness contract],
    table.hline(),
  ),
  placement: none,
  caption: [How a terminating solve meets the premises of
    #isalocale("routed_analysis_sound"), the soundness theorem of
    @sec:eq-discharge together with the check classifier. The first row uses the certificate's value bounds (C3) and (C4), the second its
    query and dependency closure (C1) and (C2), and the last two come from the
    context policy and the solver's finiteness.],
) <tab:cert-premises>

The certificate abstracts from how the solver obtains such a valuation. To run
it, two choices still have to be fixed: how side contributions update global
unknowns (@sec:update-rules), and how abstract states are represented as
executable values (@sec:readback). Neither changes the certificate.

== One proof for four update rules <sec:update-rules>

The solver merges each side contribution into its global unknown, and the
merge affects both precision and termination. In the analyzer each right-hand
side's contributions to one target arrive already joined (@sec:eq-buffer).
Voblint offers several merges
and proves the solver sound for all of them at once (#isathm("update_rule_update_global_of")). A merge is an _update
rule_.
Stemmler et al. proposed such rules @stemmler25[§3–4], and Tilscher et al. formalize a
generic update-rule interface and prove five of them sound against it
@tilscher26. Every rule keeps one record per origin (@sec:td). Most rules store the origin's latest contribution
there; per-origin warrowing stores the old record warrowed with the new
contribution. The rules differ in what they record and in how they form the
new value of the global. Voblint exposes four of them: join the
contribution into the value, join the recorded contributions, warrow the value
toward that join, or warrow the origin's own record and then join the records.
The fifth vendored rule, which bounds narrowing by a counter, is not selectable.
Voblint also proves sound a keyed combination that joins at entry seeds and
warrows elsewhere; only examples use it.
In #isaconst("run_voblint") the entry seeds are the only global unknowns that
receive contributions (@sec:coop-limits). The rule therefore decides how a callee's entry state
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
    origin widens only when A's own contribution grows. A widened bound is set
    bold and marked $nabla$. The cells are read from
    #isathm("update_rules_example"), which evaluates the vendored rules with
    Voblint's interval operators; the contributions separate the rules and come
    from no program.],
) <fig:update-rules>

No solver fact is proved per rule. The datatype #isatype("globals_rule")
names the four rules, #isaconst("update_global_of") selects the vendored
implementation, and one interpretation of the solver locale takes the rule as a
parameter, so every solver fact, the certificate included, holds for all four
at once. Only #isathm("update_rule_update_global_of"), which shows that the
selected function meets the update-rule interface, splits on the rule and cites
the four vendored interpretations.

The update rule fixes how values are combined. The values themselves still need
an executable representation, which @sec:readback supplies.


== Executable abstract states <sec:readback>

The analyses of @ch:domains are specified over abstract states $"Var" -> A$.
For semantics and proofs this is the right representation: lookup is function
application, and the lattice operations are pointwise. It is not a
representation the solver can compute with. After every evaluation the solver
decides whether an unknown changed, and deciding $f = g$ or $f lle g$ for two
such functions means checking $forall x. f(x) = g(x)$ over infinitely many
variable names. The solver also has to compute joins, widenings, narrowings,
lookups and updates. Nipkow and Klein meet the same problem in the abstract
interpreter of Concrete Semantics and solve it by a data refinement
@nipkow14[§13.6]: a state is stored as a default value plus a finite list of
overrides, so two states can differ only at the default and the listed names,
and are compared on those. The carrier works like a default dictionary, a
finite dictionary that answers every missing key with a default, and it
represents a total function exactly. The point of the carrier is not a new
abstraction: it makes the existing one computable.

Nipkow and Klein's interpreter stores one default, #ltop. Their language IMP has
one kind of variable and starts in an arbitrary state, so every unlisted
variable is unconstrained, and unreachability is kept outside the state as
`None`. VIMP separates globals from locals and initializes them as C does:
globals start at zero and the locals of `main` are arbitrary (@sec:vimp-vs-c,
#c11("6.7.9p10")). Voblint's representation therefore keeps one default for
locals and one for globals, next to a list of overrides at _locations_, which
tag a name as local or global (#isatype("resolved_st"), #isatype("location")).
The initial state is $(ltop, 0^sharp, [])$
(#isaconst("initial_resolved_st_q"); for Sign, #isaconst("cinit_sign_st")):
every local is #ltop and every global the abstraction of zero, without listing
the declared globals. The solver starts every unknown at $(lbot, lbot, [])$
(#isaconst("bot_resolved_st_q")). The mixed-flow extension of @sec:mixed-flow also stores
states whose locals are all #lbot: it publishes the global variables of a state
to a shared unknown, and with #lbot locals the publications from several call
sites join without mixing in local values.

Different lists can describe the same state: the order of the overrides does
not matter, and an override equal to its default changes nothing. A _quotient
type_ (@sec:isabelle) makes these descriptions one value. Its elements are the
classes of representations that answer every lookup alike:

#thy("resolved_st_q")

Two elements are therefore equal exactly when they describe the same state, and
the equality is decided by comparing the two defaults and the finitely many
listed locations (#isathm("resolved_st_q_eq_iff")). An operation is defined on the finite representation and
lifted to the quotient once it is shown to give equal results on equal
descriptions.

Such an element is used like a map with `get` and `set`. `get`
(#isaconst("lookup_resolved_st_q")) returns the override of a location, or the
default for its tag if there is none; `set` (#isaconst("update_resolved_st_q"))
records an override. Readback $rho$ (#isaconst("fun_of_resolved_st_q_for")) is
`get` on every variable: it turns a carrier state into the total function on
variable names that the specification uses, looking each name up at the
location the program's classifier gives it.

A carrier state means what its readback means. @sec:nonrel-state concretizes
a function state $sigma$ to the stores whose every variable lies in the
concretization of its value, $sem(sigma) = setcomp(s, forall x. s(x) in conc(sigma(x)))$
(#isaconst("gamma_state")). The carrier's concretization is that set after
readback:
$ gamma_(S) (d) = sem(rho(d)) = setcomp(s, forall x. s(x) in conc("get"(d, ell(x)))), $
where $ell(x)$ is the location the classifier gives $x$. The carrier therefore
adds no new notion of meaning. Downstream semantic arguments use $gamma_(S)$; readback remains the
refinement device that establishes its laws below. The solver never computes
$gamma_(S)$: concretization is needed to prove the carrier sound, and the solver
uses only the executable lattice operations.

The solver needs a lattice of states: bottom to start every unknown, order and
equality to decide whether an unknown changed, join to combine contributions,
and widening and narrowing at loop heads and in the update rules. It is generic
in its value type and asks exactly for these operations
(#isalocale("bounded_semilattice_sup_bot"), #isalocale("warrowing"), and
executable equality for code generation). States of the specification get them
pointwise from the value domain, as $"Var" -> A$ from $A$, and the carrier
instantiates the same classes on #isatype("resolved_st_q") whenever the values
do. @fig:carrier-lattice shows the finite lattice on which the solver then
computes. The solver therefore runs on it unchanged. With more
variables the lattice is the same product, one factor per name.

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
      "⊥e": 0.5,
      "⊥o": 1.5,
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
    let pos(st) = (xpos.at(key(st)) * 0.9, 4 - lvl.at(st.at(0)) - lvl.at(st.at(1)))
    let covers(a, b) = {
      // a is covered by b when one variable moves up one level.
      let up(u, v) = (u == "⊥" and (v == "e" or v == "o")) or ((u == "e" or u == "o") and v == "⊤")
      (a.at(0) == b.at(0) and up(a.at(1), b.at(1))) or (a.at(1) == b.at(1) and up(a.at(0), b.at(0)))
    }
    // The solver start and the initial state, each in its own colour.
    let mark = ("⊥⊥": vb.called, "⊤e": vb.accent)
    diagram(
      spacing: (12.5mm, 11mm),
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
            let conds = cons.map(((v, a)) => $s(#v) mod 2 = #rem.at(a)$)
            if conds.len() == 1 { ${s | #conds.first()}$ } else {
              [${s | #conds.at(0),$ \ $#conds.at(1)}$]
            }
          }
          align(center, text(size: 6.5pt)[(#spell(st.at(0)), #spell(st.at(1)), []) \ #text(
              size: 5.5pt,
              fill: vb.muted,
              den,
            )])
        },
        name: label("cl-" + key(st)),
        stroke: 0.6pt + mark.at(key(st), default: vb.muted),
        fill: if key(st) in mark { mark.at(key(st)).lighten(88%) } else { white },
        corner-radius: 3pt,
        inset: 2.5pt,
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
  caption: [The carrier lattice for one local $x$ and one global $g$ over
    Parity. A node shows its representation (default for locals, default for
    globals, overrides) and, below it, its concretization $gamma_(S) (d)$. Edges
    are the carrier order. Purple is the solver's start $(lbot, lbot, [])$;
    blue is the initial state $(ltop, "even", [])$ (#isaconst("cinit_parity_st")),
    which the quotient also identifies with $(ltop, ltop, [g |-> "even"])$.],
) <fig:carrier-lattice>


The figure shows two different ways in which states can be alike. The
quotient identifies representations that answer every lookup alike, such as
$(ltop, "even", [])$ and $(ltop, ltop, [g |-> "even"])$. Distinct carrier
elements can still denote the same stores: every node with a #lbot component
has $gamma_(S) (d) = emptyset$. The quotient removes redundant representations of the same abstract function;
it does not identify abstract states with equal concrete meaning, so these
nodes stay distinct, and a higher node denotes at least the stores of a lower
one.

Each operation is computed with the value domain's operation on the two
defaults and on each listed location, so under `get` it agrees with the
pointwise operation on functions: for the join,
#isathm("lookup_sup_resolved_st_q") states
$"get"(d union.sq e, l) = "get"(d, l) union.sq "get"(e, l)$, and
#isathm("lookup_bot_resolved_st_q"), #isathm("le_resolved_st_q_iff"),
#isathm("lookup_widen_resolved_st_q") and #isathm("lookup_narrow_resolved_st_q")
state the same for bottom, order, widening and narrowing. Point update is not a lattice
operation; the transfer functions use it for assignments.

Readback proves the executable operations correct; it does not state their
meaning downstream. Each carrier operation commutes with readback,
$ rho("op"_"exec" (d)) = "op"_"abs" (rho(d)), $
and since $gamma_(S) (d) = sem(rho(d))$, the existing soundness facts of
@ch:analysis-interface for the abstract operation transport to the executable
one. The carrier is a change of
representation, not a second abstract domain. The locale #isalocale("dg_analysis_exec")
states the commutation as its readback contract, for the transfer on nonempty
states and for procedure entry. For a certified operation bundle both hold
without a per-domain proof: the abstract and executable steps are derived from
the same operations (#isathm("sound_nonrelational_ops.tf_st_for_commute"),
@sec:instances-supply).

Emptiness, on which `DEAD` rests, is a condition over all names (@ch:domains).
Unlike the lattice operations, it is not decided by the listed overrides
alone: an unlisted variable can make the state empty through its default.
The carrier decides it with a finite test that inspects the local default, the
overrides at the locations the classifier selects, and the declared globals,
enumerated explicitly because a fresh global need not exist.
#isathm("resolved_st_q_is_bot_for_iff") proves the test exact,
$ "is_bot"(d) <==> gamma_(S) (d) = emptyset, $
provided the supplied list enumerates exactly the classifier's globals.

The carrier uses the equivalence in both directions. The specification
collapses exactly the empty states to #lbot, and because the test is exact the
executable collapse commutes with readback. A state the test keeps is nonempty
(#isaconst("live_resolved_st_q")), which is where the numeric transfer
commutes with readback.

The relational order analysis keeps its own state type, a set of variable pairs
(#isatype("relc")), so this section does not apply to it.

The solver can now compute every operation its interface requires on finite
carrier values, with the update rule the analyzer selects. This makes the
solve executable, not terminating: whether the recursive solve returns is the
remaining premise.

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

We expect termination to fail for some configurations. Under the unit context
the solved unknowns are finite (#isathm("compiled_unit_vars_finite")), and
bounded call strings over a compiled program form a finite space
(#isathm("compiled_call_strings_finite")).
Under entry-state contexts with Interval, Congruence or the Int product, a
recursion that changes its argument at every level demands a fresh context at
every level, and widening bounds the values of existing unknowns but not their
number (#fixture(
  "21-context-sensitivity/01-unbounded_context_chain_diverges.vimp",
  label: "01-unbounded_context_chain_diverges",
)). Finitely many unknowns do not suffice either: without contexts, the interval
recursion `f(x) { f(x + 1) }` entered with $x = 0$ contributes
$[0, 0], [0, 1], [0, 2], dots$ to the one seed of `f`, and the joining update
rules never widen this chain (@fig:rules-programs). Both regression programs
exceed their time limits; the arguments above, not the timeouts, are why we
expect divergence, and neither is machine-checked (@sec:trust-boundary).

The vendored termination theorems cover top-down solvers without side effects
over a finite type of unknowns @tilscher26. Voblint's unknowns pair a graph
node, whose type is infinite, with a context, so they apply to no
configuration. Seidl and Vogler's paper result needs only finitely many
encountered unknowns (@sec:side-effects); mechanizing such a result for the
vendored solver is future work. The end-to-end theorem is therefore a
partial-correctness result with a per-program premise, which @ch:results chains
with equation soundness into the source-level theorem (@sec:headline).
