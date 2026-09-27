#import "../lib/code.typ": fixture, isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/math.typ": *
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": definition, theorem

// One row of a registered analyzer run (thesis/shared/claims.toml), found by
// its source location, so a table cell cannot drift from what the CLI prints.
#let claim-row(name, loc) = {
  let rows = read("/shared/generated/" + name + ".txt")
    .split("\n")
    .map(l => l.trim().split(regex("\s{2,}")))
  let row = rows.find(c => c.len() >= 4 and c.at(0) == loc)
  assert(row != none, message: "no row " + loc + " in claim " + name)
  (verdict: row.at(3), state: if row.len() > 4 { row.at(4) } else { "" })
}
#let verdict(name, loc) = raw(claim-row(name, loc).verdict)
#let state(name, loc) = raw(claim-row(name, loc).state)

= Cooperating Analyses <ch:cooperation>

@ch:analysis-interface fixed what one analysis supplies. Some facts need two
analyses: one that knows the fact and one whose transfer can use it. In the
program below both guards hold at the assignment, so $x = y$ and `z` is $1$.

#listing(lang: "c", claim: "coop-eq-both", ```
fun main() {
  x = __voblint_nondet_int();
  y = __voblint_nondet_int();
  if (x <= y) {
    if (y <= x) {
      z = (x == y);
      __voblint_check(z == 1);
    }
  }
}
```)

Interval keeps one range per variable. After the guards both `x` and `y` are
still unbounded, so `x == y` evaluates to $ivl(0, 1)$ and the check stays
#verdict("coop-eq-interval", "16:7") with #state("coop-eq-interval", "16:7").
A relational analysis that records the pairs $x lt.eq y$ and $y lt.eq x$ knows
that $x = y$ but tracks no value of `z`, and it reports
#verdict("coop-eq-order", "16:7") too. Neither analysis can decide the check.
Together they can, but only if Interval's assignment can learn what the
relational analysis knows at that point.

Goblint solves this with its _master control program_ (MCP). The activated
analyses run side by side, each on its own part of one combined state, and a
transfer may ask the other analyses a question through the manager's `ask`
function
(#link("https://github.com/goblint/analyzer/blob/0dc12d355e01b0d374ab0646360a8bab00cad656/src/analyses/mCP.ml")[`mCP.ml`]).
Goblint does not prove anything about these exchanges. A proof has a
modularity problem: if Interval's assignment is proved sound using the
relational analysis's invariant, the two proofs are coupled, every new pair of
analyses needs a new proof, and adding an analysis reopens old ones. This
chapter gives each analysis one proof obligation that does not mention its
partners. It shows that analyses meeting the obligation combine into an
analysis that meets the contract of @sec:sound-core, so @ch:equations applies
to the combination unchanged.

== Questions and answers <sec:coop-queries>

The analyses must agree on what a question means and on what an answer
claims. A _query_ asks for a fact about the stores a state describes. Voblint
has one kind, named after Goblint's: the query #isaconst("EvalInt") $e$ asks which
integers the expression $e$ may evaluate to. Its answer is an abstract value
of the reduced product #isatype("int_dom") of @sec:reduced-product, lifted by a
top element that claims nothing (#isatype("query_lift")). Goblint answers its
query in the same lifted product. A comparison evaluates to $0$ or $1$, so
the exact answer $1$ to #isaconst("EvalInt") $(x == y)$ says that $x = y$.

#definition(name: [Truth of an answer], isa: "eval_holds", cmd: "fun")[
  An answer $a$ to #isaconst("EvalInt") $e$ _holds_ at a store $s$ if
  $sem(e)_e s in conc(a)$. A function $A$ from queries to answers is a
  _channel_, and it holds at $s$ if every answer it gives holds at $s$
  (#isaconst("query_algebra.oracle_holds")).
]

Two laws make answers from several analyses usable
(#isalocale("query_algebra")). The top answer holds at every store, so an
analysis that does not understand a question declines it with $ltop$. If two
answers hold at a store, so does their meet, so the answers of all analyses
can be combined into one. Goblint's `MCP.query'` also meets the answers of
all analyses and answers a query cycle with top.

Checks use the same channel. A domain answers #isaconst("EvalInt") $c$ for a
comparison $c$ with its check query from @sec:queries: a definite answer
becomes the exact integer $1$ or $0$, and an undecided one becomes
$ivl(0, 1)$ (#isaconst("abstract_check_domain.eval_answer")). A check is
decided from the meet of the answers of all active analyses
(#isaconst("answer_check")), as Goblint's `assert` analysis reads the answer
to its value query. With one analysis this gives the verdicts of
@sec:queries again (#isathm("abstract_check_domain.classify_eval_answer")).

== One obligation per operation, against every sound channel <sec:coop-oracle>

A transfer that asks cannot be proved against a particular partner without
coupling the proofs. Voblint proves it against any channel that holds. Each
operation receives the answers as an argument $A$ and must be sound for every
$A$, assuming only that $A$ holds at the stores it is applied to. For an edge
with action $a$ and a state $x$ with concretization $conc(x)$, the obligation
is

$
  #isaconst("edge_collect") thin (a, conc(x) inter setcomp(s, A "holds at" s))
  subset.eq conc("step"(A, a, x)).
$

The intersection is what makes this work. The transfer may use an answer only
for the stores the answer is true of. The framework will supply a channel that
holds at every store of $conc(x)$, so the intersection removes nothing at run
time. The proof never needs to know who produced the answers.

The idea is not new. Verasco's numerical domains communicate through
_channels_, records of query functions with a concretization that holds at an
environment when every answer is valid there, and each transfer function is
proved under the hypothesis that the channels it receives are correct
@jourdan15[§7]. Voblint adopts this form of obligation for Goblint's query
mechanism. The differences are in what surrounds it: queries ask about the
predecessor state as in Goblint, a handler may ask in turn
(@sec:coop-channel), and the obligations cover calls, returns and the routed
equations of @ch:equations.

An analysis in this form is an _MCP component_ (#isatype("mcp_component")),
with five operations, each receiving a channel (@tab:mcp-component). The
handler answers queries about a state. The step runs an edge. Entry returns the
pairs of @sec:calls. The return has Goblint's two stages, and both also receive
the callee's channel, which describes the stores at the callee's exit. Goblint's
two return functions receive the callee's `ask` function as an extra argument
in the same way.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, center, left),
    stroke: none,
    table.hline(),
    [*operation*], [*Goblint*], [*answers it receives*],
    table.hline(stroke: 0.5pt),
    [#isaconst("mc_qry")], [`query`], [the channel of the state it answers for],
    [#isaconst("mc_step")], [edge transfers], [the channel of the predecessor state],
    [#isaconst("mc_en")], [`enter`], [the channel of the caller state],
    [#isaconst("mc_comb_env")], [first return stage], [the caller's and the callee's channel],
    [#isaconst("mc_comb_assign")], [second return stage], [the callee's channel],
    table.hline(),
  ),
  placement: auto,
  caption: [The operations of an MCP component. Each receives the answers
    as an argument; the framework, not the component, decides where they
    come from.],
) <tab:mcp-component>

#definition(name: [Sound component], isa: "mcp_component_sound", cmd: "definition")[
  A component $c$ is sound for a concretization $conc$ if $conc$ is monotone
  and, for every channel that holds at the stores involved, the step satisfies
  the inclusion above, some entry pair covers the caller and the entered
  store (@sec:calls), the composed return covers #isaconst("combine_collect"),
  and every answer of the handler holds at every store of $conc(x)$.
]

#thy("mcp_component_sound")

The obligation matches #oblig("INTRA"), paired entry coverage and
#oblig("RETURN") of @ch:analysis-interface, each weakened by the assumption
that the channel holds. The handler obligation is new. It is the analysis's
promise to its partners, and it is the only one the partners rely on.

Two transfers from the development show the shape. The wrapper
#isaconst("ask_assign") lets any component use the channel at an assignment
$x := e$: it asks #isaconst("EvalInt") $e$, and when the answer is one integer
$n$, it runs the component's own assignment of the literal $n$. Since the
answer holds, $e$ evaluates to $n$ at every store the proof considers, so the
component's soundness for the literal gives soundness for $e$. One theorem
covers every component (#isathm("ask_assign_sound")). The order analysis goes
the other way (#isaconst("rel_learn")). At $x := e$ it asks, for each
candidate $y$, whether $e lt.eq y$ and whether $y lt.eq e$, and records the
pairs the answer $1$ confirms (#isathm("rel_learn_sound")).

== Closing the channel <sec:coop-channel>

The framework must supply the channel a component's operations receive. A
handler may itself ask: the combined handler asks every component, and a
component's answer may depend on another's. The channel is therefore defined
by recursion. #isaconst("ask_rec") answers a query $q$ at state $x$ by running
the handler under a channel that remembers $q$ as being asked. A query already
being asked answers $ltop$, as in `MCP.query'`. Since queries range over an
infinite type, cycle detection alone does not bound the recursion, so a depth
bound (#isaconst("query_depth")) aborts the generated program when it is
exhausted. Logically the aborted branch returns $ltop$, so the bound does not
affect soundness.

#theorem(name: [The closed channel holds], isa: "mc_channel_sound")[
  If $c$ is sound for $conc$ and $s in conc(x)$, then the channel
  #isaconst("mc_channel") $c$ $x$ holds at $s$.
]

The proof is an induction on the depth (#isathm("ask_rec_sound")). At depth
$0$ every answer is $ltop$. At depth $n + 1$ the handler runs under the depth
$n$ channel, which holds by induction, so the handler obligation makes its
answer hold. The channel is a function of the state $x$ the operation starts
from, so its answers describe the predecessor state, as in Goblint. That is
also why the theorem discharges the assumption of the step obligation: the
stores in $conc(x)$ are those at which the closed channel holds.

The closed channel turns a component into a specification of
@ch:analysis-interface. #isaconst("component_spec") runs every operation with
the channel of the state it is applied to, and
#isathm("component_contract") proves the analysis soundness contract
#isalocale("analysis_contract") from #isaconst("mcp_component_sound"). The
record #isatype("dg_spec") has a matching field #isaconst("dgs_query") for a
handler that may read globals, and the generator installs it through the same
recursion (#isaconst("ask_with")). The components below do not use globals.

== Many analyses over one state <sec:coop-mcp>

The activated analyses must run in one solve, since each needs the other's
facts at the same program point and context. The combined state is a record
with one field per analysis under one reachability lift. A _lens_, a pair of a
getter and a setter for one field, runs a component on its field and writes
back only that field (#isaconst("lens_of")). Goblint's MCP hands each
analysis its own part of the combined state in the same way. A lens preserves soundness
(#isathm("lens_of_sound")), and it makes the component a _frame_ for every
other field: none of its operations changes what another field describes
(#isaconst("mcp_frame"), #isathm("lens_of_frame")). A list of components is
_independent_ when each is a frame for every other one's concretization
(#isaconst("mcp_independent")). Components on distinct fields are independent
(#isathm("mcp_independent_map")).

#isaconst("mcp_combine") builds one component from a list. The step runs the
components in turn. Entry threads the list of pairs through the components.
The return runs each component's two stages in turn. The handler meets the
answers of all components. The concretization is the intersection of the
components' concretizations (#isaconst("mcp_gamma")). A single component is its
own combination, so one analysis and an MCP of one analysis are the same
specification.

#proved("mcp_combine_sound", note: [Soundness of the combination.])

The proof is an induction over the list. A component covers the concrete
successors in its own concretization. The components after it are frames for
that concretization, so they do not destroy the fact. Every component is given
the same channel, and the theorem is stated for every channel that holds, so
the proof never inspects which component answered what. Because only frames
are used, the order of the fold does not matter for soundness. Goblint runs
every analysis on the predecessor's part of the state, which for components on
separate fields is the same computation.

One design choice needs the independence of whole returns. Running every
component's first return stage before any second stage would require the
stages of different components to commute, which independence of
concretizations does not give. The combination therefore runs both stages of
one component before the next. The first stage of the combination does the
whole return, and its second stage returns what it is given.

The combined state becomes unreachable as soon as one active field is, as
Goblint's MCP raises `Deadcode` when one analysis does. The normalization
#isaconst("mcp_norm") keeps the concretization, because an empty field already
empties the intersection, and #isathm("map_component_sound") carries soundness
across it. #isathm("mcp_contract") then gives the analysis soundness contract
for the combination. @ch:equations consumes that contract and does not need to
know how many analyses produced it.

== What a new analysis has to prove <sec:coop-catalogue>

The obligations of a new analysis are now a fixed list, and none of them
mentions another analysis. @tab:mcp-catalogue lists them next to what the
framework proves once.

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    stroke: none,
    table.hline(),
    [*the analysis proves*], [*the framework derives*],
    table.hline(stroke: 0.5pt),
    [carrier: join semilattice with $lbot$, widening, narrowing],
    [independence of fields (@sec:coop-mcp)],
    [$conc$ monotone], [soundness of the combination],
    [each step, under any channel that holds], [the closed channel holds],
    [paired entry coverage, under any channel that holds], [the analysis soundness contract],
    [the composed return, under both channels], [coverage for every context policy (@ch:equations)],
    [the handler's answers hold], [the solved result and the verdicts (@ch:results)],
    table.hline(),
  ),
  placement: auto,
  caption: [The obligations of an analysis that joins the combined state,
    and what the framework proves once from them. The left column is
    #isaconst("mcp_component_sound"); the right column holds for every list of
    distinct analyses whose components satisfy it.],
) <tab:mcp-catalogue>

The routed pipeline of @ch:equations asks for one more property of the
component it runs: entry answers a single alternative whose resume value is
the caller's state (#isaconst("single_entry")). Lenses, combination and
normalization preserve it, so it too is proved once per analysis.

The order analysis shows the size of such an addition. Its state is a set of
pairs $(x, y)$ with $x lt.eq y$ (#isatype("relc")). It answers comparisons
between variables it has ordered (#isathm("rel_qry_sound")), learns pairs at
assignments by asking, and enters and returns with no facts. It proves its
obligations in #isathm("rel_local_component"). #isathm("order_component_sound")
lifts the result to a component, and the generated registration of
@ch:executable puts it into the combined state. No theorem of the framework
changed. For the executed numeric analyses, #isaconst("exec_component")
presents the executable analysis of @sec:whole-state as a component, and a
handler that answers from the field's readback replaces its own
(#isathm("with_qry_sound")). Every numeric analysis therefore answers
#isaconst("EvalInt") and asks at assignments through #isaconst("ask_assign").

The check at the start of this chapter is decided by the combination.
Interval's assignment asks #isaconst("EvalInt") $(x == y)$, the order analysis
answers $1$, and Interval assigns $ivl(1, 1)$: the run reports
#verdict("coop-eq-both", "16:7") with #state("coop-eq-both", "16:7"). The
exchange also works the other way.

#listing(lang: "c", claim: "coop-le-both", ```
fun main() {
  c = __voblint_nondet_int();
  if (0 < c) {
    x = 0;
    y = 10;
  } else {
    x = 20;
    y = 30;
  }
  __voblint_check(x <= y);
}
```)

Interval joins the branches to #state("coop-le-interval", "21:3") and reports
#verdict("coop-le-interval", "21:3"). The order analysis alone cannot compare a
variable with a constant and reports #verdict("coop-le-order", "21:3").
Together, the order analysis asks at `y = 10` and `y = 30` how the new value
compares with `x`, Interval answers $x lt.eq y$ with $1$ on both branches, and
the pair survives the join: #verdict("coop-le-both", "21:3"). Both runs are
also proved by evaluation of #isaconst("run_voblint")
(#isathm("coop_demo_needs_both"), #isathm("order_asks_needs_both")).

== What the combination leaves out <sec:coop-limits>

A component is a pure function of its state and its channels. It neither reads
nor publishes globals, so an analysis that needs its own global unknowns runs
as a specification of its own and cannot join the combined state; Goblint tags
each analysis's globals with its index instead. The second return stage
receives only the callee's channel. Goblint's second stage asks about the
state its first stage produced, which describes no concrete store here, because
soundness is stated only for the composed return. There is one query kind, and
no answer is cached; Goblint caches answers per transfer, which changes only
how often a handler runs. The order analysis is coarse at calls: it enters and
returns with no facts
(#fixture("25-cooperation/known-imprecision/04-order_forgotten_at_return.vimp", label: "04-order_forgotten_at_return")).
Finally, no theorem says that the combination is more precise than its parts.
The two runs above are precision witnesses for one program each
(@sec:eval-rq4).
