#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": fixture, isaconst, isalocale, isathm, isatype, listing, oblig
#import "../lib/math.typ": *
#import "../lib/sources.typ": proved
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

= How Analyses Cooperate <ch:cooperation>

@ch:analysis-interface fixed what one analysis supplies: a local
specification whose operations are proved sound one by one. Some facts need two
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

Goblint solves this with its
#link(
  "https://github.com/goblint/analyzer/blob/0dc12d355e01b0d374ab0646360a8bab00cad656/src/analyses/mCP.ml",
)[_master control program_]
(MCP). The activated
analyses run side by side, each on its own part of one combined state, and a
transfer may ask the other analyses a question through the manager's `ask`
function.
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
$ivl(0, 1)$ (#isaconst("sound_check_query.eval_answer")). A check is
decided from the meet of the answers of all active analyses
(#isaconst("mcp_answer")): #isaconst("mcp_classify") reads the verdict off
that answer with #isaconst("answer_check"), as Goblint's `assert` analysis
reads the answer to its value query. With one analysis this gives the verdicts of
@sec:queries again (#isathm("sound_check_query.classify_eval_answer")).

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

The idea is not new. In Astrée a domain asks the others for constraints
through an input channel, and an abstract transfer need only be sound for
arguments that also satisfy the channel's constraints @cousot07astree[§§5.3, 6].
Verasco's numerical domains communicate through
_channels_, records of query functions with a concretization that holds at an
environment when every answer is valid there, and each transfer function is
proved under the hypothesis that the channels it receives are correct
@jourdan15[§7]. Voblint adopts this form of obligation for Goblint's query
mechanism. The differences are in what surrounds it: queries ask about the
predecessor state as in Goblint, a handler may ask in turn
(@sec:coop-channel), and the obligations cover calls, returns and the routed
equations of @ch:equations.

The local specification of @sec:sound-core (#isatype("local_spec")) has
this form: every operation receives a channel as an argument
(@tab:local-spec). The handler #isaconst("ls_query") answers queries about a
state. Seven fields, #isaconst("ls_skip") to #isaconst("ls_event"), hold one
transfer per kind of edge, as Goblint's `Spec` has `assign`, `branch`,
`return` and the others, and the step #isaconst("ls_step") on an arbitrary
edge is derived from them. Entry returns the pairs of @sec:calls. The return
has Goblint's two stages, and both also receive the callee's channel, which
describes the stores at the callee's exit. Goblint's two return functions
receive the callee's `ask` function as an extra argument in the same way. We
call a local specification that runs inside the combined state of
@sec:coop-mcp a _component_.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, center, center),
    stroke: none,
    table.hline(),
    [*field*], [*Goblint*], [*channels it receives*],
    table.hline(stroke: 0.5pt),
    [#isaconst("ls_query")], [`query`], [the state's own],
    [#isaconst("ls_skip") to #isaconst("ls_event")], [edge transfers], [the predecessor's],
    [#isaconst("ls_enter")], [`enter`], [the caller's],
    [#isaconst("ls_combine_env")], [first return stage], [the caller's and the callee's],
    [#isaconst("ls_combine_assign")], [second return stage], [the callee's],
    table.hline(),
  ),
  placement: auto,
  caption: [The fields of a local specification and the channels each
    receives. The framework, not the analysis, decides where the answers come
    from.],
) <tab:local-spec>

The soundness predicate #isaconst("sound_local_spec") is one law per field
(#isathm("sound_local_spec_iff")), with the two return stages sharing one law
for their composition. Each law is quantified over every channel that holds at
the stores involved: the caller's store for a step, an entry, a query and the
first return stage, and the callee's exit store for the callee's channel. The
seven edge laws together are the inclusion displayed above. The laws match
#oblig("INTRA"), entry coverage and #oblig("RETURN") of
@ch:analysis-interface, each weakened by the assumption that the channel holds.
The handler law says that every answer holds at every store of $conc(x)$. It
is the analysis's promise to its partners, and it is the only law the partners
rely on.

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

#theorem(name: [The closed channel holds], isa: "ls_channel_sound")[
  If $c$ is sound for $conc$ and $s in conc(x)$, then the channel
  #isaconst("ls_channel") $c$ $x$ holds at $s$.
]

The proof is an induction on the depth (#isathm("ask_rec_sound")). At depth
$0$ every answer is $ltop$. At depth $n + 1$ the handler runs under the depth
$n$ channel, which holds by induction, so the handler obligation makes its
answer hold. The channel is a function of the state $x$ the operation starts
from, so its answers describe the predecessor state, as in Goblint. That is
also why the theorem discharges the assumption of the step obligation: the
stores in $conc(x)$ are those at which the closed channel holds.

This theorem is what #isaconst("dg_spec_of") of @sec:sound-core relies on. It
runs every operation of a local specification with the closed channel of the
state it is applied to, so the channel hypotheses of the laws hold, and
#isathm("dg_spec_of_contract") obtains the analysis soundness contract
#isalocale("analysis_contract") from #isaconst("sound_local_spec"). The
record #isatype("dg_spec") has a matching field #isaconst("dgs_query") for a
handler that may read globals, and the generator installs it through the same
recursion (#isaconst("ask_with")). A local specification uses no globals.

== Many analyses over one state <sec:coop-mcp>

The activated analyses must run in one solve, since each needs the other's
facts at the same program point and context. The combined state
#isatype("mcp_st") nests one field per registered analysis in pairs of type
#isatype("analysis_product"). Each numeric field carries its own reachability
lift, and the whole state is lifted once more. A _lens_, a pair of a
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
components in turn. Entry runs the components' entries in turn.
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
empties the intersection, and #isathm("map_local_spec_sound") carries soundness
across it.

The analyzer assembles its combination from these parts
(@fig:mcp-assembly). The fields of #isatype("mcp_st") and the constants below
are generated from the analysis manifest (@ch:tooling). #isaconst("local_spec_of")
puts each registered analysis on its field through a lens. A numeric field
runs #isaconst("exec_spec"), the executable analysis of @sec:whole-state,
wrapped in #isaconst("ask_assign"). The order field runs #isaconst("order_spec")
unwrapped. #isaconst("mcp_field") replaces each field's handler by one that
answers from the field's readback (#isaconst("part_answer")), which is sound
because a handler may be replaced by any sound one (#isathm("with_qry_sound")).
The combined handler meets these answers, and #isaconst("ls_channel") closes
it over the combined state. #isaconst("mcp_comp") combines the fields of an
activation list and normalizes the result. #isathm("mcp_comp_sound") proves it
a sound local specification for every distinct, non-empty activation list,
from #isathm("mcp_combine_sound") and the independence of distinct fields. The
analyzer interprets #isalocale("dg_analysis") once per context family with
this component (#isathm("mcp_routed_dg_analysis")), and inside the locale
#isathm("dg_spec_of_contract") gives the analysis soundness contract.
@ch:equations consumes that contract and does not need to know how many
analyses produced it. For an arbitrary independent list without normalization,
#isathm("mcp_contract") states the same contract directly.

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    let mnode(pos, name, body, color: vb.neutral) = node(
      pos,
      align(center, body),
      name: name,
      stroke: 0.7pt + color,
      fill: color.lighten(93%),
      corner-radius: 2pt,
      inset: 5pt,
    )
    let lab(body) = text(size: 7pt, fill: vb.muted, body)
    let query(from, to, side) = edge(
      from,
      to,
      "<->",
      stroke: 0.6pt + vb.accent,
      label: lab[asks, answers],
      label-side: side,
    )
    let flow(from, to, ..args) = edge(from, to, "->", stroke: 0.6pt + vb.neutral, ..args)
    diagram(
      spacing: (10mm, 11mm),
      mnode(
        (0, 0),
        <m-num>,
        [numeric field \ #isaconst("ask_assign") around #isaconst("exec_spec")],
      ),
      mnode((1, 0), <m-chan>, [combined handler \ meets every answer]),
      mnode((2, 0), <m-ord>, [order field \ #isaconst("order_spec")]),
      mnode(
        (1, 1),
        <m-comp>,
        [#isaconst("mcp_comp") of the activation list \ #isathm("mcp_comp_sound")],
        color: vb.proved,
      ),
      mnode(
        (1, 2),
        <m-dg>,
        [#isalocale("dg_analysis"), one interpretation \ per context family],
        color: vb.proved,
      ),
      query(<m-num>, <m-chan>, left),
      query(<m-ord>, <m-chan>, right),
      flow(<m-num>, <m-comp>, label: lab(isaconst("mcp_field")), label-side: right),
      flow(<m-ord>, <m-comp>, label: lab(isaconst("mcp_field")), label-side: left),
      flow(<m-comp>, <m-dg>),
    )
  },
  kind: image,
  placement: auto,
  caption: [The combined state of the analyzer, schematic. Each registered
    analysis runs on its own field through #isaconst("mcp_field"). Blue arrows
    are queries through the closed channel, whose handler meets the answers of
    all active fields. The combination is proved sound once and consumed by the
    three interpretations of #isalocale("dg_analysis").],
) <fig:mcp-assembly>

== What a new analysis has to prove <sec:coop-catalogue>

A new analysis enters the combined state by one of two routes. On both, its
obligations are a fixed list that mentions no other analysis
(@tab:mcp-catalogue), and the framework proves the rest once.

A non-relational numeric domain supplies its primitive operations as one
record (#isatype("nonrelational_ops")) and certifies them once
(#isalocale("sound_nonrelational_ops"), @sec:instances-supply). From that
certificate #isathm("sound_nonrelational_ops.dg_analysis_execI") derives every
obligation of #isalocale("dg_analysis_exec") that concerns the domain: sound
transfers, agreement of the executable steps with the abstract ones, and a
sound check classifier. The domain's generated registration discharges the six
that remain, which concern the context policy, the solver and the initial
state. The soundness of its field component #isaconst("exec_spec") follows,
and the domain never states a law of #isaconst("sound_local_spec") itself.

Any other analysis proves a local specification sound directly. It may start
from the conservative defaults (#isaconst("conservative_local_spec")): the
handler answers $ltop$, skip, branch, body and event keep the state, and the
first return stage keeps the caller's state. Each default is sound for every
concretization, so the analysis supplies only assignment, special calls,
return, entry and the second return stage
(#isathm("sound_conservative_local_spec")). A field it overrides later needs
only that field's law again (#isathm("sound_local_spec_update")).

#figure(
  table(
    columns: (auto, auto),
    align: (left, center),
    stroke: none,
    table.hline(),
    [*the analysis proves*], [*the framework derives*],
    table.hline(stroke: 0.5pt),
    [carrier: join semilattice with $lbot$, widening, narrowing],
    [independence of fields (@sec:coop-mcp)],
    [$conc$ monotone], [soundness of the combination],
    [each edge field's law, under any channel that holds], [the closed channel holds],
    [entry coverage and a single entry], [the analysis soundness contract],
    [the composed return, under both channels], [coverage for every context policy (@ch:equations)],
    [the handler's answers hold], [the solved result and the verdicts (@ch:results)],
    table.hline(),
  ),
  placement: auto,
  caption: [The obligations of an analysis that joins the combined state,
    and what the framework proves once from them. Apart from the carrier's
    classes, the left column is #isaconst("sound_local_spec") with
    #isaconst("single_entry"). A numeric domain obtains it from its certified
    operations. The right column holds for every distinct, non-empty
    activation list.],
) <tab:mcp-catalogue>

The routed pipeline of @ch:equations asks for the single entry: entry answers one pair, whose resume value is the caller's state
(#isaconst("single_entry")). Lenses, combination and normalization preserve
it, so every activation list has it once each analysis does
(#isathm("single_entry_mcp_comp")).

On either route the analysis then needs an entry in the analysis manifest.
The generator derives from it the registration and the analysis's field of the
combined state. The command-line tool's table of analysis names is still
edited by hand (@ch:tooling).

The order analysis takes the second route. Its state is a set of pairs
$(x, y)$ with $x lt.eq y$ (#isatype("relc")). It starts from the conservative
defaults and overrides the handler and the branch. It answers comparisons
between variables it has ordered (#isathm("rel_qry_sound")), learns pairs at
assignments by asking, and enters and returns with no facts
(#isathm("order_spec_sound")). No theorem of the framework changed to admit
it. The numeric fields answer through #isaconst("part_answer") and ask at
assignments through #isaconst("ask_assign"). A numeric field answers
#isaconst("EvalInt") only for comparisons and logical operators and declines
every other expression with $ltop$, so a numeric assignment gains from asking
when another field decides the right-hand side.

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
Together, at `y = 10` the order analysis asks about the state before the
assignment whether $x lt.eq 10$. Interval knows $x = 0$ there and answers $1$,
so the order analysis records the pair $(x, y)$. At `y = 30` it asks whether
$x lt.eq 30$ and records the same pair, which therefore survives the join:
#verdict("coop-le-both", "21:3"). Variants of both programs, without the
`__voblint_nondet_int` initializations, are also proved by evaluation of
#isaconst("run_voblint") (#isathm("coop_demo_needs_both"),
#isathm("order_asks_needs_both")).

== What the combination leaves out <sec:coop-limits>

A component is a pure function of its state and its channels. It neither reads
nor publishes globals, so an analysis that needs its own global unknowns, such
as #isaconst("rel_order_spec"), cannot join the combined state. It enters the
proof at the analysis soundness contract of @sec:sound-core directly, and
#isaconst("run_voblint") does not select it. Goblint tags each analysis's
globals with its index instead. The second return stage
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
