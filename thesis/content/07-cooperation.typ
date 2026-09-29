#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
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
  $sem(e)_e s in conc(a)$:
  #{
    show raw.where(block: true): set text(size: 6.5pt)
    thy("eval_holds")
  }
]

Two laws, stated by the locale #isalocale("query_algebra"), let answers from
several analyses work together. The top answer $ltop$ holds at every store, so
an analysis that cannot answer a question answers $ltop$ and claims nothing.
If two answers hold at a store, so does their meet, so a question asked of all
analyses can be answered by the meet of their answers. In the example, asked
#isaconst("EvalInt") $(x == y)$ after both guards, Interval answers
$ivl(0, 1)$, which holds at every store, and the relational analysis answers
$1$. Their meet is $1$: $x = y$. Goblint's `MCP.query'` combines answers the
same way, and answers $ltop$ to a query that would ask itself in a cycle.

Checks are answered through the same questions. A check with condition $c$
becomes the question #isaconst("EvalInt") $c$. Each analysis answers it from
its check query of @sec:queries: $1$ if it proves $c$, $0$ if it refutes $c$,
and $ivl(0, 1)$ otherwise (#isaconst("sound_check_query.eval_answer")). The
analyzer meets the answers of all active analyses (#isaconst("mcp_answer")) and
reads the verdict off the result (#isaconst("mcp_classify")). A single analysis
thus gets its verdicts of @sec:queries back
(#isathm("sound_check_query.classify_eval_answer")), and several analyses
together can decide a check that each alone leaves unknown. Goblint's `assert`
analysis likewise reads its verdict off the answer to a value query.

== One obligation per operation, against every sound channel <sec:coop-oracle>

=== Channels <sec:coop-channels>

A transfer may ask several questions, and which ones depends on the state and
the edge. The framework therefore hands it all answers at once, as a function
from queries to answers.

#definition(name: [Channel], isa: "oracle_holds", cmd: "definition")[
  A _channel_ is a function $A$ from queries to answers. It _holds_ at a store
  $s$ if every answer it gives holds at $s$:
  #{
    show raw.where(block: true): set text(size: 6.5pt)
    thy("oracle_holds")
  }
]

By the laws of @sec:coop-queries, the channel answering $ltop$ everywhere
holds at every store, and the pointwise meet of two channels that hold at $s$
holds at $s$ (#isathm("query_algebra.oracle_holds_inf")).

=== Proving a transfer against any channel <sec:coop-any-channel>

Take Interval's assignment $z := (x == y)$ in the example. It asks
#isaconst("EvalInt") $(x == y)$, receives $1$, and sets $z$ to $ivl(1, 1)$,
which is right only if the answer is true. Proving that from the relational
analysis's invariant would tie Interval's proof to that partner, and every new
partner would need a new proof.

Voblint makes the channel an argument of the transfer and the truth of its
answers a premise of the proof. The transfer $"step"(A, a, x)$ receives a
channel $A$ besides the action $a$ and the value $x$ before the edge. Soundness
is the condition of @sec:dg with one extra premise: for every channel $A$,
every $s in conc(x)$ _at which $A$ holds_, and every
$s' in$ #isai("edge_step a s"), $s' in conc("step"(A, a, x))$ (the step law of
#isaconst("sound_local_spec"), split per edge kind by
#isathm("ls_step_sound_iff")). In the example,
the premise excludes the stores where $x != y$, at which the answer $1$ is
false. At the others $z$ becomes $1$, so $ivl(1, 1)$ is sound. The proof uses
only that the answer holds, so it works with every partner whose answers hold.
The framework discharges the premise once (@sec:coop-channel): it supplies a
channel that holds at every store of $conc(x)$.

The idea is not new. In Astrée a domain asks the others for constraints
through an input channel, and an abstract transfer need only be sound for
arguments that also satisfy the channel's constraints @cousot07astree[§§5.3, 6].
Verasco's numerical domains communicate through channels, from which we take
the term: records of query functions with a concretization that holds at an
environment when every answer is valid there, and each transfer function is
proved under the hypothesis that the channels it receives are correct
@jourdan15[§7]. Voblint uses the same form for Goblint's queries.
It also covers calls and returns, and handlers that ask in turn
(@sec:coop-channel).

=== Local specifications with channels <sec:coop-local-spec>

An analysis that cooperates supplies a _local specification_
(#isatype("local_spec"), @fig:local-spec). It has the operations of
@sec:sound-core, and each takes a channel as its first argument, of type
#isatype("answers"): a handler #isaconst("ls_query") that answers queries about
a state, one transfer per kind of edge, entry, and the two return stages. The
step #isaconst("ls_step") on an arbitrary edge dispatches to the edge
transfers. We call a local specification that runs inside the combined state
of @sec:coop-mcp a _component_.

#figure(
  {
    show raw.where(block: true): set text(size: 6.5pt)
    thy("local_spec")
  },
  kind: image,
  placement: auto,
  caption: [The declaration of #isatype("local_spec"), lifted from the theory.
    Every operation receives a channel of type #isatype("answers"), and
    the first return stage receives two.],
) <fig:local-spec>

Each operation receives the channel of the store it reasons about. The
handler, an edge transfer and entry receive the channel of the state they are
applied to. A return reasons about two stores, the caller's at the call and the
callee's at its exit. The return has the two stages of @sec:calls. The first,
#isaconst("ls_combine_env"), merges the caller's and the callee's
environments and receives both channels. The second,
#isaconst("ls_combine_assign"), writes the return value into the destination
and receives the callee's channel. Goblint's return functions likewise receive the
callee's `ask` function as an extra argument.

Soundness (#isaconst("sound_local_spec")) is one law per operation
(#isathm("sound_local_spec_iff")). The edge, entry and return laws are
#oblig("INTRA"), entry coverage and #oblig("RETURN") of
@ch:analysis-interface, each with the premise of @sec:coop-any-channel that the
channels hold at the stores involved. The two return stages share one law for
their composition. The handler law is new: every answer holds at every store
of $conc(x)$. It is the analysis's promise to its partners, and the only law
they rely on.

Two transfers from the development show how an operation uses its channel. The wrapper
#isaconst("ask_assign") lets any component use the channel at an assignment
$x := e$: it asks #isaconst("EvalInt") $e$, and when the answer is one integer
$n$, it runs the component's own assignment of the literal $n$. Since the
answer holds, $e$ evaluates to $n$ at every store the proof considers, so the
component's soundness for the literal gives soundness for $e$. One theorem
covers every component (#isathm("ask_assign_sound")). The order analysis goes
the other way (#isaconst("rel_learn")). At $x := e$ it asks, for each
candidate $y$, whether $e lt.eq y$ and whether $y lt.eq e$, and records the
pairs the answer $1$ confirms (#isathm("rel_learn_sound")).

== Where the answers come from <sec:coop-channel>

The premise of @sec:coop-any-channel leaves one task to the framework: for
every state $x$ it must build a channel that holds at every store of
$conc(x)$. The answers come from the handler #isaconst("ls_query"). A handler
may ask in turn, though. In the combined state of @sec:coop-mcp the handler
asks every component, and one component's answer may depend on another's. The
framework therefore answers by recursion:

#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("ask_rec")
}

The handler $H$ answers $q$ at $x$ under a channel that remembers $q$ as
asked. A query asked again while it is being answered gets $ltop$, as in
Goblint's `MCP.query'`. Queries range over an infinite type, so cycle
detection alone does not bound the recursion. The depth bound
#isaconst("query_depth") does: when it runs out, the generated program aborts.
In the logic `Code.abort` returns its fallback $ltop$, which holds at every
store, so the bound costs no soundness. The channel of a state $x$ is
#isaconst("ls_channel") $c$ $x$, the recursion started at depth
#isaconst("query_depth") with no query asked.

#proved("ls_channel_sound", note: [The channel the framework supplies holds.])

The proof is an induction on the depth (#isathm("ask_rec_sound")). At depth
$0$ every answer is $ltop$. At depth $n + 1$ the handler runs under the depth
$n$ channel, which holds by induction, so the handler law of
#isaconst("sound_local_spec") makes its answer hold. The channel is built from
the state before the edge, so its answers describe the predecessor state, as
in Goblint.

The theorem discharges the premise. #isaconst("dg_spec_of") of
@sec:sound-core runs every operation of a local specification with the channel
of the state it is applied to, and #isathm("dg_spec_of_contract") obtains the
analysis soundness contract #isalocale("analysis_contract") from
#isaconst("sound_local_spec").

== Many analyses over one state <sec:coop-mcp>

The activated analyses must run in one solve, since each needs the others'
facts at the same program point and context. The combined state
#isatype("mcp_st") has one field per analysis (@fig:mcp-step), and its
concretization is the intersection of the fields' concretizations
(#isaconst("mcp_gamma")). Each component runs on its own field through a
_lens_, a getter and a setter for that field (#isaconst("lens_of")), as
Goblint's MCP hands each analysis its own part of the combined state. A
component therefore never changes what another field describes. It is a
_frame_ for the other fields (#isathm("lens_of_frame")), and components on
distinct fields are _independent_ (#isathm("mcp_independent_map")).

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    let cell(pos, name, body, color: vb.neutral) = node(
      pos,
      align(center, body),
      name: name,
      stroke: 0.7pt + color,
      fill: color.lighten(93%),
      corner-radius: 2pt,
      inset: 5pt,
      width: 30mm,
    )
    let lab(body) = text(size: 7pt, fill: vb.muted, body)
    let ask(from, to, body, side) = edge(
      from,
      to,
      "->",
      stroke: 0.6pt + vb.accent,
      label: lab(body),
      label-side: side,
    )
    diagram(
      spacing: (8mm, 9mm),
      node((-1, 0), lab[before \ `z = (x == y)`], stroke: none),
      node((-1, 2), lab[after], stroke: none),
      cell((0, 0), <b-int>, [Interval \ $x, y$ unbounded]),
      cell((2, 0), <b-ord>, [Order \ $x lt.eq y, y lt.eq x$]),
      cell((1, 1), <chan>, [channel \ meet of the answers], color: vb.accent),
      cell((0, 2), <a-int>, [Interval \ $z = ivl(1, 1)$]),
      cell((2, 2), <a-ord>, [Order \ $x lt.eq y, y lt.eq x$]),
      edge(
        <b-int>,
        <a-int>,
        "->",
        stroke: 0.6pt + vb.neutral,
        label: lab[assign],
        label-side: right,
      ),
      edge(
        <b-ord>,
        <a-ord>,
        "->",
        stroke: 0.6pt + vb.neutral,
        label: lab[assign],
        label-side: left,
      ),
      ask(<b-int>, <chan>, [$ivl(0, 1)$], left),
      ask(<b-ord>, <chan>, [$1$], right),
      ask(<chan>, <a-int>, [$1$], left),
    )
  },
  kind: image,
  placement: auto,
  caption: [One step of the combined state for Interval and the order analysis
    at `z = (x == y)` in the program at the start of this chapter. Each
    analysis updates only its own field. Interval's assignment asks
    #isaconst("EvalInt") $(x == y)$. Blue arrows show the answers of both
    fields and their meet, $1$, which the channel returns. The combined state
    describes the stores both fields admit. The final states match the
    analyzer run #verdict("coop-eq-both", "16:7") with
    #state("coop-eq-both", "16:7").],
) <fig:mcp-step>

#isaconst("mcp_combine") builds one component from a list. The step, entry and
return run the components in turn, and the handler meets their answers. A
single component is its own combination, so one analysis and an MCP of one
analysis are the same specification.

#proved("mcp_combine_sound", note: [Soundness of the combination.])

Take the step in @fig:mcp-step to see why. Start from a store that both fields
admit. Interval's assignment is sound, so its new field admits every store the
edge produces. The order analysis then updates only its own field, so it
cannot take anything away from Interval's, and its own new field is sound as
well. Every produced store is thus admitted by both fields, and so by the
combined state. The proof repeats this argument along the list of analyses. It
uses only each analysis's own laws. They hold for every channel that holds, so
the proof never needs to know which analysis gave an answer.

The analyzer builds this combination for the analyses the user selects
(#isaconst("mcp_comp")). The combined state is unreachable as soon as one field
is, as in Goblint's MCP. #isathm("mcp_comp_sound") proves the combination sound
for every non-empty selection of distinct analyses, so it meets the analysis
soundness contract of @sec:sound-core, and @ch:equations treats it like a
single analysis.

== What a new analysis has to prove <sec:coop-catalogue>

A new analysis joins the combined state by satisfying the laws of its local
specification (@sec:coop-local-spec). The laws mention no other analysis, and
the framework proves the rest once: the combination, the channel, the analysis
soundness contract and the results of the later chapters.

=== Numeric domains <sec:coop-numeric>

A non-relational numeric domain never states these laws itself. It supplies
its primitive operations as one record (#isatype("nonrelational_ops")) and
certifies them once (#isalocale("sound_nonrelational_ops"),
@sec:instances-supply). From that certificate the framework derives the
obligations that concern the domain
(#isathm("sound_nonrelational_ops.dg_analysis_execI")), and with them the
soundness of the domain's field. A numeric field answers
#isaconst("EvalInt") for comparisons and logical operators, answers $ltop$
otherwise, and asks at assignments through #isaconst("ask_assign").

=== Other analyses <sec:coop-other>

Any other analysis proves its local specification sound directly. Conservative
defaults (#isaconst("conservative_local_spec")) cover the handler, which
answers $ltop$, and skip, branch, body, event and the first return stage,
which keep the state. They are sound for every concretization
(#isathm("sound_conservative_local_spec")), so the analysis supplies only
assignment, special calls, return, entry and the second return stage. Replacing
a default later needs only that operation's law
(#isathm("sound_local_spec_update")).

The order analysis is built this way. Its state is a set of pairs $(x, y)$
with $x lt.eq y$ (#isatype("relc")). It replaces the default handler, which
now answers comparisons between variables it has ordered
(#isathm("rel_qry_sound")), and the default branch. At assignments it asks and
records the pairs the answers confirm, and it enters and returns with no facts
(#isathm("order_spec_sound")). No theorem of the framework changed to admit
it.

=== The combination at work <sec:coop-examples>

The combination decides the check at the start of this chapter, as
@fig:mcp-step shows: Interval asks and the order analysis answers. The
exchange also works the other way, with the order analysis asking
(@fig:coop-le).

#figure(
  listing(lang: "c", claim: "coop-le-both", ```
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
  ```),
  kind: image,
  placement: auto,
  caption: [A check that needs the order analysis to ask Interval.],
) <fig:coop-le>

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

Components cannot read or publish analysis globals (@sec:analysis-globals).
Every fact a selectable analysis keeps therefore lives in its flow-sensitive
local state, program globals included. The only side effects in an analyzer
run are the framework's activation seeds (@sec:global-unknowns). An analysis
with an analysis global, such as #isaconst("rel_order_spec"), is proved sound
on its own but cannot be selected. The analyzer runs a local variant of it,
the order analysis, instead. Goblint allows analysis globals in its MCP by
tagging each analysis's globals with the analysis's index.

The second return stage
receives only the callee's channel. Goblint's second stage asks about the
state its first stage produced, which describes no concrete store here, because
soundness is stated only for the composed return. The order analysis is coarse at calls: it enters and
returns with no facts
(#fixture("25-cooperation/known-imprecision/04-order_forgotten_at_return.vimp", label: "04-order_forgotten_at_return")).
No theorem says that the combination is more precise than its parts. The two
runs above witness it for one program each (@sec:eval-rq4).
