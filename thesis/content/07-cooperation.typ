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

@ch:analysis-interface fixed what one analysis supplies: a record of
operations whose soundness is proved operation by operation. Some facts need two
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
The order analysis is relational: its state is a set of pairs $(x, y)$, each
meaning that the value of $x$ is at most the value of $y$. After the guards it
holds $(x, y)$ and $(y, x)$, so it knows that $x = y$, but it tracks no value
of `z` and reports #verdict("coop-eq-order", "16:7") too. Neither analysis can
decide the check. Together they can, if Interval's assignment can learn what
the order analysis knows at that point (@fig:mcp-step).

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
      cell((1, 1), <chan>, [meet of the answers], color: vb.accent),
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
  caption: [One step of Interval and the order analysis at `z = (x == y)` in
    the program above. Each analysis updates only its own part of the state.
    Interval's assignment asks #isaconst("EvalInt") $(x == y)$. Blue arrows
    show the answers of both analyses and their meet, $1$, which Interval
    receives. The final states match the analyzer run
    #verdict("coop-eq-both", "16:7") with #state("coop-eq-both", "16:7").],
) <fig:mcp-step>

Goblint solves this with its
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/mCP.ml",
)[_master control program_]
(MCP). The activated analyses run side by side, each on its own part of one
combined state, and a transfer may ask the other analyses a question through
the manager's `ask` function. Goblint does not prove anything about these
exchanges. A proof has a modularity problem: if Interval's assignment is proved
sound using the order analysis's invariant, the two proofs are coupled, every
new pair of analyses needs a new proof, and adding an analysis reopens old
ones. This chapter gives each analysis one proof obligation that does not
mention its partners. It shows that analyses meeting the obligation combine
into an analysis that meets the analysis contract of @sec:sound-core, so @ch:equations
applies to the combination unchanged.

== Questions and answers <sec:coop-queries>

The analyses must agree on what a question means and on what an answer
claims. A _query_ asks for a fact about the stores a state describes. Voblint
has one kind, named after Goblint's: the query #isaconst("EvalInt") $e$ asks
which integers the expression $e$ may evaluate to. Its answer is an abstract
value of Int (#isatype("int_dom")) of @sec:reduced-product,
lifted by a bottom and by a top element that claims nothing
(#isatype("query_lift")). Goblint answers its query in an analogous lifted
integer domain. A comparison evaluates to $0$ or $1$, so the exact answer $1$
to #isaconst("EvalInt") $(x == y)$ says that $x = y$.

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
$ivl(0, 1)$, which holds at every store, and the order analysis answers $1$.
Their meet is $1$: $x = y$. Goblint's `MCP.query'` combines answers the same
way, and answers $ltop$ to a query that would ask itself in a cycle.

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

By the two laws, the channel answering $ltop$ everywhere holds at every store,
and the pointwise meet of two channels that hold at $s$ holds at $s$
(#isathm("query_algebra.oracle_holds_inf")).

== Proving an analysis against any channel <sec:coop-oracle>

=== Transfers that ask <sec:coop-any-channel>

Interval's assignment in @fig:mcp-step uses the wrapper
#isaconst("ask_assign"), which any analysis can put around its assignment
$x := e$. The wrapper asks #isaconst("EvalInt") $e$. When the answer is one
integer $n$, it runs the analysis's own assignment of the literal $n$, and
otherwise the assignment of $e$. At $z := (x == y)$ Interval receives $1$ and
sets $z$ to $ivl(1, 1)$, which is right only if the answer is true. Proving
that from the order analysis's invariant would couple the two proofs.

Voblint makes the channel an argument of the transfer and the truth of its
answers a premise of the proof. The transfer
$#isaconst("ls_step") thin c thin A thin a thin x$ of a local specification $c$
receives a channel $A$ besides the action $a$ and the value $x$ before the
edge. Soundness
is the condition of @sec:dg with one extra premise: for every channel $A$,
every $s in conc(x)$ _at which $A$ holds_, and every
$s' in$ #isai("edge_step a s"), $s' in conc(#isaconst("ls_step") thin c thin A thin a thin x)$
(#isaconst("sound_local_spec"), #isathm("ls_step_sound_iff")). In the example, the premise excludes the stores
where $x != y$, at which the answer $1$ is false. At the others $e$ evaluates
to $1$, so the analysis's soundness for the literal $1$ gives soundness for
$e$. One theorem covers every analysis (#isathm("ask_assign_sound")). The proof
uses only that the answer holds, so it works with every partner whose answers
hold. @sec:coop-channel shows that the framework supplies a channel that holds
at every store of $conc(x)$, so the premise excludes no store.

The order analysis asks in the other direction (#isaconst("relc_learn")). At an
assignment $x := e$ it asks, for each variable $y$, whether $e lt.eq y$ and
whether $y lt.eq e$, and records the pairs the answer $1$ confirms. Its
soundness follows the same pattern (#isathm("relc_learn_sound")).

=== Local specifications with channels <sec:coop-local-spec>

Every operation may need its partners' answers, so every operation must
receive a channel. Most analyses use no analysis global, and for them the
framework offers a simpler interface than the record of @sec:spec-record, the
_local specification_ #isatype("local_spec") (@fig:local-spec). Its operations
work on local values, and each takes a channel as its first argument, of type
#isatype("answers"): a handler
#isaconst("ls_query") that answers queries about a state, one transfer per kind
of edge, enter, and the two combine stages. The step #isaconst("ls_step") on an
arbitrary edge dispatches to the edge transfers.

#figure(
  {
    show raw.where(block: true): set text(size: 6.5pt)
    thy("local_spec")
  },
  kind: image,
  placement: auto,
  caption: [The declaration of #isatype("local_spec"), lifted from the theory.
    Every operation receives a channel of type #isatype("answers"), and
    the first combine stage receives two.],
) <fig:local-spec>

Each operation receives the channel of the store it reasons about. The
handler, an edge transfer and enter receive the channel of the state they are
applied to. Combine reasons about two stores, the caller's at the call and the
callee's at its exit. It has the two stages of @sec:calls. The first,
#isaconst("ls_combine_env"), merges the caller's and the callee's environments
and receives both channels. The second, #isaconst("ls_combine_assign"), writes
the return value into the destination and receives the callee's channel.
Goblint's combine functions likewise receive the callee's `ask` function as an
extra argument.

Soundness (#isaconst("sound_local_spec")) asks for a monotone concretization
and one law per operation (#isathm("sound_local_spec_iff")). The edge, enter
and combine laws are #oblig("INTRA"), entry coverage and #oblig("RETURN") of
@ch:analysis-interface, each with the premise that the channels hold at the
stores involved. The two combine stages share one law for their composition.
The handler law is new: at every store of $conc(x)$ at which the channel the
handler receives holds, every answer it gives holds too (#isaconst("sound_query")). It is the analysis's
promise to its partners, and the only law they rely on.

The idea is not new. In Astrée a domain asks the others for constraints
through an input channel, and an abstract transfer need only be sound for
arguments that also satisfy the channel's constraints @cousot07astree[§§5.3, 6].
Verasco's numerical domains communicate through channels, from which we take
the term: records of query functions with a concretization that holds at an
environment when every answer is valid there, and each transfer function is
proved under the hypothesis that the channels it receives are correct
@jourdan15[§7]. Voblint uses the same form for Goblint's queries.

== Many analyses over one state <sec:coop-mcp>

The activated analyses must run in one solve, since each needs the others'
facts at the same program point and context. The combined state
#isatype("mcp_st") has one field per registered analysis, and its
concretization is the intersection of the concretizations of the selected
fields (#isaconst("mcp_gamma")). Fields of analyses that are not selected take
no part. We call a local specification that runs on one field a _component_.
Each component runs on its field through a _lens_, a getter and a setter for
that field (#isaconst("lens_of")), as Goblint's MCP hands each analysis its own
part of the combined state. A component therefore never changes what another
field describes. It is a _frame_ for the other fields
(#isathm("field_frame")), and components on distinct fields are
_independent_ (#isathm("mcp_independent_map")).

The combination should be sound whenever its components are sound and
independent, whatever channel they share. #isaconst("mcp_combine") builds it from a list: the step, enter and
the combine stages run the components in turn, and the handler meets their answers. Every
component receives the same channel, computed from the state before the edge,
as every Goblint analysis receives the same `ask`. A single component is its
own combination, so one analysis and an MCP of one analysis are the same
specification.

#proved("mcp_combine_sound", note: [Soundness of the combination.])

Take the step in @fig:mcp-step to see why. Start from a store that both fields
admit. Interval's assignment is sound, so its new field admits every store the
edge produces. The order analysis then updates only its own field, so it
cannot take anything away from Interval's, and its own new field is sound as
well. Every produced store is thus admitted by both fields, and so by the
combined state. The proof repeats this argument along the list. It uses only
each component's own laws. They hold for every channel that holds, so the
proof never needs to know which component gave an answer.

The analyzer builds this combination for the analyses the user selects
(#isaconst("mcp_comp")). The combined state is unreachable as soon as one field
is, as in Goblint's MCP. #isathm("mcp_comp_sound") proves the combination sound
for every non-empty selection of distinct analyses.

== Where the answers come from <sec:coop-channel>

The premise of @sec:coop-any-channel leaves one task to the framework: for
every state $x$ it must build a channel that holds at every store of
$conc(x)$. The answers come from the handler #isaconst("ls_query"). A handler
may ask in turn, though. The combined handler asks every component, and one
component's answer may depend on another's. The framework therefore answers by
recursion:

#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("ask_rec")
}

The handler $H$ answers $q$ at $x$ under a channel that remembers $q$ as
asked. A query asked again while it is being answered gets $ltop$, as in
Goblint's `MCP.query'`. Since queries range over an infinite type, a depth
bound (#isaconst("query_depth")) also stops the recursion: the generated
program aborts there, while in the logic the aborted branch returns $ltop$,
which holds at every store. The channel of a state $x$ is
#isaconst("ls_channel") $c$ $x$, the recursion started at depth
#isaconst("query_depth") with no query asked.

#proved("ls_channel_sound", note: [The channel the framework supplies holds.])

The proof is an induction on the depth (#isathm("ask_rec_sound")). At depth
$0$ every answer is $ltop$. At depth $n + 1$ the handler runs under the depth
$n$ channel, which holds by induction, so the handler law of
#isaconst("sound_local_spec") makes its answer hold. The channel is built from
the state before the edge, so its answers describe the predecessor state, as
in Goblint.

The equations consume the record of @sec:spec-record, so a local
specification must become one. #isaconst("dg_spec_of") does this, and the
record it builds never touches the analysis global. It computes the channel of each state
with #isaconst("ls_channel") and passes it to the operation, so its transfers
leave the manager's #isaconst("man_ask") unused. With the theorem above,
#isathm("dg_spec_of_contract") obtains the analysis contract
#isalocale("analysis_contract") from #isaconst("sound_local_spec"). Applied to
#isathm("mcp_comp_sound"), this gives the analysis contract for every selection, and
@ch:equations treats the combination like a single analysis.

== The combination at work <sec:coop-examples>

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
`__voblint_nondet_int` initializations, are checked by evaluating
#isaconst("run_voblint") (#isathm("coop_demo_needs_both"),
#isathm("order_asks_needs_both")), which trusts the code generator
(@sec:trust-boundary).

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

== What a new analysis has to prove <sec:coop-catalogue>

A new analysis joins the combined state by satisfying the laws of its local
specification (@sec:coop-local-spec). The laws mention no other analysis. Its
field, the lens and the code that reads its answers are generated from the analysis
manifest (@ch:tooling).

A non-relational numeric domain never states these laws itself. It proves
its primitives sound once (#isalocale("sound_nonrelational_ops"),
@sec:instances-supply). From that proof the framework proves the
domain's executable analysis #isaconst("exec_local_spec") a sound
local specification (#isathm("sound_nonrelational_ops.dg_analysis_execI")),
and #isathm("ask_assign_sound") keeps it sound under the wrapper. The domain's
own handler answers $ltop$. The analyzer replaces it by one that reads answers
off the domain's field (#isaconst("part_answer")), which is sound because a
handler may be replaced by any sound one (#isathm("with_qry_sound")). A
numeric field answers #isaconst("EvalInt") for comparisons and logical
operators and answers $ltop$ otherwise.

Any other analysis proves its local specification sound directly. Conservative
defaults (#isaconst("conservative_local_spec")) cover the handler, which
answers $ltop$, and skip, branch, body, event and the first combine stage,
which keep the state. They are sound for every concretization
(#isathm("sound_conservative_local_spec")), so the analysis supplies only
assignment, special calls, the return-statement transfer, enter and the second
combine stage. Replacing a default later needs only that operation's law
(#isathm("sound_local_spec_update")).

The order analysis is built this way. Its state (#isatype("relc")) is
unreachable or a set of pairs $(x, y)$, and it describes the stores $s$ with
$s(x) lt.eq s(y)$ for every pair. It replaces the default handler, which now
answers comparisons between variables it has ordered
(#isathm("relc_qry_sound")), and the default branch. It asks at assignments (@sec:coop-any-channel) and enters and returns
with no facts (#isathm("order_spec_sound")). @fig:contract-routes collects
the routes by which the analyses of this thesis reach the analysis contract.

#let _cbox(pos, name, body) = node(
  pos,
  text(size: 8pt, body),
  name: name,
  inset: 4pt,
  stroke: 0.6pt + vb.neutral,
  shape: rect,
  corner-radius: 2pt,
)
#let _clab(body) = text(size: 7pt, body)
#figure(
  diagram(
    spacing: (26mm, 6mm),
    _cbox((0, 0), <c-prim>, [primitives \ #isatype("nonrelational_ops")]),
    _cbox(
      (0, 1),
      <c-sound>,
      [soundness locale, once per domain \ #isalocale("sound_nonrelational_ops")],
    ),
    _cbox((0, 2), <c-rules>, [one rule per operation \ #isalocale("sound_nonrelational_transfer")]),
    _cbox((0, 3), <c-local>, [sound local specification \ #isaconst("sound_local_spec")]),
    _cbox((0, 4), <c-contract>, [analysis contract \ #isalocale("analysis_contract")]),
    _cbox((1, 3), <c-order>, [order analysis \ #isaconst("order_spec")]),
    _cbox(
      (1, 4),
      <c-relspec>,
      [order analysis with an analysis global \ #isaconst("rel_order_spec")],
    ),
    edge(
      <c-prim>,
      <c-sound>,
      "->",
      stroke: 0.6pt + vb.neutral,
      label: _clab[one interpretation per domain],
      label-side: left,
    ),
    edge(
      <c-sound>,
      <c-rules>,
      "->",
      stroke: 0.6pt + vb.neutral,
      label: _clab(isathm("sound_nonrelational_ops.is_sound_nonrelational_transfer")),
      label-side: left,
    ),
    edge(
      <c-rules>,
      <c-local>,
      "->",
      stroke: 0.6pt + vb.neutral,
      label: _clab[#isathm("dg_domain_exec.exec_local_spec_sound"), at #isaconst("exec_local_spec")],
      label-side: left,
    ),
    edge(
      <c-local>,
      <c-contract>,
      "->",
      stroke: 0.6pt + vb.neutral,
      label: _clab[#isathm("dg_spec_of_contract"), through #isaconst("dg_spec_of")],
      label-side: left,
    ),
    edge(
      <c-order>,
      <c-local>,
      "->",
      stroke: 0.6pt + vb.neutral,
      label: _clab(isathm("order_spec_sound")),
      label-side: right,
    ),
    edge(
      <c-relspec>,
      <c-contract>,
      "->",
      stroke: 0.6pt + vb.neutral,
      label: _clab[interpretation],
      label-side: left,
    ),
  ),
  kind: image,
  placement: auto,
  caption: [How the analyses of this thesis reach the analysis contract. An arrow leads from what an analysis supplies to what it thereby
    establishes, and its label names the Isabelle fact. A numeric domain
    proves its primitives sound once, which yields one rule
    per operation, as Voblint proves once for every domain. These rules make its executed local specification sound.
    The order analysis is a sound local specification by its own proof. Every
    sound local specification meets the analysis contract through
    #isaconst("dg_spec_of"). The order analysis with an analysis global is not a local specification and interprets the analysis contract itself.],
) <fig:contract-routes>

== What the combination leaves out <sec:coop-limits>

Components cannot read or publish analysis globals (@sec:analysis-globals).
Every fact a selectable analysis keeps therefore lives in its local state. The
one exception applies to the combined state as a whole: when program globals
are flow-insensitive, a lifter around the combination publishes each program
global's part of the combined state to that global's unknown
(@sec:mixed-flow). Apart from those, the only values published in an analyzer
run are the entry states that calls publish to their callees' seeds
(@sec:eq-seed-global). An analysis
with an analysis global, such as #isaconst("rel_order_spec"), is proved sound
on its own but cannot be selected. The analyzer runs a local variant of it,
the order analysis, instead. Goblint allows analysis globals in its MCP by
tagging each analysis's globals with the analysis's index.

The second combine stage receives only the callee's channel. Goblint's second
stage asks about the state its first stage produced, which describes no
concrete store here, because soundness is stated only for the composed combine.
Since the order analysis keeps no facts across calls, it is coarse there
(#fixture("25-cooperation/known-imprecision/04-order_forgotten_at_return.vimp", label: "04-order_forgotten_at_return")).
No theorem says that the combination is more precise than its parts. The two
runs of @sec:coop-examples witness it for one program each (@sec:eval-precision).
