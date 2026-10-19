#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig, thy-badge
#import "../lib/math.typ": *
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": definition
#import "../lib/figures.typ": verdict as verdict-chip
#import "../lib/claims.typ": claim-check, claim-ref

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
#let verdict(name, loc) = verdict-chip(claim-row(name, loc).verdict)
#let state(name, loc) = absval(raw(claim-row(name, loc).state))

= Cooperating Analyses <ch:cooperation>

An analysis of @ch:analysis-interface sees only its own state. For some
properties a user checks, however, a single analysis is not enough. They can
only be proved by combining what several analyses know while they run
together. Consider the
example below:

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

A reader easily sees that the check holds in every run, since both guards hold
at the assignment, so $x = y$ and `z` is $1$. No single analysis, however, can
prove it. Interval keeps one range per variable. After the guards, both `x` and `y` are
still unbounded, so `x == y` evaluates to $absval(ivl(0, 1))$ and the check stays
#verdict("coop-eq-interval", "16:7") with #state("coop-eq-interval", "16:7").
The order analysis (@sec:relational) is relational. Its state is a set of pairs $(x, y)$, each
meaning that the value of $x$ is at most the value of $y$. After the guards, it
holds $(x, y)$ and $(y, x)$, so it knows that $x = y$. It tracks no values of variables,
however, so it learns nothing about `z` and reports #verdict("coop-eq-order", "16:7") too. Together, the two can
decide it, if Interval's assignment can learn what
the order analysis knows at that point (@fig:mcp-step).

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    let lab(body) = text(size: 7pt, fill: vb.muted, body)
    let party(pos, body, color: vb.neutral) = node(
      pos,
      align(center, body),
      stroke: 0.7pt + color,
      fill: color.lighten(93%),
      corner-radius: 2pt,
      inset: 4pt,
      width: 30mm,
    )
    let life(x) = edge((x, 0), (x, 5), stroke: (paint: vb.muted, thickness: 0.4pt, dash: "dashed"))
    let msg(from, to, body, side: left) = edge(
      from,
      to,
      "->",
      stroke: 0.6pt + vb.accent,
      label: lab(body),
      label-side: side,
    )
    diagram(
      spacing: (14mm, 6.5mm),
      life(0),
      life(1),
      life(2),
      party((0, 0), [Interval \ $x, y$ unbounded]),
      party((1, 0), [channel], color: vb.accent),
      party((2, 0), [Order \ $x lt.eq y, y lt.eq x$]),
      msg((0, 1), (1, 1), [asks #isaconst("EvalInt") $(x == y)$]),
      msg((0, 2), (1, 2), [answers $absval(ivl(0, 1))$]),
      msg((2, 2), (1, 2), [answers $1$], side: right),
      node((1, 3), text(size: 7pt)[$absval(ivl(0, 1)) lmeet 1 = 1$], fill: white, inset: 2pt),
      msg((1, 4), (0, 4), [$1$], side: right),
      party((0, 5), [Interval after \ $z = absval(ivl(1, 1))$]),
    )
  },
  kind: image,
  placement: none,
  caption: [One step of Interval and the order analysis at `z = (x == y)` in
    the program above (schematic). Interval's assignment asks #isaconst("EvalInt") $(x == y)$. The channel
    asks the handler of every analysis and gives Interval the meet of their
    answers. Each analysis updates only its own field
    of the product state. The final states match the analyzer run
    #verdict("coop-eq-both", "16:7") with #state("coop-eq-both", "16:7").],
) <fig:mcp-step>

Goblint solves this with its
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/mCP.ml",
)[_master control program_]
(MCP). The selected analyses run side by side, each on its own part of one
product state, and a transfer may ask all selected analyses a question
through the manager's `ask` function. Goblint has no machine-checked argument that these exchanges are sound. A
proof, however, has a modularity problem. If Interval's assignment is proved
sound using the order analysis's invariant, the two proofs are coupled, every
new pair of analyses needs a new proof, and adding an analysis reopens old
ones. This chapter describes how each analysis instead gets one proof
obligation that does not mention the analyses it runs with, and why analyses
meeting it combine into one analysis that meets the analysis contract of
@sec:sound-core.

== Queries, answers, and channels #thy-badge("Voblint_Framework", "Analysis_Query") <sec:coop-queries>

The analyses must agree on what a question means and on what an answer
claims. A _query_ asks for a fact about the stores a state describes. Voblint
has one kind, named after Goblint's. The query #isaconst("EvalInt") $e$ asks
which integers the expression $e$ may evaluate to. Its answer is a value of the reduced product Int (#isatype("int_dom"),
@sec:reduced-product), lifted by a bottom and by a top element that claims nothing
(#isatype("query_lift")). A
comparison evaluates to $0$ or $1$, so the exact answer $1$ to
#isaconst("EvalInt") $(x == y)$ says that $x = y$.

#definition(name: [Truth of an answer], isa: "eval_holds", cmd: "fun")[
  An answer $a$ to #isaconst("EvalInt") $e$ _holds_ at a store $s$ if
  $sem(e)_e s in conc(a)$:
  #{
    show raw.where(block: true): set text(size: 6.5pt)
    thy("eval_holds")
  }
]

Two laws, stated by the locale #isalocale("query_algebra"), let answers from
several analyses work together:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("query_algebra")
}
The top answer $ltop$ holds at every store, so
an analysis that cannot answer a query answers $ltop$ and claims nothing.
If two answers hold at a store, so does their meet, so a query asked of all
analyses can be answered by the meet of their answers. In the example, when asked #isaconst("EvalInt") $(x == y)$ after both guards, Interval answers
$absval(ivl(0, 1))$, which holds at every store, and the order analysis answers $1$.
Their meet is $absval(ivl(0, 1)) lmeet 1 = 1$, so $x = y$. Goblint's `MCP.query'` combines answers the
same way, as formalized by Apinis @apinis14[§5.5].

A transfer may need answers to several queries. Instead of answering each
query separately, the framework passes the transfer one function that
answers every query, a _channel_ $italic("ch")$ of type #isatype("channel"),
and the transfer applies it to the queries it needs. A single premise about
the channel then covers all answers the transfer uses. A channel _holds_ at a store $s$ if every answer it
gives holds at $s$:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("channel_holds")
}
By the two laws, the channel answering $ltop$ everywhere holds at every store,
and the pointwise meet of two channels that hold at $s$ holds at $s$
(#isathm("query_algebra.channel_holds_inf")).

== Proving each analysis against true answers #thy-badge("Voblint_Framework", "MCP_Spec") <sec:coop-channels>

Interval's assignment in @fig:mcp-step uses the wrapper
#isaconst("ask_assign"), which any analysis can put around its assignment
$x := e$. The wrapper asks #isaconst("EvalInt") $e$. When the answer is one
integer $n$, it runs the analysis's own assignment of the literal $n$, and
otherwise, the assignment of $e$. At $z := (x == y)$, Interval receives $1$ and
sets $z$ to $absval(ivl(1, 1))$, which is right only if the answer is true. Proving
that from the order analysis's invariant would couple the two proofs.

Voblint avoids this coupling by separating two facts, that a transfer uses its
answers correctly and that the answers are true. The transfer
$#isaconst("ls_step") thin c thin italic("ch") thin a thin x$ of an analysis $c$
receives the channel $italic("ch")$ as an extra argument, besides the action
$a$ and the state $x$ before the edge. Its soundness is proved under the
assumption that the channel holds. The transfer must lose no successor, as in
@sec:calls, but only of stores at which every answer is true
(#isathm("ls_step_sound_iff")). Whether the answers are true is not the
transfer's concern, and @sec:coop-mcp shows that the framework always supplies
a channel that holds.

For #isaconst("ask_assign") this assumption is exactly what the proof needs.
In the example, only the stores with $x = y$ remain, because the answer $1$ is
false at all others. At these stores, $e$ evaluates to $1$, so the analysis's
own assignment of the literal $1$ is sound for $e$ as well
(#isathm("ask_assign_sound")). The proof never mentions the order analysis
and works with any analyses whose answers hold.

An analysis without analysis globals is written as a _local specification_
(#isatype("local_spec")). It bundles the operations of @sec:calls, each taking
a channel, with a handler #isaconst("ls_query") that answers queries about a
state, so that the analysis can answer queries from the analyses it runs with.

#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("local_spec")
}

Every operation receives a channel. The first combine stage receives two, one
with answers about the caller's state and one with answers about the callee's
exit state.

A local specification is sound (#isaconst("sound_local_spec")) if its
operations satisfy the laws of the analysis contract (@sec:sound-core), each
under the assumption that its channels hold, as for the transfer above. This
amounts to a monotone concretization and one law per operation
(#isathm("sound_local_spec_iff")). The edge and combine laws correspond to
those of the analysis contract, and the enter law to entry coverage. The handler adds
a law of its own. Its answers about a state $x$ must hold at every store of
$conc(x)$ at which its own channel holds (#isaconst("sound_query")), and the
analyses rely on one another only through this law. Verasco proves each
transfer function under the hypothesis that the channels it receives are
correct @jourdan15[§7], following Astrée @cousot07astree[§§5.3, 6], and Voblint
applies the same form of proof to Goblint's queries.

== Combining analyses into one sound analysis #thy-badge("Voblint_Framework", "MCP_Spec") <sec:coop-mcp>

The analyses cannot be solved one after another, because each may need the
other's facts at the same program point and context. In the program below, the
exchange runs in both directions, here between the order analysis and Int, the
reduced product (@sec:reduced-product).

#let _z(name) = claim-check(name, "z == 1")
#listing(lang: "c", claim: "coop-mutual-both", ```
fun main() {
  c = __voblint_nondet_int();
  if (0 < c) { x = 0; y = 10; } else { x = 20; y = 30; }
  z = (x <= y);
  __voblint_check(z == 1);
}
```)

Int alone joins the branches, so `z` lies only in
#raw(_z("coop-mutual-int").at(4).split("intervals:").at(1).split(";").at(0)),
and the check is #verdict-chip(_z("coop-mutual-int").at(3)). The order analysis
alone cannot compare a variable with a constant and reports
#verdict-chip(_z("coop-mutual-order").at(3)). Together, at both assignments to
`y` the order analysis asks Int whether $x$ is at most the assigned constant
and records the pair $(x, y)$ on both branches. At `z = (x <= y)` Int asks
#isaconst("EvalInt") $(x <= y)$, the order analysis answers $1$, and the check
is #verdict-chip(_z("coop-mutual-both").at(3)) (claims
#claim-ref("coop-mutual-*")).

The framework therefore runs all selected analyses as a
single analysis whose abstract state is a tuple with one field per analysis.
For the solver,
the tuple is one abstract state per node and context like any other. It is ordered, joined, and widened field by field (#isatype("analysis_product")),
so each field evolves as it would alone, except that its transfers may ask the
other fields. If one selected field shows that a node is unreachable, the whole
product state does (#isaconst("mcp_norm")).

The product state #isatype("mcp_st") has one field per analysis the analyzer
ships, and a run uses the fields of the analyses the user selects
(@fig:mcp-combine). The product state describes a store if every selected field does:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("mcp_gamma")
}
Here, $Gamma$ is the list of concretizations of the selected fields. Each
$gamma_i in Gamma$ reads its own field of $x$, so $gamma_i (x)$ is the
concretization of that field.
#figure(
  {
    set text(size: 7.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let lab(body) = text(size: 6.5pt, fill: vb.muted, body)
    let cell(pos, name, body, color: vb.neutral, width: 21mm) = node(
      pos,
      align(center, body),
      name: name,
      stroke: 0.6pt + color,
      fill: white,
      corner-radius: 2pt,
      inset: 4pt,
      width: width,
    )
    let rows = (("Interval", "I"), ("Order", "O"))
    let panel(a, b, name, title) = node(
      enclose: (a, b),
      stroke: 0.6pt + vb.neutral,
      fill: vb.neutral.lighten(95%),
      inset: 6pt,
      corner-radius: 3pt,
      name: name,
    )
    diagram(
      spacing: (11mm, 3mm),
      // before, components, after
      ..rows
        .enumerate()
        .map(((i, r)) => (
          cell((0, i), label("b" + str(i)), [#r.at(0) field \ $x_#r.at(1)$]),
          cell(
            (1, i),
            label("c" + str(i)),
            [*#r.at(0)* \ transfer + handler],
            color: vb.accent,
            width: 25mm,
          ),
          cell((2, i), label("a" + str(i)), [#r.at(0) field \ $x'_#r.at(1)$]),
          edge(label("b" + str(i)), label("c" + str(i)), "->", stroke: 0.6pt + vb.neutral),
          edge(label("c" + str(i)), label("a" + str(i)), "->", stroke: 0.6pt + vb.neutral),
        ))
        .flatten(),
      cell((0, 2), <b2>, $dots.v$, width: 21mm),
      cell((1, 2), <c2>, $dots.v$, color: vb.accent, width: 25mm),
      cell((2, 2), <a2>, $dots.v$, width: 21mm),
      panel(<b0>, <b2>, <before>, none),
      panel(<a0>, <a2>, <after>, none),
      node(
        enclose: (<c0>, <c2>),
        stroke: 0.6pt + vb.accent,
        fill: vb.accent.lighten(92%),
        inset: 6pt,
        corner-radius: 3pt,
        name: <band>,
      ),
      node((0, -0.9), lab[product state $x$], stroke: none),
      cell(
        (1, -1.6),
        <chan>,
        [channel $italic("ch")$ \ meet of handler answers],
        color: vb.accent,
        width: 30mm,
      ),
      edge(
        <chan>,
        <band>,
        "->",
        stroke: 0.6pt + vb.accent,
        label: lab[same for all],
        label-side: left,
      ),
      node((2, -0.9), lab[product state $x'$], stroke: none),
    )
  },
  kind: image,
  placement: none,
  caption: [One step of the combination (schematic). Each component reads its
    own field of the product state $x$ and writes its own field of $x'$, and
    the components run in turn. All components receive the same channel
    $italic("ch")$ (blue).],
) <fig:mcp-combine>

A local specification that runs on one field is called a _component_. Each
component reads and writes only its own field, through a _lens_
(#isaconst("lens_of")) that takes the field out of the product state and puts
a new value back, as Goblint's MCP hands each analysis its own part of the
product state. A component therefore leaves the concretizations of all other
fields unchanged (#isathm("field_frame")), which makes the components
_independent_ (#isaconst("mcp_independent")). #isaconst("mcp_combine") runs the
components in turn, gives each of them the same channel, and meets the answers of
their handlers. If the list of components is nonempty, the components are
independent, and each is a sound local specification, then the combination is
a sound local specification for the intersection of their concretizations
(#isathm("mcp_combine_sound")). The components cannot invalidate one
another's guarantees, since each guarantee is about a field no other component
writes. Instantiated with the analyses Voblint ships, the theorem gives the
result of this chapter. Any nonempty list #isai("as") of distinct analyses
combines into a sound local specification:

#proved("mcp_comp_sound")

Running the combined handler on the current state $x$ gives a channel for the
premise of the theorem (#isaconst("ls_channel")). A query that comes back while
it is being answered gets $ltop$, as in Goblint's `MCP.query'`. Every answer of
this channel holds at every store of $conc(x)$ (#isathm("ls_channel_sound")),
so #isaconst("dg_spec_of") can pass it to the operations and turn the
combination into a record that meets the analysis contract
(#isathm("dg_spec_of_contract")).

Each analysis is thus proved sound once, against any channel that holds, and
its proof never mentions the analyses it runs with. Their combination meets the
analysis contract and decides the check of the opening example. Adding an
analysis requires only its own proof, and the proofs of the others stay
unchanged. @ch:equations discharges the obligations of @ch:traces for any
analysis that meets the analysis contract, the combination included.
