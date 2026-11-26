#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig, thy-badge
#import "../lib/math.typ": *
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": definition, theorem
#import "../lib/figures.typ": verdict as verdict-chip
#import "../lib/claims.typ": claim-check, claim-ref, claim-row

#let verdict(name, loc) = verdict-chip(claim-row(name, loc).verdict)
#let state(name, loc) = absval(raw(claim-row(name, loc).state))

= Cooperating Analyses <ch:cooperation>

An analysis of @ch:analysis-interface sees only its own state. Some checks,
however, can only be proved by combining what several analyses know while
they run together. The program below contains such a check:

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

Both guards hold at the assignment, so $x = y$, `z` is $1$, and the check
holds. Interval keeps one range per variable, leaving `x` and `y` unbounded
after the guards. Thus `x == y` evaluates to $absval(ivl(0, 1))$ and the check stays
#verdict("coop-eq-interval", "16:7") with #state("coop-eq-interval", "16:7").
Suppose a second, relational analysis runs alongside Interval and tracks the
order between variables as a set of pairs $(x, y)$, each meaning that the value
of $x$ is at most the value of $y$ (the order analysis of @sec:relational). After the guards, it
holds $(x, y)$ and $(y, x)$, so it knows that $x = y$. Since it tracks no values of variables, it
learns nothing about `z` and reports #verdict("coop-eq-order", "16:7") too. Together, the two can
decide it, if Interval's assignment can use the order analysis's fact
$x = y$ at that point (@fig:mcp-step).

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
  caption: [One step of Interval and the order analysis at `z = (x == y)`
    (schematic). Interval asks which values $x == y$ may take, and the channel of
    @sec:coop-queries gives it the meet of all analyses' answers. The final state matches the
    analyzer run, #verdict("coop-eq-both", "16:7") with
    #state("coop-eq-both", "16:7").],
) <fig:mcp-step>

Goblint solves this with its
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/mCP.ml",
)[_master control program_]
(MCP). The selected analyses run side by side, each on its own part of one
product state, and a transfer may ask all selected analyses a question
through the MCP's `ask` function. Goblint has no machine-checked soundness
argument for these exchanges. If the proof of one analysis relied on
the invariant of another, their proofs would be coupled, and every new
combination would need new proofs. Voblint instead gives each analysis one
obligation that does not mention its partners. When every selected analysis
meets it, their combination meets the analysis contract of @sec:sound-core.

== Queries, answers, and channels #thy-badge("Voblint_Framework", "Analysis_Query") <sec:coop-queries>

The analyses must agree on what a question means and on what an answer
claims. An _analysis query_, unlike the solver queries of @sec:td, asks an
analysis for a fact about the stores its state describes. Voblint has one kind,
named after Goblint's. The query #isaconst("EvalInt") $e$ asks
which integers the expression $e$ may evaluate to. An #isaconst("EvalInt") answer uses Int, the reduced
product of the four numeric domains Sign, Interval, Parity, and Congruence
(@sec:reduced-product). An Int value holds one value of each and denotes the
integers all four admit (#isatype("int_dom")).
The answer type adds a bottom and a top element that claims nothing
(#isatype("query_lift")). A
comparison evaluates to $0$ or $1$, so the exact answer $1$ to
#isaconst("EvalInt") $(x == y)$ says that $x = y$.

#definition(name: [Truth of a query answer], isa: "eval_holds", cmd: "fun")[
  The predicate $#isaconst("eval_holds") (ctor("EvalInt")(e),a,s)$ says that answer $a$
  to expression query $e$ holds at store $s$:
  $ #isaconst("eval_holds") (ctor("EvalInt")(e),a,s) arrow.l.r.double sem(e)_e s in conc(a). $
  Here $conc(a)$ is $emptyset$ for the added bottom, $ZZ$ for the added top,
  and the concretization of $d$ for a lifted value $d$.
]

Two laws, stated by the locale #isalocale("query_algebra"), let answers from
several analyses work together:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("query_algebra")
}
An analysis that cannot answer returns $ltop$, which holds at every store.
Meeting answers that hold at a store preserves truth there, so the framework
combines all analyses' answers by meet (@fig:mcp-step).
Goblint's `MCP.query'` combines answers the
same way, as formalized by Apinis @apinis14[§5.5].

A transfer may ask several queries, so the framework hands it all answers at
once, as a _channel_ (#isatype("channel")) that maps every query to its answer.
A channel _holds_ at a store when every answer in it is true there, in the
sense of the definition above (#isaconst("channel_holds")). Both laws of the query
algebra carry over to channels. The channel that answers $ltop$ to every query holds at every
store, and the meet of two channels that hold at a store still holds there
(#isathm("query_algebra.channel_holds_inf")).

== Soundness given correct query answers #thy-badge("Voblint_Framework", "MCP_Spec") <sec:coop-channels>

Interval's assignment in @fig:mcp-step uses the wrapper
#isaconst("ask_assign"), which any analysis can put around its assignment
$x := e$. The wrapper asks #isaconst("EvalInt") $e$. When the answer is one
integer $n$, it runs the analysis's own assignment of the literal $n$, and
otherwise, the assignment of $e$.

The transfer
$#isaconst("ls_step") thin c thin italic("ch") thin a thin x$ of an analysis $c$
receives a channel $italic("ch")$, action $a$, and input state $x$. Its
soundness law requires it to describe every successor of every store in
$conc(x)$ at which the channel holds
(#isathm("ls_step_sound_iff")). @sec:coop-mcp proves the answers true once
for all analyses.

In the example, the answer $1$ holds exactly at stores with $x = y$.
At these stores, $e$ evaluates to $1$, so the analysis's
own assignment of the literal $1$ is sound for $e$ as well
(#isathm("ask_assign_sound")). The proof never mentions the order analysis.

An analysis without analysis globals is written as a _local specification_
(#isatype("local_spec")). It bundles the operations of @sec:calls, each taking
a channel, with a handler #isaconst("ls_query") that answers queries about a
state, so that the analysis can answer the queries of the others.

#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("local_spec")
}

A local specification is sound (#isaconst("sound_local_spec")) if its
concretization is monotone and its operations satisfy their laws whenever
their channels hold (#isathm("sound_local_spec_iff")). Edge and combine follow
the analysis contract (@sec:sound-core), and enter requires entry coverage. The handler's answers about $x$ must hold at
every store in $conc(x)$ where its own channel holds (#isaconst("sound_query")).
This is the analyses' only mutual assumption. Verasco likewise proves
transfers under correct-channel hypotheses @jourdan15[§7], following Astrée
@cousot07astree[§§5.3, 6]; Voblint applies this approach to Goblint's queries.

== Soundness of combined analyses #thy-badge("Voblint_Framework", "MCP_Spec") <sec:coop-mcp>

In the opening example, only Interval asked. If every exchange ran in one
direction, the analyses could be solved one after another. In the program below, however, the exchange runs in both
directions, between the order analysis and Int, at the same program point and
context.

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
#absval(raw(_z("coop-mutual-int").at(4).split("intervals:").at(1).split(";").at(0))),
and the check is #verdict-chip(_z("coop-mutual-int").at(3)). The order analysis
alone cannot compare a variable with a constant and reports
#verdict-chip(_z("coop-mutual-order").at(3)). Together, at both assignments to
`y`, the order analysis asks Int whether $x$ is at most the assigned constant
and records the pair $(x, y)$ on both branches. At `z = (x <= y)` Int asks
#isaconst("EvalInt") $(x <= y)$, the order analysis answers $1$, and the check
is #verdict-chip(_z("coop-mutual-both").at(3)) (claims
#claim-ref("coop-mutual-*")).

The solver works on a single product state per node and context. This state
(#isatype("mcp_st")) has one field per shipped analysis, of which a run uses
the selected ones (@fig:mcp-combine). Order, join, and widening act field by
field (#isatype("analysis_product")); transfers may query the other fields. The product describes a store if every
selected field does, so its concretization $conc_M$ (#isaconst("mcp_gamma")) is
the intersection of the selected fields' concretizations.

#figure(
  {
    set text(size: 7.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let lab(body) = text(size: 7pt, fill: vb.muted, body)
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
    $italic("ch")$, drawn above the band of components.],
) <fig:mcp-combine>

Each selected analysis runs as a _component_ on its own field of the product
state (@fig:mcp-combine). Writing one field leaves what every other field
describes unchanged (#isathm("field_frame")), so the soundness argument of one
component does not depend on what the others write. The combination runs the
components in turn, gives each the same channel, and answers queries by
meeting the answers of their handlers (#isaconst("mcp_combine")). If every
component is sound, the combination is sound for the intersection of their
concretizations (#isathm("mcp_combine_sound")). For Voblint's analyses:

#theorem(name: [Sound combination of selected analyses], isa: "mcp_comp_sound")[
  For any program $p$ and any nonempty list of distinct selected analyses,
  their combination is a sound local specification for the intersection of
  the selected concretizations.
]

The channel that the theorem assumes comes from the combination itself. The
combined handler, run on the current state, answers every query truthfully for all
stores that state describes (#isathm("ls_channel_sound")). Every selection of
analyses thus yields one analysis that meets the contract of @sec:sound-core
(#isathm("dg_spec_of_contract")). These laws are local, however. They speak
about one edge or one call at a time, not about which states reach a node or in
which context. The equations of @ch:equations connect these local
laws. They link the state of each node and context to the states of its
predecessors and of the calls that reach it. Every post-solution of these
equations then describes all stores that executions bring to each node in each
context.
