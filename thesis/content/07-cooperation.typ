#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/math.typ": *
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": definition
#import "../lib/figures.typ": verdict as verdict-chip

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
#let state(name, loc) = raw(claim-row(name, loc).state)

= How Analyses Cooperate <ch:cooperation>

@ch:analysis-interface fixed what one analysis supplies, a record of
operations whose soundness is proved operation by operation. Its transfers, however, see only the analysis's own state, while
a check may need a fact that one analysis knows and another must use. In the
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
The order analysis is relational. Its state is a set of pairs $(x, y)$, each
meaning that the value of $x$ is at most the value of $y$. After the guards it
holds $(x, y)$ and $(y, x)$, so it knows that $x = y$, but it tracks no value
of `z` and reports #verdict("coop-eq-order", "16:7") too. Neither analysis can
decide the check. Together they can, if Interval's assignment can learn what
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
      msg((0, 2), (1, 2), [contributes $ivl(0, 1)$]),
      msg((2, 2), (1, 2), [contributes $1$], side: right),
      node((1, 3), text(size: 7pt)[$ivl(0, 1) lmeet 1 = 1$], fill: white, inset: 2pt),
      msg((1, 4), (0, 4), [$1$], side: right),
      party((0, 5), [Interval after \ $z = ivl(1, 1)$]),
    )
  },
  kind: image,
  placement: none,
  caption: [One step of Interval and the order analysis at `z = (x == y)` in
    the program above (schematic). Interval's assignment asks #isaconst("EvalInt") $(x == y)$. The channel
    asks the handler of every analysis and gives Interval the meet of their
    contributions. Each analysis updates only its own part
    of the state. The final states match the analyzer run
    #verdict("coop-eq-both", "16:7") with #state("coop-eq-both", "16:7").],
) <fig:mcp-step>

Goblint solves this with its
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/mCP.ml",
)[_master control program_]
(MCP). The activated analyses run side by side, each on its own part of one
combined state, and a transfer may ask all activated analyses a question
through the manager's `ask` function. Goblint has no machine-checked argument that these exchanges are sound. A
proof, however, has a modularity problem. If Interval's assignment is proved
sound using the order analysis's invariant, the two proofs are coupled, every
new pair of analyses needs a new proof, and adding an analysis reopens old
ones. This chapter describes how each analysis instead gets one proof
obligation that does not mention its partners, and why analyses meeting it
combine into one analysis that meets the analysis contract of @sec:sound-core.

== Questions and answers <sec:coop-queries>

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
an analysis that cannot answer a question answers $ltop$ and claims nothing.
If two answers hold at a store, so does their meet, so a question asked of all
analyses can be answered by the meet of their answers. In the example, asked
#isaconst("EvalInt") $(x == y)$ after both guards, Interval answers
$ivl(0, 1)$, which holds at every store, and the order analysis answers $1$.
Their meet is $ivl(0, 1) lmeet 1 = 1$, so $x = y$. Goblint's `MCP.query'` combines answers the
same way.

A transfer may ask several questions. The framework therefore hands it all
answers at once, as a _channel_ $italic("ch")$ of type #isatype("channel"), a function
from queries to answers. A channel _holds_ at a store $s$ if every answer it
gives holds at $s$:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("channel_holds")
}
By the two laws, the channel answering $ltop$ everywhere holds at every store,
and the pointwise meet of two channels that hold at $s$ holds at $s$
(#isathm("query_algebra.channel_holds_inf")).

== Proving an analysis against any channel <sec:coop-channels>

Interval's assignment in @fig:mcp-step uses the wrapper
#isaconst("ask_assign"), which any analysis can put around its assignment
$x := e$. The wrapper asks #isaconst("EvalInt") $e$. When the answer is one
integer $n$, it runs the analysis's own assignment of the literal $n$, and
otherwise the assignment of $e$. At $z := (x == y)$ Interval receives $1$ and
sets $z$ to $ivl(1, 1)$, which is right only if the answer is true. Proving
that from the order analysis's invariant would couple the two proofs.

Voblint instead makes the channel an argument of the transfer and the truth of
its answers a premise of the proof. The transfer
$#isaconst("ls_step") thin c thin italic("ch") thin a thin x$ of an analysis $c$
receives a channel $italic("ch")$ besides the action $a$ and the value $x$
before the edge. Soundness is the condition of @sec:calls with one extra
premise. For every channel $italic("ch")$, every $s in conc(x)$ _at which
$italic("ch")$ holds_, and every $s' in$ #isai("edge_step a s"), we require
$s' in conc(#isaconst("ls_step") thin c thin italic("ch") thin a thin x)$, and
#isathm("ls_step_sound_iff") splits this into one law per kind of edge. In the
example, the premise excludes the stores where $x != y$, at which the answer
$1$ is false. At the others $e$ evaluates to $1$, so the analysis's soundness
for the literal $1$ gives soundness for $e$. One theorem covers every analysis
(#isathm("ask_assign_sound")). Its proof uses only that the answer holds, so it
works with every partner whose answers hold.

An analysis without analysis globals is written as a _local specification_
(#isatype("local_spec"), @fig:local-spec), whose operations each take a
channel, and whose handler #isaconst("ls_query") answers queries about a
state.

#figure(
  {
    show raw.where(block: true): set text(size: 6.5pt)
    thy("local_spec")
  },
  kind: image,
  placement: auto,
  caption: [The declaration of #isatype("local_spec"), lifted from the theory.
    Every operation receives a channel of type #isatype("channel"), and the
    first combine stage receives two.],
) <fig:local-spec>

Soundness of a local specification (#isaconst("sound_local_spec")) asks for a
monotone concretization, which turns the solver's inequalities into inclusions
as in @sec:sound-core, and one law per operation, with one law for the two
combine stages together (#isathm("sound_local_spec_iff")). The edge and combine
laws are the counterparts of the step and combine laws of the analysis contract
(@sec:sound-core), and the enter law that of entry coverage, each assuming that the channels it receives
hold. The new handler law requires the handler's answers about a state $x$ to
hold at every store of $conc(x)$ at which the channel it receives holds
(#isaconst("sound_query")). It is the analysis's promise to its partners, and
the only one they rely on. Beyond the analysis contract, a sound local
specification thus also contains entry coverage and the handler law.

The idea is not new. In Astrée an abstract transfer need only cover concrete
arguments and results that satisfy the constraints of its channels
@cousot07astree[§§5.3, 6]. Verasco, whose channels follow Astrée's and whose
term we adopt, proves each transfer function under the hypothesis that the
channels it receives are correct @jourdan15[§7]. Voblint uses the same form
for Goblint's queries.

== Many analyses over one state <sec:coop-mcp>

The analyses cannot be solved one after another. In the opening example
Interval needs the order analysis's facts at `z = (x == y)`, and in the example
of @sec:eval-precision the order analysis needs Interval's, at the same program
point and context. The framework therefore runs all selected analyses as a
single analysis whose abstract state is a tuple with one field per analysis.
At `z = (x == y)` this state is the pair of Interval's state, in which $x$ and
$y$ are unbounded, and the order analysis's state $\{x lt.eq y, y lt.eq x\}$.
The solver sees one value per node and context and never looks inside it. The
tuple is ordered, joined and widened field by field (#isatype("analysis_product")),
so each field evolves as it would alone, except that its transfers may ask the
other fields. If one selected field shows that a node is unreachable, the whole
tuple does (#isaconst("mcp_norm")).

The combined state #isatype("mcp_st") has one field per analysis the analyzer
ships, and a run uses the fields of the analyses the user selects
(@fig:mcp-combine). The tuple describes a store if every selected field does:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("mcp_gamma")
}
Here $Gamma$ is the list of concretizations of the selected fields. Each
$gamma_i in Gamma$ reads its own field of $x$, so $gamma_i (x)$ is the meaning
that field contributes.
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
      node((0, -0.9), lab[combined state $x$], stroke: none),
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
      node((2, -0.9), lab[combined state $x'$], stroke: none),
    )
  },
  kind: image,
  placement: none,
  caption: [One step of the combination (schematic). Each component reads its
    own field of the combined state $x$ and writes its own field of $x'$, and
    the components run in turn. All components receive the same channel
    $italic("ch")$ (blue), which the framework builds from $x$ as the meet of the answers of all handlers.],
) <fig:mcp-combine>

We call a local specification that runs on one field a _component_. Each
component reads and writes only its own field, through a _lens_
(#isaconst("lens_of")) that takes the field out of the combined state and puts
a new value back, as Goblint's MCP hands each analysis its own part of the
combined state. A component therefore leaves the concretizations of all other
fields unchanged (#isathm("field_frame")), which makes the components
_independent_ (#isaconst("mcp_independent")). #isaconst("mcp_combine") runs the
components in turn, gives every one the same channel, and meets the answers of
their handlers. If the list of components is non-empty, the components are
independent, and each is a sound local specification, then the combination is
a sound local specification for the intersection of their concretizations
(#isathm("mcp_combine_sound")). #isathm("mcp_comp_sound") applies this to every
non-empty selection of distinct analyses. The components cannot invalidate one
another's guarantees, since each guarantee is about a field no other component
writes, and it holds for any channel that holds, whichever component gave the
answer.

The premise that the channel holds leaves one task to the framework. For every
state $x$ it must build a channel that holds at every store of $conc(x)$. It
asks the combined handler, whose components may ask in turn, and answers a
query that is asked again while it is being answered with $ltop$, as Goblint's
`MCP.query'` does. Every answer of this channel holds
(#isathm("ls_channel_sound")). #isaconst("dg_spec_of") passes this channel to
the operations and turns a sound local specification into a record that meets
the analysis contract (#isathm("dg_spec_of_contract")). The combination of any
non-empty selection of distinct analyses therefore meets the analysis contract, and @ch:equations treats it
like a single analysis.

Checks are decided from the same kind of answers. At a check with condition
$b$, every active analysis answers the question #isaconst("EvalInt") about the
truth value of $b$ from its own part of the solved state, and the analyzer
meets these answers (#isaconst("mcp_answer")). An exact $1$ proves the check,
and an exact $0$ refutes it (#isaconst("mcp_classify")). Several analyses
together can thus decide a check that each alone leaves unknown, as the run
#verdict("coop-eq-both", "16:7") of the opening example shows. The exchange
also works in the other direction, with the order analysis asking Interval
(@sec:eval-precision).

== What a new analysis has to prove <sec:coop-catalogue>

A new analysis joins the combined state by proving the laws of its local
specification, which mention no other analysis. Its field, the lens and the
code that reads its answers are generated from its entry in the analysis
manifest (@ch:tooling), so only its operations and their proofs are written by
hand. There are two routes to these proofs. A numeric domain proves its
primitive operations sound once (#isalocale("sound_nonrelational_ops"),
@sec:instances-supply), and the framework derives the laws from that proof
(#isathm("sound_nonrelational_ops.dg_analysis_execI")). Any other analysis
starts from conservative defaults, a handler that answers $ltop$ and
operations that keep the state at skips, guards, procedure bodies, events and
the first combine stage. These defaults are sound for every concretization (#isathm("sound_conservative_local_spec")). The
analysis then supplies and proves the assignment, the special calls, the
return, enter and the second combine stage, and proves each default it
replaces. The order analysis follows this route. It answers comparisons between
variables it has ordered, asks at assignments, and enters and returns with no
facts (#isathm("order_spec_sound")).

Two limits remain. Components cannot read or publish analysis globals
(@sec:shared-facts), which Goblint's MCP allows by tagging each analysis's
globals with its index. And no theorem guarantees that the combination is more
precise than its components. The opening program and the one in
@sec:eval-precision only show concrete cases where it is.

Each analysis is proved sound against every channel that holds, and the
framework supplies such a channel and runs each analysis on its own field. The
proofs of the analyses therefore stay independent, and adding an analysis needs
one new proof and reopens none.

This completes what the analyses contribute. @ch:domains gave the laws of one
abstract state, @ch:analysis-interface the contract of one analysis, and this
chapter showed that a selection of analyses meets the same contract as one.
None of these chapters mentions contexts, equations or a solver.
@ch:equations builds an equation system over nodes and contexts from the
operations of the combined analysis and discharges the obligations of
@ch:traces for it.
