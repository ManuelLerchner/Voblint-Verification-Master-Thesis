#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, thy-badge
#import "../lib/math.typ": *
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
operations whose soundness is proved operation by operation. Its transfers,
however, see only the analysis's own state, while a check may need a fact that
one analysis knows and another must use. In the program below both guards hold
at the assignment, so $x = y$ and `z` is $1$.

#listing(lang: "c", claim: "coop-eq-both", ```
fun main() {
  i32 x = __voblint_nondet_int();
  i32 y = __voblint_nondet_int();
  if (x <= y) {
    if (y <= x) {
      i32 z = (x == y);
      __voblint_check(z == 1);
    }
  }
}
```)

Interval keeps one range per variable. After the guards, `x` and `y` are
still unconstrained within their kind, so `x == y` evaluates to $ivl(0, 1)$
and the check stays #verdict("coop-eq-interval", "16:7") with
#state("coop-eq-interval", "16:7"). The order analysis is relational. Its
state is a set of pairs $(x, y)$, each meaning that the value of $x$ is at
most the value of $y$. After the guards it holds $(x, y)$ and $(y, x)$, so it
knows that $x = y$, but it tracks no value of `z` and reports
#verdict("coop-eq-order", "16:7") too. Their combination decides the check if
Interval's assignment can use what the order analysis knows at that point
(@fig:mcp-step).

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
      party((0, 0), [Interval \ $x, y$ unconstrained]),
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
    the program above (schematic). Interval's assignment asks #isaconst("EvalInt") $(x == y)$, which values $x == y$ may take. The channel
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
combined state, and a transfer may ask all of them a question through the
manager's `ask` function. No machine-checked argument shows that these
exchanges are sound. If Interval's assignment were proved sound from the order
analysis's invariant, the two proofs would be coupled, and every new analysis
could reopen old proofs. Voblint instead gives each analysis one proof
obligation that does not mention its partners, and analyses meeting it combine
into one analysis that meets the analysis contract of @sec:sound-core.

== Questions and answers #thy-badge("Voblint_Framework", "Analysis_Query") <sec:coop-queries>

The analyses must agree on what a question means and on what an answer
claims. A _query_ asks for a fact about the stores a state describes. This
analysis query differs from the query of a local solver, the unknown it starts
from (@sec:side-effects). Voblint has one kind, named after Goblint's. The query #isaconst("EvalInt") $e$ asks
which integers the expression $e$ may evaluate to. Its answer is a record
(#isatype("int_dom")) of a sign, an interval, a parity and a congruence, lifted
by a bottom and by a top element that claims nothing (#isatype("query_lift")).
An answer $a$ _holds_ at a store $s$ if the value of $e$ in $s$ lies in
$conc(a)$ (#isaconst("eval_holds")). A comparison evaluates to $0$ or $1$, so
the exact answer $1$ to #isaconst("EvalInt") $(x == y)$ says that $x = y$. A
non-relational domain converts between its own values and this record with
the operations #isaconst("answer_ik") and #isaconst("of_answer_ik") of its
interface (@fig:domain-carrier). Answers are restricted to this record. A
domain whose facts it cannot express, such as the exclusion $x != 5$ for an
$x$ in a wide interval, contributes only what the record can say. A
new kind of fact would need a new query or a wider answer type, together with
the two laws below.

Two laws (#isalocale("query_algebra")) let answers from several analyses work
together. The top answer $ltop$ holds at every store, so an analysis that
cannot answer a question answers $ltop$ and claims nothing. If two answers
hold at a store, so does their meet, so a question asked of all analyses can
be answered by the meet of their answers. In the example, Interval answers
$ivl(0, 1)$ after both guards and the order analysis answers $1$, and their
meet $ivl(0, 1) lmeet 1 = 1$ says that $x = y$. Goblint's `MCP.query'`
combines answers the same way, as formalized by Apinis @apinis14[§5.5].

A transfer may ask several questions. The framework therefore hands it all
answers at once, as a _channel_ $italic("ch")$ (#isatype("channel")), a
function from queries to answers. A channel _holds_ at a store $s$ if every
answer it gives holds at $s$ (#isaconst("channel_holds")). By the two laws, the
channel answering $ltop$ everywhere holds at every store, and the pointwise
meet of two channels that hold at $s$ holds at $s$
(#isathm("query_algebra.channel_holds_inf")).

== Proving an analysis against any channel #thy-badge("Voblint_Framework", "MCP_Spec") <sec:coop-channels>

Interval's assignment in @fig:mcp-step evaluates its right-hand side with
#isaconst("aeval_ask"), the abstract evaluation every non-relational analysis
uses. For an expression $e$ other than a literal, it asks #isaconst("EvalInt")
$e$ of all analyses, itself included, and meets the answer with its own value
of $e$. @sec:coop-mcp shows why a question to itself does not loop. At $z := (x == y)$
Interval receives $1$, meets it with its own $ivl(0, 1)$, and sets $z$ to
$ivl(1, 1)$, which is right only if the answer is true.

Voblint makes the channel an argument of the transfer and the truth of its
answers a premise of the proof. The transfer
$#isaconst("ls_step") med ell med italic("ch") med a med x$ of an analysis
$ell$ receives a channel $italic("ch")$ besides the action $a$ and the value
$x$ before the edge. Soundness is the condition of @sec:calls with one extra
premise, that $italic("ch")$ holds at the store. For every channel,
$
  s in conc(x) and #isaconst("channel_holds") med italic("ch") med s and s' in #isai("edge_step a s")
  ==> s' in conc(#isaconst("ls_step") med ell med italic("ch") med a med x),
$
which #isathm("ls_step_sound_iff") splits into one law per kind of edge. In the
example, the premise excludes the stores where $x != y$, at which the answer
$1$ is false. At the others the value of $e$ lies in both the answer and the
analysis's own value, hence in their meet. This argument covers every
non-relational analysis and every partner whose answers hold
(#isathm("aeval_ask_sound")). The premise that the channel holds is the one
left open by the evaluation and refinement laws of @sec:domain-forward and
@sec:branches.

An analysis without analysis globals is written as a _local specification_
(#isatype("local_spec")). It has the operations of @fig:dg-spec, and each
operation takes a channel. The first combine stage takes two, one that holds
at the caller's store and one that holds at the callee's exit store. Its
handler #isaconst("ls_query") answers queries about a state.

Soundness of a local specification (#isaconst("sound_local_spec")) asks for a
monotone concretization and one law per operation
(#isathm("sound_local_spec_iff")). The edge and combine laws are the
counterparts of the step and combine laws of the analysis contract
(@sec:sound-core), and the enter law matches entry coverage, each assuming
that its channels hold. The new handler law requires the handler's answers
about a state $x$ to hold at every store of $conc(x)$ at which the channel it
receives holds (#isaconst("sound_query")). It is the only law about an
analysis that its partners rely on.

Astrée and Verasco use the same idea. In Astrée an abstract transfer only has
to cover concrete arguments and results that satisfy the constraints of its
channels @cousot07astree[§§5.3, 6]. Verasco, whose channels are inspired by
Astrée's and whose term we adopt, proves each transfer function under the
hypothesis that the channels it receives are correct @jourdan15[§7]. Voblint
uses the same form for Goblint's queries.

== Many analyses over one state #thy-badge("Voblint_Framework", "MCP_Spec") <sec:coop-mcp>

The analyses cannot be solved one after another, since each may need the
other's facts at the same program point and context. Interval needs the order
analysis's facts at `z = (x == y)`, and to record $x <= y$ where $y$ is
assigned a constant, the order analysis needs a numeric bound on $x$. The
framework
therefore runs all selected analyses as a single analysis whose abstract state
is a tuple with one field per analysis. At `z = (x == y)` this state pairs
Interval's state, in which $x$ and $y$ are unconstrained, with the order
analysis's state $\{x lt.eq y, y lt.eq x\}$. The tuple is ordered, joined, and widened field by field
(#isatype("analysis_product")), so each field evolves as it would alone,
except that its transfers may ask the other fields. If one selected field
shows that a node is unreachable, the whole tuple does
(#isaconst("mcp_norm", thy: "MCP_Carrier")).

The combined state #isatype("mcp_st") has one field per analysis the analyzer
ships, and a run uses the fields of the analyses the user selects
(@fig:mcp-combine). The tuple describes a store if every selected field does,
$conc(x) = inter.big_(gamma_i in Gamma) gamma_i (x)$ (#isaconst("mcp_gamma")),
where $Gamma$ lists the concretizations of the selected fields and each
$gamma_i$ reads its own field of $x$.

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
(#isaconst("lens_of")), as Goblint's MCP hands each analysis its own part of
the combined state. A component therefore leaves the concretizations of all
other fields unchanged (#isathm("field_frame")). #isaconst("mcp_combine") runs
the components in turn, gives every one the same channel, and meets the
answers of their handlers. If the list of components is nonempty, the
components are independent in this sense, and each is a sound local
specification, then the combination is a sound local specification for the
intersection of their concretizations (#isathm("mcp_combine_sound")), and
#isathm("mcp_comp_sound") applies this to every nonempty selection of distinct
analyses. Distinctness matters because two copies of one analysis would write
the same field, so neither would leave the other's concretization unchanged.
The analyzer meets both conditions, because #isaconst("run_voblint") answers
an empty selection or a repeated analysis with
#isaconst("Invalid_Activation") before it compiles the program
(@sec:report).

The framework therefore has to build, for every state $x$, a channel that
holds at every store of $conc(x)$. It asks the combined handler, whose
components may ask in turn, and answers $ltop$ to any query that is asked again
while it is being answered, as Goblint's `MCP.query'` does. It also stops at
a fixed nesting depth, where the logic reads the answer as $ltop$ and the
generated code aborts. Every answer of this channel holds
(#isathm("ls_channel_sound")). The argument looks circular, since the handler
law assumes a channel that holds and the channel is built from the handlers.
Induction on the remaining depth makes it well founded. An answer cut off at a
cycle or at the depth bound is $ltop$ and holds trivially. Any other answer
comes from a handler whose own questions are answered one level deeper, where
they hold by induction, so the handler law makes the answer hold. Passing this channel to the
operations turns a sound local specification into a record that meets the
analysis contract (#isathm("dg_spec_of_contract")). The combination of any
nonempty selection of distinct analyses therefore meets the analysis contract,
like a single analysis.

Checks are decided from the same kind of answers. At a check with condition
$b$, every active analysis answers #isaconst("EvalInt") about the truth value
of $b$ from its own part of the solved state, and the analyzer meets these
answers (#isaconst("mcp_answer", thy: "MCP_Carrier")). A non-relational
analysis answers with the three-valued evaluation of @sec:queries. An exact $1$ proves the
check, and an exact $0$ refutes it
(#isaconst("mcp_classify", thy: "MCP_Carrier")). Several analyses together
can thus decide a check that each alone leaves unknown, as the run
#verdict("coop-eq-both", "16:7") of the opening example shows.

== What a new analysis has to prove <sec:coop-catalogue>

A new analysis joins the combined state by proving the laws of its local
specification, which mention no other analysis. It also needs a field in the
combined state #isatype("mcp_st") and the lens onto it, which are ordinary
theory text checked by Isabelle like the rest. A non-relational domain instantiates the class #isalocale("kind_int_domain")
(@sec:domain-contract), and one generic proof derives the laws for every
instance (#isathm("nonrel_spec_sound")). Any other analysis starts from
conservative defaults, a handler that answers $ltop$ and operations that keep
the state at skips, guards, procedure bodies and events, which are sound for
every concretization. The default first combine stage keeps the caller's
state. The analysis then supplies the assignment, the special calls, the
return, enter, and the second combine stage. It proves each operation it
supplies, and the combine law for its second stage after the default first
one, since that law concerns both stages together
(#isathm("sound_conservative_local_spec")). The order analysis
also replaces the default at guards, answers comparisons between variables
it has ordered, asks at assignments, and returns with no facts
(#isathm("ord_spec_sound")).

Components cannot read or publish analysis globals (@sec:shared-facts). The
flow-insensitive placement of @sec:mixed-flow wraps the whole combination and
adds analysis globals for the program globals itself. Goblint's MCP, in
contrast, lets each analysis keep analysis globals of its own, tagged with its
index. No
theorem guarantees that the combination is more precise than its components,
and programs such as the opening one only show concrete cases where it is.

Since each analysis is proved sound against every channel that holds, adding
an analysis needs one new soundness proof and leaves the soundness proofs of
the existing analyses unchanged. The laws so far mention no
contexts, equations, or solver. @ch:equations builds an equation system over
nodes and contexts from the operations of the combined analysis and
discharges the obligations of @ch:traces for it.
