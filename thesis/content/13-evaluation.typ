#import "../lib/code.typ": *
#import "../lib/stats.typ": stat, stat-percent, stat-sum
#import "../lib/alignment.typ": alignment, alignment-count
#import "../lib/claims.typ": (
  claim-check, claim-ref, claim-snapshot, claim-timed-out, snapshot-verdict,
)
#import "../lib/theme.typ": vb

= Evaluation <ch:evaluation>

Each section below answers one question of @sec:rqs, gives the evidence and
its kind, and states what the evidence does not show. The chapter closes with
the relation to Goblint, the evidence the thesis does not supply, and the
design constraints the formal statements exposed.

The kinds of evidence differ in strength. A _machine-checked_ result is an
Isabelle theorem and holds for every input its statement ranges over, under its
premises. An _evaluated_ result is an Isabelle lemma proved by `eval`, which
runs the generated code of a concrete solve: Isabelle checks it, but it trusts
the code generator and concerns one input. An _executable_ result records that
one program, run at one configuration, produces one answer, and it also
exercises the parser and renderer outside the theorem (@sec:trust-boundary). An
_illustrative_ result, such as a screenshot, lets a reader inspect the others
and adds no guarantee. A _repository measurement_ supports statements about
size, a _source inspection_ statements about structure. An _argument_ is
reasoning no theorem checks, and we mark it where a claim rests on one.

== Is the analysis sound from source executions to verdicts? <sec:eval-rq1>

Can soundness be machine-checked from source executions to the verdicts of
the exported executable, and which premises and trusted components remain? It
can, for partial correctness: the theorem covers every report the analyzer
returns, with no termination premise, and rests on a trusted toolchain below
the exported constant.

_Evidence: machine-checked._ #isathm("run_voblint_source_sound")
(@sec:headline) is stated once for every domain, global update rule and
context policy that #isaconst("run_voblint") accepts, and about the constant
that #isacmd("export_code") emits (@sec:codegen). Its chain starts at the
forward simulation #isathm("csim_star") from source runs to graph runs
(@sec:csim) and ends at the verdict semantics of @sec:verdicts, where `PROVED`,
`REFUTED` and `DEAD` are constrained and `UNKNOWN` is not. The premises can be
met together: @sec:nonvacuity instantiates the theorem on concrete programs
with every premise discharged. The oracle audit below shows which theorems of the
chain rest on an oracle.

_Limits._ The result is partial correctness. The analyzer answers only where
its solve returns, and termination is not proved for every program:
#isathm("certificate_demo_full_certificate") evaluates one solve to completion
inside Isabelle, and regression programs exist whose solves do not finish
(@sec:termination). The reduction of the Int product is a second place where
the executable may fail to return: in the fixpoint mode, which the analyzer
uses, the generated code iterates until the value stops changing, and that it
stops is not proved (@sec:reduced-product). The delivered guarantee also trusts the parser, the code
generator, the compilers, runtimes and renderer of @sec:trust-boundary, which
are tested (@sec:eval-corpus) and proved nowhere. Whether #isaconst("pstep") models the
intended language is argued in @sec:vimp-vs-c and cannot be proved from the
same definitions. A verdict about a VIMP program does not transfer to a C
program with the same text.

=== Size of the proved and the unverified parts

_Evidence: repository measurement._ The theories under `src/` contain
#stat("isabelle.lines") physical lines in #stat("isabelle.theories") files:
semantics and compiler #stat("isabelle.directories.Program_Model")\; framework
and value lattices #stat("isabelle.directories.Abstract_Interpreter")\; the
analyses, with the generic transfer, routing and result theories they share,
#stat("isabelle.directories.Analyses")\; examples and witnesses
#stat("isabelle.directories.Examples")\; executable surface
#stat("isabelle.directories.Executable_Surface"). The count includes comments,
document text (about #stat-percent("isabelle.doc", "isabelle.lines")), and the
generated per-domain assembly theories. The framework figure includes the
lattice of every value domain, including the relational one, because these
theories live beside the generic lattice constructions. It excludes the vendored solver, of
which Voblint's sessions import #stat("solver.used.theories") of
the #stat("solver.theories") theories of its `TD` session. The analyzer that runs is the
#stat("generated_ocaml")-line generated OCaml module. Around it lie
#stat("handwritten_ocaml") lines of handwritten OCaml under `cli/`, the
unverified part this question asks about; the count excludes the lexer and parser
specifications, which a script generates from a grammar description, and the
page's JavaScript.

Two more figures show how much material a review of definitional adequacy must cover. The
source semantics over which the theorem's premises quantify is defined in
#stat("semantics.theories") theories of #stat("semantics.lines") lines, among
them the #stat("semantics.pstep_rules") rules of #isaconst("pstep")\; the
conclusion additionally uses the collecting semantics and the report and
verdict semantics (#isaconst("report_sem"), #isaconst("verdict_stores")),
defined elsewhere. The numbers locate the
material and do not measure original proof work. We draw no comparison with other
projects: reported proof-to-code ratios, such as that of
#cite(<franceschino21>, form: "prose"), depend on language, automation, and
scope.

=== Oracle audit

#let _facts = json("/shared/generated/facts.json").facts
// Rule cases such as `pstep.Assign` share their inductive's proof; only whole
// theorems are audited.
#let _audited = _facts.keys().filter(n => not n.contains(".")).sorted()
#let _oracles(name) = _facts.at(name).at("oracles", default: none)
#let _unexported = _audited.filter(n => _oracles(n) == none)

For the main theorems, supporting lemmas of the proof chain, and seven
witnesses and counterexamples, the dependence on oracles is
exported from the built session by Isabelle's #isacmd("thm_oracles")
(@tab:oracles-audit). A `sorry` would appear there as Pure's skip-proof oracle,
and a proof by `eval` as the code generator's evaluation oracle.
#if _unexported.len() > 0 [
  #text(fill: vb.unproved)[TODO: the oracle audit is not exported yet; run
    `pixi run thesis-facts-write` against a built session.]
] else if _audited.all(n => _oracles(n).len() == 0) [
  None of the audited theorems depends on an oracle.
] else [
  Of the audited theorems, only
  #_audited.filter(n => _oracles(n).len() > 0).map(isathm).join(", ", last: ", and ")
  depend on an oracle, the code generator's evaluation oracle: they concern
  fixed programs and prove facts about them by `eval`.
]
The audit covers only the theorems listed. The example theories contain
#stat("eval_witnesses") occurrences of `by eval`, and every witness proved that
way inherits the code generator's oracle whether or not it is listed.

#figure(
  table(
    columns: 2,
    align: (left, left),
    stroke: none,
    table.hline(),
    [*theorem*], [*oracles reported by* #isacmd("thm_oracles")],
    table.hline(stroke: 0.5pt),
    ..for n in _audited {
      let o = _oracles(n)
      (
        isathm(n),
        if o == none { [not exported] } else if o.len() == 0 { [none] } else {
          o.map(raw).join(", ")
        },
      )
    },
    table.hline(),
  ),
  caption: [Oracle audit of the main theorems, supporting lemmas of the proof
    chain, and seven witnesses and counterexamples, exported from the built
    session.],
) <tab:oracles-audit>

=== Tests of the unverified parts <sec:eval-corpus>

_Evidence: executable._ The parts outside the theorem are tested: a regression
corpus runs the analyzer end to end, and property tests exercise the frontend.
The corpus holds #stat("corpus.cases") VIMP fixtures in
#stat("corpus.groups") groups. Each fixture states its command-line flags and
the verdict expected at each check. Cases in `precision/` must obtain a
definite answer. In `soundness/`, the program has executions on both sides of
the check, so `UNKNOWN` is the only sound answer. In `known-imprecision/`, the
concrete result is fixed but the abstraction cannot establish it, and the
header names the mechanism that loses the information; these two categories
separate genuine variation among executions from lost abstract information.
The remaining #stat("corpus.kinds.other") fixtures pin output other than a
definite verdict: snapshots of the rendered graph or state, rejection of
malformed input, and solves expected not to finish within their time limit.
The runner matches results by source line, which tests the position
bookkeeping of @sec:ocaml-boundary, and distinguishes a missing report row
from a `DEAD` one, so a check the compiler dropped cannot pass as proved
unreachable. Some fixtures pin the conventions of @tab:vimp-vs-c at the
analyzer's output, for instance
#fixture("10-arithmetic/precision/07-signed_division_totalization.vimp") (truncating
division and remainder) and #fixture("04-globals/precision/01-global_default_zero.vimp")
(zero-initialized globals); they check verdicts, not concrete runs
(@sec:eval-absent).

The parser and the printer of VIMP syntax trees are both generated from one
grammar description. Property tests print randomly generated syntax trees and
require the parser to read back the same tree, and they feed mutated programs
to the parser and require it to finish without a crash. A round trip cannot
detect a misreading of the grammar that parser and printer share, and no test
relates the parsed tree to the program a user meant to write. CI runs the
corpus and the property tests on every pull request and push to the main
branch.

== What does a calling context mean? <sec:eval-rq2>

What does a calling context mean concretely, and when does indexing by context
lose no executions? A context is read off the trace of an activation, and
indexing loses nothing under the totality obligation #oblig("TOTAL").

_Evidence: machine-checked._ The meaning is the relation
#isaconst("activation_context_rel") of @sec:contexts, which reads a context off an
activation trace at the call that created the activation. The
condition is #oblig("TOTAL")
(#isaconst("call_context_total_on")), stated relative to the claim: under the
five coverage obligations, #isathm("activation_collect_sound") bounds the
activation collecting semantics of each context, and
#isathm("node_collect_eq_Union_activation_collect") shows that together they
are the node collecting semantics. The link to the
executable analyzer is #isathm("activation_collect_dg_sound"), which
discharges all five obligations in every domain, for every policy that
proves its routing adequacy and totality (@sec:eq-discharge). _Evidence: executable and illustrative._ The two calls of
`bump` show what indexing changes on one program (@sec:eq-call).

_Limits._ That #oblig("TOTAL") is needed is evaluated on
one program (#isathm("total_dropped_unsound"), @sec:falsification). An
evaluated solve leaves a continuation at bottom when no context is admitted
(#isathm("ov_empty_continuation_bot")); that a run reaches it is argued. The activation collecting semantics is defined over valid traces, and that every
valid trace arises from a graph run is not proved (@sec:valid); soundness needs
only the forward direction.

== Do the ingredients discharge their obligations independently? <sec:eval-rq3>

Do the domain, the context policy and the solver discharge their obligations
independently? They do: each proves facts that mention none of the others, and
one composition theorem covers every configuration.

_Evidence: machine-checked._ A non-relational domain supplies one record of
primitives, #isatype("nonrelational_ops"): its evaluator, comparison
queries, refinement operations, `min` and `max`, and whole-value element
(@sec:instances-supply). Its soundness locale #isalocale("sound_nonrelational_ops")
states facts about integers and stores, none of which mentions a context, a
routing policy or a solver. The guard, the check classifier, the transfer
functions and procedure entry are derived from the record once for every
domain, and #isathm("sound_nonrelational_ops.dg_analysis_execI") discharges
every obligation the executed analysis places on the domain. A domain's
generated registration adds only the premises that belong to the routing
policy, the solver and the initial state. The numeric domains therefore differ
in their primitives and the proofs of their soundness alone. A relational analysis enters
at the next boundary, as a local specification that satisfies
#isaconst("sound_local_spec"), from which generic results derive the analysis
soundness contract #isalocale("analysis_contract") (@ch:cooperation). The routing
obligations are discharged once for all domains
(#isathm("activation_collect_dg_sound")). The solver is consumed only through
the post-solution certificate #isaconst("part_post_solution", thy: "Basics_side")
(@sec:certificate), so the five selectable update rules share one proof
(@sec:update-rules). Analyses combine without reference to one another: each
proves the laws of its local specification against every channel that holds, and
#isathm("mcp_combine_sound") composes any list of independent components
(@ch:cooperation). The assembly interprets #isalocale("dg_analysis")
once per context family for the combination, with the activation list, the
update rule and the call-string depth as parameters (@fig:assembly), and
#isathm("run_voblint_source_sound") covers every resulting configuration.

_Evidence: source inspection._ The lattice of the relational carrier
#isatype("relc") lies beside the numeric value lattices in
#isasession("Voblint_Domain") (@sec:rel-state). The analyses over it
(@sec:relational) live in #isasession("Voblint_Analysis_Relational"), which
builds on #isasession("Voblint_Exec") and does not import
#isasession("Voblint_Nonrelational"), and
#isasession("Voblint_Examples_Relational") runs them through the generator.
No theory of the framework or of the numeric domains refers to these analyses
outside document text.
Making the carrier selectable as the order analysis took three proofs about
its local specification, soundness (#isathm("order_spec_sound")), a single
entry pair (#isathm("single_entry_order_spec")) and sound query answers
(#isathm("relc_qry_sound")), and an entry in the analysis manifest
(@ch:tooling). On the non-relational side, Parity's refinement operations
(#isaconst("parity_refine_ops")) reach the analyzer only as a field of its
record #isaconst("parity_ops"), and no theory outside Parity's own names them.
The statistics tooling measures
directories, not sessions, so we give no line count for either extension.

_Limits._ Precision depends on how the ingredients combine. Which update
rule decides a check depends on the program (@fig:rules-programs), and whether
a call-string depth decides the `down` recursion below depends on widening. Under
the default placement the global unknowns carry only activation seeds. The
shared placement keeps all program globals in one further global unknown
(@sec:mixed-flow). A component of the
combined state cannot read or publish globals, so an analysis with its own analysis globals cannot join it (@sec:coop-limits).

== Are the obligations necessary, and are the theorems informative? <sec:eval-rq4>

Are the obligations necessary, and do the theorems say something about
computed results? Selected obligations are shown necessary by falsification
lemmas, the end-to-end theorem is shown non-vacuous, and precision differences
are proved for single programs.

=== Necessity: falsification lemmas <sec:falsification>

_Evidence: machine-checked and evaluated._ Following
#cite(<kim26regulatory>, form: "prose", supplement: [§6])
#text(fill: vb.unproved)[TODO: check locator.], we separate two
questions. A _non-vacuity_ witness shows that the premises hold together on a
concrete input (@sec:nonvacuity). _Falsification_ evidence removes or weakens
a condition and shows that its consumer then fails on a concrete execution, so
the condition is needed.

Soundness alone is easy to satisfy. #isaconst("verdict_stores") constrains only
decided verdicts, so an analyzer answering `UNKNOWN` at every check satisfies
it at every node and store (#isathm("unknown_everywhere_sound")). Answering
`PROVED` everywhere violates it at the store $x = 1$, which reaches the check
`x == 0` (#isathm("proved_everywhere_unsound")). Any abstract remainder that
returns the constant 1 for $(1 + 2ZZ) mod 2$ violates the statement of
#isathm("congruence_mod_sound") at $-5$
(#isathm("prefix_congruence_mod_unsound"), @sec:eval-1161). Reading a callee's
result at the caller's own context meets #oblig("INIT"), #oblig("INTRA"),
#oblig("CALL"), #oblig("TOTAL") and a weakened #oblig("RETURN") and still
misses a store a run reaches (#isathm("return_at_caller_context_unsound"),
@sec:contract).  A relation
that admits no context lets a claim meet #oblig("INIT"), #oblig("INTRA"),
#oblig("CALL") and #oblig("RETURN") while a store collected at a continuation
lies outside it (#isathm("total_dropped_unsound"), @sec:contract). These are
direct mutations of conditions we selected; they do not show that every
premise of the development is needed. The three counterexamples on concrete
programs prove facts about them by `eval` and are therefore evaluated.


=== A real unsoundness, replayed: Goblint pull request 1161 <sec:eval-1161>

_Evidence: executable, against a defect documented upstream._ Goblint #link("https://github.com/goblint/analyzer/issues/1156")[issue
  1156] reports that Goblint claimed `c % 2 == 1` for $c in {-5, -7}$, although
C's truncating remainder gives $-1$ for both values (@ch:intro). #link("https://github.com/goblint/analyzer/pull/1161")[Pull request
  1161] restricted the cases in which the congruence domain returns a constant
remainder and added the program as regression test
`37-congruence/14-negative.c` @goblint1161. That test marks the first check as
unknown, and the second check, `c % 2 == -1`, as not yet provable.

Our fixture transliterates the test into VIMP, whose remainder also truncates
toward zero. @fig:goblint-1161 shows the result. Congruence alone knows only
$c in 1 + 2ZZ$ and decides neither check. The Int product also knows that $c$
lies in $[-7, -5]$, refutes the first check, and proves the second.

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    show raw: set text(size: 7.5pt)
    let program = json("/shared/generated/vimp-claims.json").at("goblint-1161-int").program
    // Verdict and state of one check, as the registered claim prints them;
    // the product's state is broken at its components.
    let cell(name, cond) = {
      let r = claim-check(name, cond)
      let tone = if r.at(3) == "PROVED" { vb.proved } else if r.at(3) == "REFUTED" {
        vb.unproved
      } else { vb.unstable }
      [#text(fill: tone, weight: "bold", r.at(3)) \ #r.at(4).split("; ").map(raw).join(linebreak())]
    }
    let conds = ("c % 2 == 1", "c % 2 == -1")
    grid(
      columns: (58mm, 1fr),
      column-gutter: 10pt,
      align: horizon,
      listing(program, lang: "c", claim: "goblint-1161-int"),
      table(
        columns: (auto, auto, auto),
        inset: (x: 4pt, y: 3pt),
        table.hline(stroke: 0.5pt),
        [*check*], [*Congruence*], [*Int product*],
        table.hline(stroke: 0.4pt),
        ..conds
          .map(c => (
            raw(c),
            cell("goblint-1161-congruence", c),
            cell("goblint-1161-int", c),
          ))
          .flatten(),
        table.hline(stroke: 0.5pt),
      ),
    )
  },
  kind: image,
  caption: [Goblint's regression test for #link("https://github.com/goblint/analyzer/pull/1161")[pull request 1161] in VIMP, and the
    verdict and state at each check with Congruence alone and with the Int
    product, both without contexts. Concretely, `c % 2` evaluates to $-1$ on
    both executions.],
) <fig:goblint-1161>

The issue documents the defect and the pull request the repair; we did not
re-run a pre-fix Goblint binary, and the example does not show that Voblint is
more precise than current Goblint. The formalization adds the obligation
behind the verdict. For Congruence it is
#isathm("congruence_mod_sound"): the truncating remainder of any two concrete
values lies in the concretization of the abstract remainder. The constant 1 for
$(1 + 2ZZ) mod 2$ violates it at $-5$ (#isathm("prefix_congruence_mod_unsound")),
so the pre-fix answer is not available to the verified domain.

=== Non-vacuity <sec:nonvacuity>

_Evidence: machine-checked, with the concrete solves evaluated._ A theorem
whose premises no configuration meets holds vacuously. The end-to-end
theorem assumes an initial store, a source run, a terminating solve and an
#isaconst("Analysed") answer. As in
#cite(<marmsoler26stark>, form: "prose", supplement: [§9])
#text(fill: vb.unproved)[TODO: check locator.], one small
executable instance shows that the assumptions can be met together.

The instance is the two-call program of @fig:program-to-equations under
Interval, entry-state contexts and warrowing. The theory builds the source run
that returns from `bump(5)` and `bump(4)` and stops before the first check,
and computes the answer by evaluation: both checks `PROVED`.
#isathm("nv_source_certified") instantiates
#isathm("run_voblint_source_sound") with every premise discharged,
and #isathm("nv_check_proved_sound") instantiates
#isathm("run_voblint_check_sound") at the check `a == 6`. For the reachability
claim, a second program sets `x = 1` and guards a check by `x < 0`; the
analyzer marks it `DEAD`, and #isathm("nv_dead_unreached") instantiates
#isathm("run_voblint_dead_check_unreached") to conclude that the collecting
semantics at that node is empty. The runs and the collecting-semantics facts
are proved by simplification. The answers are computed by `eval` and therefore
trust the code generator (@sec:trust-boundary).
The witnesses are informative because the verdicts they constrain are `PROVED`
and `DEAD`, which #isathm("unknown_everywhere_sound") shows to be the
non-trivial ones. Non-vacuity is a property of the premises: the witnesses do
not show that #isaconst("pstep") is the intended semantics of VIMP.

=== Precision witnesses

Each witness below fixes the concrete behaviour first, then shows what one
mechanism keeps or loses, and supports a claim about its program only.

#let _k99 = claim-snapshot("cost-down-k99")
#let _k100 = claim-snapshot("cost-down-k100")

*Contexts.* _Evidence: executable, and evaluated._ The two calls of `bump` are
decided under entry-state contexts but not without them (@sec:eq-unknowns,
@sec:eq-call). #isathm("sign_k2_strictly_more_precise_than_k1_at_g") proves a
strict separation on one program: the Sign value of a parameter at a procedure
entry is strictly lower under call strings of length 2 than under length 1,
with the component values computed by `eval`. The witness uses Sign because
its widening is its join and its narrowing returns the current value, so the
difference cannot come from widening. On one pair of configurations, the gain
from contexts is not proportional to their cost. `down(100)` recurses to `down(0)`, so `n >= 0`
holds at every call. Call strings of length 100 give
#_k100.clusters.len() procedure copies, and the check is
#snapshot-verdict(_k100, "n >= 0"). Length 99 gives #_k99.clusters.len() copies, but one context still
stands for the deepest calls, widening removes the lower bound there, and the
check is #snapshot-verdict(_k99, "n >= 0") (claims #claim-ref("cost-down-k99") and
#claim-ref("cost-down-k100")).

*Update rules.* _Evidence: executable, and evaluated for a two-equation
system._ @fig:rules-programs runs the five update rules of @sec:update-rules on
four programs whose checks hold in every execution. In the first row `p(1)`
and `p(2)` publish to the same entry seed. Warrow joins the two contributions
before widening, so the second looks like growth and the upper bound goes to
$+infinity$. Per-origin warrowing widens each call site's contribution
separately. Each origin writes one constant, so nothing grows.
#isathm("two_writer_slot_warrow_loses_upper_bound") and
#isathm("two_writer_slot_warrow_per_origin_exact") prove the same effect on a
two-equation system by `eval`. No rule is best on every row. In the last row the
fixture header attributes the loss to the recursive call's own contribution:
per-origin warrowing widens it to $-infinity$, `a + 2` may then be zero, and
the division loses all information, while Warrow first joins in `main`'s
argument $-1$ and keeps the lower bound. On the growing recursion the joining
rules give no answer within the limit. The argument grows without bound, so we
expect, without a proof, that their solve diverges (@sec:termination); the
timeout alone does not show this (@sec:trust-boundary). Bounded narrowing, at
its default bound 5, reaches the verdicts of per-origin warrowing on all four
programs.

#let _verdict(name, cond) = {
  if claim-timed-out(name) { return text(fill: vb.unproved)[no answer in 5 s] }
  let r = claim-check(name, cond)
  let tone = if r.at(3) == "PROVED" { vb.proved } else { vb.unstable }
  [#text(fill: tone, r.at(3)) \ #raw(r.at(4))]
}

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    show raw: set text(size: 7.5pt)
    let rules = ("join", "per-origin", "warrow", "warrow-per-origin", "bounded-narrowing")
    let progs = (
      ("two-sites", "x <= 2", [two call sites: `p(1); p(2);`, check `x <= 2` in `p`]),
      ("loop-call", "x < 10", [call in a loop: `g(x)` for `x` from 0 to 9, check `x < 10` in `g`]),
      ("grows", "x >= 0", [growing recursion: `f(x)` calls `f(x + 1)` from `f(0)`, check `x >= 0`]),
      (
        "shrinks",
        "a <= 9",
        [shrinking recursion: `f(a)` calls `f(9 / (a + 2))` while `a < 4`,
          from `f(-1)`, check `a <= 9`],
      ),
    )
    table(
      columns: (1.7fr, 1fr, 1fr, 1fr, 1fr, 1fr),
      align: (
        left + horizon,
        center + horizon,
        center + horizon,
        center + horizon,
        center + horizon,
        center + horizon,
      ),
      stroke: none,
      inset: (x: 3pt, y: 3pt),
      table.hline(stroke: 0.5pt),
      [*program*], [*join*], [*join per origin*], [*warrow*], [*warrow per origin*],
      [*bounded narrowing*],
      table.hline(stroke: 0.4pt),
      ..progs
        .enumerate()
        .map(((i, (key, cond, what))) => (
          what,
          ..rules.map(r => _verdict("rules-" + key + "-" + r, cond)),
          ..if i + 1 < progs.len() { (table.hline(stroke: 0.25pt + luma(190)),) },
        ))
        .flatten(),
      table.hline(stroke: 0.5pt),
    )
  },
  kind: table,
  caption: [Update rules on four programs (Interval, no contexts; bounded
    narrowing at its default bound 5). Each cell is
    the verdict and state of the check row. Every check holds in every execution, so an `UNKNOWN` is lost
    precision. "No answer in 5 s" means the command-line `--timeout 5` stopped
    the solve.],
) <fig:rules-programs>

*The product.* _Evidence: executable._ In @fig:stride2 the reduced product
decides a check that none of its components decides alone.

*Cooperation.* _Evidence: machine-checked by evaluation, and executable._
The two programs of @sec:coop-examples separate the combination from its parts
in each direction. #isathm("coop_demo_needs_both") and
#isathm("order_asks_needs_both") (with #isathm("order_asks_interval_alone") and
#isathm("order_asks_order_alone")) state the verdicts of #isaconst("run_voblint")
for all three activation lists and are proved by `eval`.

#let _sign = claim-check("sign-cannot-bound-magnitude", "total < 100")

*Known imprecision.* _Evidence: executable, except where marked._ Sign has no
magnitude: in the claim #claim-ref("sign-cannot-bound-magnitude"), `total` is 7 in every execution, and at
the check `total < 100` Sign reports #raw(_sign.at(4)) and the verdict
#raw(_sign.at(3)). _Argument:_ no context policy or update rule can change this
verdict, because Sign's comparison query decides nothing for a positive value
against 100, which may lie on either side of it. Intervals lose nonconvex
information, as the multiples of three of @fig:verdict-regions show. Pointwise
stores lose relations between variables (@sec:relational). The order analysis
recovers some of them, within the limits of @sec:coop-limits. A call string of
length $k$ merges paths deeper than $k$, as in `down` above.

_Limits._ Every precision witness concerns one program at fixed configurations, and the evaluated ones trust the code generator. The
development proves no general precision or optimality theorem, and a
separation shown on one program does not order two configurations on all
programs. The concrete behaviour a fixture header states is the author's
reading of the program, and the corpus is tested, not proved.

== Relation to Goblint <sec:eval-goblint>

_Evidence: source inspection._ The comparison targets the framework interface
of Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/"
    + alignment.revision
    + "/src/framework/constraints.ml",
)[constraint generator]
at revision #raw(alignment.revision.slice(0, 8)). There, a call runs the
analysis's `enter`, selects the callee context from the entered state,
publishes the callee entry, and combines the callee's exit with the caller.
Voblint's D/G specification has the same four roles. The project site's
side-by-side comparison
(#link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/#goblint")[site]) lists #alignment.rows.len() Goblint constructs with
their counterparts:
#alignment-count("modeled") are modeled, #alignment-count("simplified")
simplified, and #alignment-count("absent") not modeled. It records
architectural correspondence; no row claims that the two compute the same
fixpoint.

Four simplifications affect how the results transfer to Goblint. The callee
entry is published to a global seed and read back by the entry's local
unknown, where Goblint writes the local entry directly. Under the warrowing
rules the seed itself can be widened, so widening is placed differently; the
direction of that difference is unproved, and no equivalence is claimed. All
program globals share one global unknown, where Goblint keeps one per declared
global; only the shared placement of @sec:mixed-flow, which is not the
default, places program globals there at all. Call targets are resolved statically in every instance.
The activated analyses share one combined state and one query kind, and their
components use no globals, where Goblint's MCP also passes events, spawns and
per-analysis globals and supports many query kinds. There are no threads.

No agreement rate between Voblint's verdicts and Goblint's is reported. The
fixtures adapted from Goblint's regression tests record Goblint's annotations
in their header comments, as prose the test runner does not read, and the
corpus has not been run through Goblint. A measured comparison would need those
annotations in machine-readable form and would have to fix Goblint's
configuration flags per test.

== Evidence not supplied <sec:eval-absent>

No time or memory measurement is reported. The executable keeps the data
representations the proofs use: finite sets are unordered lists and the
solver's value table is a function, so membership, insertion and lookup take
linear time @haftmann10 #text(fill: vb.unproved)[TODO: check that the
  cited work states this.]. _Evidence: measured once on one machine, not a
benchmark._ On a chain of assignments, each doubling of its length multiplied
the running time by about 7, close to the cubic factor of 8
#text(fill: vb.unproved)[TODO: register the command, input and data.], mostly from the
list unions in #isaconst("compile"). A data refinement to red-black trees
would remove these costs. Isabelle's library and the Isabelle Collections
Framework provide such implementations with proofs that they refine the
abstract types @lammich26collections[§1.1]
#text(fill: vb.unproved)[TODO: check locator.]. The refinement would change the
state of the vendored solver, so its proof would have to be redone, while the
rest of the chain uses the solver only through its certificate
(@sec:certificate). It is not done.

No test runs VIMP programs concretely. The development contains no executable
form of #isaconst("pstep"), so the adequacy of the source semantics rests on
the comparison with C11 in @sec:vimp-vs-c alone. The playground
(@sec:ocaml-boundary) is illustrative, and no study measures whether it helps a
reader.

== What the mechanization revealed <sec:revealed>

The findings below are constraints that the formal statements force on the
design, or consequences of the source model that they make explicit. Each item
names the kind of its evidence and the section that argues it.

+ *A per-context statement can hold vacuously at a callee entry* if the callee
  is indexed by the caller's context, which is why #isaconst("activation_context_rel")
  reads the context at the call. _Argument_; the current definitions exclude
  the situation. @sec:why-traces.

+ *Totality is a premise of the per-context theorem*, and for entry-state
  routing it must be discharged against the computed result. _Evaluated_
  on one program (#isathm("total_dropped_unsound")), with one evaluated solve
  (#isathm("ov_empty_continuation_bot")). @sec:contexts, @sec:contract.

+ *A callee's result must be read at the callee's own context.* This fixes the shape of #oblig("RETURN"). _Evaluated_ on one program (#isathm("return_at_caller_context_unsound")). @sec:contract.

+ *Context selection and seed publication must use the same entered value.*
  _Evaluated_ for one call (#isathm("w0_seed_at_entered_frame"),
  #isathm("w0_no_seed_at_caller_frame")). @sec:eq-call.

+ *A right-hand side may publish to a global unknown only once per evaluation*, because
  the update rules record one contribution per origin. _Evaluated_ for the
  buffered system (#isathm("keyed_multiwrite_buffered_terminates")); the
  non-termination of the unbuffered one is expected, neither proved nor
  evaluated. @sec:eq-buffer.

+ *A domain obligation excludes a documented Goblint defect* for all operands,
  where the upstream regression test samples one program. _Machine-checked_
  (#isathm("prefix_congruence_mod_unsound")); the upstream behaviour is
  documented, not re-run. @sec:eval-1161.

+ *A `PROVED` verdict may depend on VIMP's convention for behaviour that C11 leaves undefined*:
  division by zero, and the zeroed locals of a callee (#isaconst("enter_state")),
  which no shipped analysis uses but the theorem would accept. _Source
  inspection_, and executable for the division (claim #claim-ref("pg-division-definite"):
  `quotient == 0` is
  #raw(claim-check("pg-division-definite", "quotient == 0").at(3))).
  @sec:vimp-vs-c, @sec:verdicts.
