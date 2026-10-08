#import "../lib/code.typ": *
#import "../lib/stats.typ": stat, stat-percent, stat-sum
#import "../lib/alignment.typ": alignment, alignment-count
#import "../lib/claims.typ": (
  claim-check, claim-ref, claim-snapshot, claim-timed-out, snapshot-cluster-of, snapshot-verdict,
)
#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": verdict

= Evaluation <ch:evaluation>

A machine-checked theorem needs no test of whether it holds. What an
evaluation can still establish is how much the theorem covers, whether it is
strong enough to say something about real answers, how precise the analyzer
is under it, and what the delivered tool adds outside it. The sections follow
these four points, then relate Voblint to Goblint and collect the design
constraints the formal statements exposed.

The kinds of evidence differ in strength. A _machine-checked_ result is an
Isabelle theorem and holds for every input its statement ranges over, under its
premises. An _evaluated_ result is an Isabelle fact proved by `eval`, which
runs the generated code of a concrete solve: Isabelle checks it, but it trusts
the code generator and concerns one input. An _executable_ result records that
one program, run with fixed analysis settings, produces one answer, and it also
exercises the parser and renderer outside the theorem (@sec:trust-boundary). An
_illustrative_ result, such as a screenshot, lets a reader inspect the others
and adds no guarantee. A _repository measurement_ supports statements about
size, a _source inspection_ statements about structure. An _argument_ is
reasoning no theorem checks, and we mark it where a claim rests on one.

== What the theorem covers <sec:eval-scope>

_Evidence: machine-checked._ #isathm("run_voblint_source_sound")
(@sec:headline) connects source executions to the verdicts of the exported
analyzer. It holds for every analysis configuration #isaconst("run_voblint") accepts,
and it is stated about the constant #isacmd("export_code") emits
(@sec:codegen). Its chain runs from the forward simulation #isathm("csim_star")
to the verdict semantics of @sec:verdicts.

Contexts lose no executions. A context is read off an activation trace at the
call that created the activation (#isaconst("activation_context_rel"),
@sec:contexts). Under #oblig("TOTAL"), the per-context collecting semantics
together are the node collecting semantics
(#isathm("node_collect_eq_Union_activation_collect")), and
#isathm("activation_collect_dg_sound") discharges the coverage obligations for
every policy that proves its routing adequacy and totality (@sec:eq-discharge).

The ingredients are verified on their own: a numeric domain through
#isalocale("sound_nonrelational_ops") and
#isathm("sound_nonrelational_ops.dg_analysis_execI") (@sec:instances-supply), a
relational analysis as a local specification (#isaconst("sound_local_spec"),
@ch:cooperation), the routing once for all domains, the solver through its
certificate for all five update rules (@sec:certificate), and a combination of
analyses through #isathm("mcp_combine_sound"). _Evidence: source inspection._ Adding the order analysis took
three proofs about its local specification (#isathm("order_spec_sound"),
#isathm("single_entry_order_spec"), #isathm("relc_qry_sound")) and an entry in
the analysis manifest (@ch:tooling). No theory of the framework or of the
numeric domains refers to it outside document text.

_Limits._ The result is partial correctness about VIMP and rests on a trusted
toolchain (@sec:limitations), whose parts @sec:eval-unverified measures and
tests.

== How strong the theorem is <sec:eval-strength>

A soundness theorem can hold for uninteresting reasons: its premises may never
be met together, or its obligations may be weaker than they look. Following
#cite(<kim26regulatory>, form: "prose", supplement: [§6])
#text(fill: vb.unproved)[TODO: check locator.], we separate two questions. A
_non-vacuity_ witness shows that the premises hold together on a concrete
input. _Falsification_ evidence removes or weakens a condition and shows that
its consumer then fails on a concrete execution, so the condition is needed. A
replayed Goblint defect shows one obligation excluding a real unsoundness.

=== Non-vacuity <sec:nonvacuity>

_Evidence: machine-checked, with the concrete solves evaluated._ A theorem
whose premises are unsatisfiable holds vacuously. The end-to-end
theorem assumes an initial store, a source run, a terminating solve and an
#isaconst("Analysed") answer. As in
#cite(<marmsoler26stark>, form: "prose", supplement: [§9])
#text(fill: vb.unproved)[TODO: check locator.], one small
executable instance shows that the assumptions can be met together.

The instance is the two-call program of @fig:program-to-equations under
Interval, entry-state contexts and warrowing. The theory builds the source run
that returns from `bump(5)` and `bump(4)` and stops before the first check,
and computes the answer by evaluation: both checks #verdict("PROVED").
#isathm("nv_source_certified") instantiates
#isathm("run_voblint_source_sound") with every premise discharged,
and #isathm("nv_check_proved_sound") instantiates
#isathm("run_voblint_check_sound") at the check `a == 6`. For the reachability
claim, a second program sets `x = 1` and guards a check by `x < 0`; the
analyzer marks it #verdict("DEAD"), and #isathm("nv_dead_unreached") instantiates
#isathm("run_voblint_dead_check_unreached") to conclude that the collecting
semantics at that node is empty. The runs and the collecting-semantics facts
are proved by simplification and the answers by `eval`. The witnesses
constrain #verdict("PROVED") and #verdict("DEAD"), the non-trivial verdicts (@sec:falsification).
Non-vacuity is a property of the premises: the witnesses do
not show that #isaconst("pstep") is the intended semantics of VIMP.

=== Necessity: falsification theorems <sec:falsification>

_Evidence: machine-checked and evaluated._ Soundness alone is easy to satisfy. #isaconst("verdict_stores") constrains only
decided verdicts, so an analyzer answering #verdict("UNKNOWN") at every check satisfies
it at every node and store (#isathm("unknown_everywhere_sound")). Answering
#verdict("PROVED") everywhere violates it at the store $x = 1$, which reaches the check
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
premise of the development is needed.


=== A real unsoundness, replayed: Goblint pull request 1161 <sec:eval-1161>

_Evidence: executable, against a defect documented upstream._ @ch:intro opened
with Goblint #link("https://github.com/goblint/analyzer/issues/1156")[issue
  1156], which reports that Goblint claimed `c % 2 == 1` for $c in {-5, -7}$,
although C's truncating remainder gives $-1$ for both values. #link("https://github.com/goblint/analyzer/pull/1161")[Pull request
  1161] restricted the cases in which the congruence domain returns a constant
remainder and added the program as regression test
`37-congruence/14-negative.c` @goblint1161. That test marks the first check as
unknown, and the second check, `c % 2 == -1`, as not yet provable.

Our fixture transliterates the test into VIMP, whose remainder also truncates
toward zero. @fig:goblint-1161 shows the result. Congruence alone knows only
$c in 1 + 2ZZ$ and decides neither check. Int also knows that $c$
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
        [*check*], [*Congruence*], [*Int*],
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

== Precision on concrete programs <sec:eval-precision>

The theorem says nothing about precision, since an analyzer that answers
#verdict("UNKNOWN") everywhere satisfies it (@sec:falsification). What each mechanism gains is therefore shown on
concrete programs. Each witness below fixes the concrete behaviour first, then
shows what one mechanism keeps or loses, and supports a claim about its program
only.

#let _k99 = claim-snapshot("cost-down-k99")
#let _k100 = claim-snapshot("cost-down-k100")

*Contexts.* _Evidence: executable, and evaluated._ The two calls of `bump` are
decided under entry-state contexts but not without them (@sec:eq-call). #isathm("sign_k2_strictly_more_precise_than_k1_at_g") proves a
strict separation on one program: the Sign value of a parameter at a procedure
entry is strictly lower under call strings of length 2 than under length 1,
with the component values computed by `eval`. The witness uses Sign because
its widening is its join and its narrowing returns the current value, so the
difference cannot come from widening. On one pair of analysis settings, the gain
from contexts is not proportional to their cost. `down(100)` recurses to `down(0)`, so `n >= 0`
holds at every call. Call strings of length 100 give
#_k100.clusters.len() procedure copies, and the check is
#snapshot-verdict(_k100, "n >= 0"). Length 99 gives #_k99.clusters.len() copies, but one context still
stands for the deepest calls, widening removes the lower bound there, and the
check is #snapshot-verdict(_k99, "n >= 0") (claims #claim-ref("cost-down-k99") and
#claim-ref("cost-down-k100")).

A context policy decides which calls share an unknown (@fig:eq-policies). A
call string of length one separates the two calls of `wrap` but merges them
again in `scale`, where both arrive from the same call site. Length two and
entry-state routing keep them apart through `scale`. The strict separation
between call-string lengths one and two above is of this kind.

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
    the verdict and state of the check row. Every check holds in every execution, so an #verdict("UNKNOWN") is lost
    precision. "No answer in 5 s" means the command-line `--timeout 5` stopped
    the solve.],
) <fig:rules-programs>

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


*The product.* _Evidence: executable._ In @fig:stride2 Int
decides a check that none of its components decides alone.

#let _le(name) = claim-check(name, "x <= y")

*Cooperation.* _Evidence: machine-checked by evaluation, and executable._ The
program opening @ch:cooperation needs Interval to ask the order analysis. In
the following program the order analysis must ask Interval:

#listing(lang: "c", claim: "coop-le-both", ```
fun main() {
  c = __voblint_nondet_int();
  if (0 < c) { x = 0; y = 10; } else { x = 20; y = 30; }
  __voblint_check(x <= y);
}
```)

Interval joins the branches to #raw(_le("coop-le-interval").at(4)) and reports
#verdict(_le("coop-le-interval").at(3)). The order analysis alone cannot compare a
variable with a constant and reports #verdict(_le("coop-le-order").at(3)).
Together, at `y = 10` the order analysis asks about the state before the
assignment whether $x lt.eq 10$. Interval knows $x = 0$ there and answers $1$,
so the order analysis records the pair $(x, y)$. At `y = 30` it asks whether
$x lt.eq 30$ and records the same pair, which therefore survives the join, and
the check is #verdict(_le("coop-le-both").at(3)). Variants of both programs without
the `__voblint_nondet_int` initializations separate the combination from its
parts in each direction. #isathm("coop_demo_needs_both") and
#isathm("order_asks_needs_both") (with #isathm("order_asks_interval_alone") and
#isathm("order_asks_order_alone")) state the verdicts of #isaconst("run_voblint")
for all three activation lists and are proved by `eval`.

#let _sign = claim-check("sign-cannot-bound-magnitude", "total < 100")

*Known imprecision.* _Evidence: executable, except where marked._ Sign has no
magnitude: in the claim #claim-ref("sign-cannot-bound-magnitude"), `total` is 7 in every execution, and at
the check `total < 100` Sign reports #raw(_sign.at(4)) and the verdict
#verdict(_sign.at(3)). _Argument:_ no context policy or update rule can change this
verdict, because Sign's comparison query decides nothing for a positive value
against 100, which may lie on either side of it. Intervals lose nonconvex
information, as the multiples of three of @sec:verdict-meaning show. Pointwise
stores lose relations between variables (@sec:relational). The order analysis
recovers some of them, within the limits of @sec:coop-catalogue. A call string of
length $k$ merges paths deeper than $k$, as in `down` above.

== The unverified parts <sec:eval-unverified>

=== Size of the proved and the unverified parts

_Evidence: repository measurement._ The theories under #link(repo-blob + "src")[`src/`] contain
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
#stat("handwritten_ocaml") lines of handwritten OCaml under #link(repo-blob + "cli")[`cli/`], the
unverified part; the count excludes the lexer and parser
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
Franceschino et al. @franceschino21, depend on language, automation, and
scope.

=== Tests of the unverified parts <sec:eval-corpus>

_Evidence: executable._ The parts outside the theorem are tested: a
#link(repo-blob + "tests/regression")[regression corpus] runs the analyzer end to end, and property tests exercise the frontend.
The corpus holds #stat("corpus.cases") VIMP fixtures in
#stat("corpus.groups") groups. Each fixture states its command-line flags and
the verdict expected at each check. Cases in `precision/` must obtain a
definite answer. In `soundness/`, the program has executions on both sides of
the check, so #verdict("UNKNOWN") is the only sound answer. In `known-imprecision/`, the
concrete result is fixed but the abstraction cannot establish it, and the
header names the mechanism that loses the information; these two categories
separate genuine variation among executions from lost abstract information.
The remaining #stat("corpus.kinds.other") fixtures pin output other than a
definite verdict: snapshots of the rendered graph or state, rejection of
malformed input, and solves expected not to finish within their time limit.
The runner matches results by source line, which tests the position
bookkeeping of @sec:ocaml-boundary, and distinguishes a missing report row
from a #verdict("DEAD") one, so a check the compiler dropped cannot pass as proved
unreachable. Some fixtures pin the conventions of @tab:vimp-vs-c at the
analyzer's output, for instance
#fixture("10-arithmetic/precision/07-signed_division_totalization.vimp") (truncating
division and remainder) and #fixture("04-globals/precision/01-global_default_zero.vimp")
(zero-initialized globals); they check verdicts, not concrete runs
(@sec:limitations).

The parser and the printer of VIMP syntax trees are both generated from one
grammar description. Property tests print randomly generated syntax trees and
require the parser to read back the same tree, and they feed mutated programs
to the parser and require it to finish without a crash. A round trip cannot
detect a misreading of the grammar that parser and printer share, and no test
relates the parsed tree to the program a user meant to write. CI runs the
corpus and the property tests on every pull request and push to the main
branch.

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

Three simplifications affect how the results transfer to Goblint. The callee
entry is published to a global seed and read back by the entry's local
unknown, where Goblint writes the local entry directly. Under the warrowing
rules the seed itself can be widened, so widening is placed differently; the
direction of that difference is unproved, and no equivalence is claimed. Call
targets are resolved statically in every instance. The activated analyses share one combined state and one query kind, and their
components use no globals, where Goblint's MCP also passes events, spawns and
per-analysis globals and supports many query kinds. There are no threads.
The flow-insensitive placement of @sec:mixed-flow keys program globals by name,
one global unknown per declared global, as Goblint keys its globals; it applies
to all program globals of a run at once.

No agreement rate between Voblint's verdicts and Goblint's is reported. The
fixtures adapted from Goblint's regression tests record Goblint's annotations
in their header comments, as prose the test runner does not read, and the
corpus has not been run through Goblint. A measured comparison would need those
annotations in machine-readable form and would have to fix Goblint's
configuration flags per test.

== What the mechanization revealed <sec:revealed>

Stating the theorems formally forced the following constraints on the design
and made some consequences of the source model explicit. Each item names the
strength of its evidence and the section that develops it.
- A callee is indexed by the context read at its call. Indexed by the caller's
  context, a per-context statement could hold vacuously at a callee entry
  (argument, @sec:why-traces).
- Totality is a premise of the per-context theorem, and entry-state routing
  must discharge it against the computed result (evaluated,
  #isathm("total_dropped_unsound"), #isathm("ov_empty_continuation_bot"),
  @sec:contract).
- A callee's result must be read at the callee's own context, which fixes the
  shape of #oblig("RETURN") (evaluated,
  #isathm("return_at_caller_context_unsound"), @sec:contract).
- Context selection and seed publication must use the same entered value
  (evaluated, #isathm("w0_seed_at_entered_frame"),
  #isathm("w0_no_seed_at_caller_frame"), @sec:eq-call).
- A right-hand side may publish to a global unknown only once per evaluation,
  because the update rules record one contribution per origin (evaluated for
  the buffered system, #isathm("keyed_multiwrite_buffered_terminates"),
  @sec:eq-buffer).
- A domain obligation excludes the Goblint remainder defect for all operands
  (machine-checked, #isathm("prefix_congruence_mod_unsound"), @sec:eval-1161).
- A #verdict("PROVED") verdict may depend on VIMP's conventions for division by zero and
  zeroed callee locals, which C11 leaves undefined (executable, claim
  #claim-ref("pg-division-definite"), @sec:vimp-vs-c).
