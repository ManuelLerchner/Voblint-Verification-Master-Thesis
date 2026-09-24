#import "../lib/code.typ": *
#import "../lib/stats.typ": stat, stat-percent, stat-sum
#import "../lib/alignment.typ": alignment, alignment-count
#import "../lib/claims.typ": claim-check, claim-snapshot, claim-timed-out, snapshot-verdict
#import "../lib/theme.typ": vb

= Evaluation <ch:evaluation>

For each of the four questions of @sec:rqs, this chapter gives the evidence
the thesis offers, its kind, and what it does not show. Later sections relate
the results to Goblint, list evidence the thesis does not supply, collect the
threats to validity, and record design constraints that the formal statements
expose.

== Kinds of evidence

A _machine-checked_ result is an Isabelle theorem. It holds for every input its
statement ranges over, under its stated premises. An _evaluated_ result is an
Isabelle lemma proved by `eval`, which runs the generated code of a concrete
solve; it is checked by Isabelle but trusts the code generator, and it concerns
the one input it evaluates. An _executable_ result records that one program,
run at one configuration, produces one answer; it also exercises the parser and
renderer, which lie outside the theorem (@sec:trust-boundary). An
_illustrative_ result, such as a playground screenshot, lets a reader inspect
the others and adds no guarantee. A _repository measurement_ counts lines and
files with a script and supports statements about size only. A _source
inspection_ reads the theories, their session structure, or Goblint's code, and
supports statements about structure only. An _argument_ is reasoning in the
text that no theorem checks; we mark it where a claim rests on one.

== Is the analysis sound from source executions to verdicts? <sec:eval-rq1>

The first question asks whether soundness can be machine-checked from source executions to
the verdicts of the exported executable, and which premises and trusted
components remain.

_Evidence: machine-checked._ #isathm("run_voblint_certified_source_sound")
(@sec:headline) is stated once for every domain, global update rule and
context policy that #isaconst("run_voblint") accepts, and about the constant
that #isacmd("export_code") emits (@sec:codegen). Its chain starts at the
forward simulation #isathm("csim_star") from source runs to graph runs
(@sec:csim) and ends at the verdict semantics of @sec:verdicts, where `PROVED`,
`REFUTED` and `DEAD` are constrained and `UNKNOWN` is not. The premises can be
met together: @sec:nonvacuity instantiates the theorem on concrete programs
with every premise discharged. The oracle audit below shows that the chain
itself rests on no oracle.

_Limits._ The result is partial correctness. #isaconst("config_terminates") is
a per-program premise, discharged by evaluation where it is discharged at all:
#isathm("certificate_demo_full_certificate") does so for one program at one
configuration, and regression programs exist whose solves do not finish
(@sec:termination). The delivered guarantee also trusts the parser, the code
generator, the compilers, runtimes and renderer of @sec:trust-boundary, which
are tested below and proved nowhere. Whether #isaconst("pstep") models the
intended language is argued in @sec:vimp-vs-c and cannot be proved from the
same definitions. A verdict about a VIMP program does not transfer to a C
program with the same text.

=== Size of the proved and the unverified parts

_Evidence: repository measurement._ The theories under `src/` contain
#stat("isabelle.lines") physical lines in #stat("isabelle.theories") files:
semantics and compiler #stat("isabelle.directories.Program_Model")\; framework
#stat("isabelle.directories.Abstract_Interpreter")\; concrete analyses
#stat("isabelle.directories.Analyses")\; examples and witnesses
#stat("isabelle.directories.Examples")\; executable surface
#stat("isabelle.directories.Executable_Surface"). The count includes comments,
document text (about #stat-percent("isabelle.doc", "isabelle.lines")), and the
generated per-domain assembly theories. It excludes the vendored solver, of
which Voblint's sessions import #stat("solver.used.theories") of
#stat("solver.theories") theory files; @app:theory-map shows the sessions. The analyzer that runs is the
#stat("generated_ocaml")-line generated OCaml module. Around it lie
#stat("handwritten_ocaml") lines of handwritten OCaml under `cli/`, the
unverified part this question asks about; the count excludes the lexer and parser
specifications, which a script generates from a grammar description, and the
page's JavaScript.

Two more figures show how much material a review of definitional adequacy must cover. The
source semantics over which the theorem's premises quantify is defined in
#stat("semantics.theories") theories of #stat("semantics.lines") lines, among
them the #stat("semantics.pstep_rules") rules of #isaconst("pstep")\; the
conclusion additionally uses the collecting semantics and
#isaconst("checks_sound_at"), defined elsewhere. The numbers locate the
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

For the main theorems, supporting lemmas of the proof chain, and three
witnesses, the dependence on oracles is
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
  depend on an oracle, the code generator's evaluation oracle: they are
  witnesses on fixed programs and discharge their premises by `eval`.
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
    chain, and three witnesses, exported from the built session.],
) <tab:oracles-audit>

=== Tests of the unverified frontend

_Evidence: executable._ The parser and the printer of VIMP syntax trees are
both generated from one grammar description. Property tests print randomly
generated syntax trees and require the parser to read back the same tree, and
they feed mutated programs to the parser and require it to finish without a
crash. The regression runner of @sec:eval-corpus matches every reported check
to its source line, which tests the position bookkeeping of @sec:ocaml-boundary.
CI runs both on every pull request and push to the main branch. A round trip
cannot detect a misreading of the grammar that parser and printer share, and no
test relates the parsed tree to the program a user meant to write.

== What does a calling context mean? <sec:eval-rq2>

A calling context needs a concrete meaning, and context indexing needs a
condition under which it loses no executions when one call may be admitted at
several contexts.

_Evidence: machine-checked._ The meaning is the relation
#isaconst("trace_context") of @sec:contexts, which reads a context off an
activation-local trace at the call that created the activation;
#isathm("ov_two_contexts_admitted") gives one concrete call admitted under
two distinct contexts. The condition is #oblig("TOTAL")
(#isaconst("call_context_total_on")), stated relative to the claim: under the
five coverage obligations, #isathm("activation_collect_sound") bounds each
context's bucket, and #isathm("ltr_collect_eq_Union_activation_collect") shows
that the buckets together are the context-free collection. The link to the
executable analyzer is #isathm("activation_collect_dg_sound"), which
discharges all five obligations for every routing policy and domain
(@sec:eq-discharge). _Evidence: executable and illustrative._ The two calls of
`bump` show what indexing changes on one program (@sec:eq-call,
@fig:pg-contexts).

_Limits._ The shipped numeric analyses answer each call with a single
alternative (#isathm("dgs_enter_local_state_st_for_lifted")), so admission at
several contexts is exercised only by a Sign specification outside
#isaconst("run_voblint"). That #oblig("TOTAL") is needed is machine-checked on
one program (#isathm("total_dropped_unsound"), @sec:falsification); an
evaluated analyzer run shows the same failure at the executable level
(#isathm("ov_empty_continuation_bot")). The buckets are defined over valid traces, and that every
valid trace arises from a graph run is not proved (@sec:valid); soundness needs
only the forward direction.

== Do the ingredients discharge their obligations independently? <sec:eval-rq3>

The claim is that the abstract domain, the context policy and the solver
discharge their obligations independently, and that one composition theorem
covers every configuration.

_Evidence: machine-checked._ A domain instance proves facts about integers,
none of which mentions a context, a routing policy or a solver, and generic
results lift them to the analysis contract #isalocale("sound_dg_spec_core")
(@ch:instances). The routing
obligations are discharged once for all domains
(#isathm("activation_collect_dg_sound")). The solver is consumed only through
the post-solution certificate #isaconst("part_post_solution")
(@sec:certificate), so the four selectable update rules share one proof
(@sec:update-rules). The assembly interprets #isalocale("routed_dg_analysis")
once per domain and context family, with the update rule and the call-string
depth as parameters (@fig:assembly), and
#isathm("run_voblint_certified_source_sound") covers every resulting
configuration.

_Evidence: source inspection._ Adding a relational local state needed no
change to the framework. The relational witness of @sec:relational
consists of two theory files in two sessions of its own:
#isasession("Voblint_Analysis_Relational") builds on #isasession("Voblint_Exec")
and does not import #isasession("Voblint_Nonrelational"), and
#isasession("Voblint_Examples_Relational") runs it through the generator. No
framework session imports either; the framework theories mention the witness
only in document text. The statistics tooling measures directories, not
sessions, so we give no line count for the extension.

_Limits._ Precision depends on how the ingredients combine. Which update
rule decides a check depends on the program (@fig:rules-programs), and whether
a call-string depth decides the `down` recursion below depends on widening. In
every selectable analysis the shared component carries only entry seeds;
program globals in a flow-insensitive unknown are proved sound for one program
only (#isathm("mf_ltr_collect_sound"), @sec:mixed-flow). The relational witness
is not selectable through #isaconst("run_voblint"), because the assembly fixes
a store of per-variable values (@sec:engineering).

== Are the obligations necessary, and are the theorems informative? <sec:eval-rq4>

The last question asks which proof obligations are necessary, and whether precision
differences and non-vacuity can be established as theorems about computed
results rather than by testing.

=== Necessity: falsification lemmas <sec:falsification>

_Evidence: machine-checked._ Following
#cite(<kim26regulatory>, form: "prose", supplement: [§6]), we separate two
questions. A _non-vacuity_ witness shows that the premises hold together on a
concrete input (@sec:nonvacuity). _Falsification_ evidence removes or weakens
a condition and shows that its consumer then fails on a concrete execution, so
the condition is needed.

Soundness alone is easy to satisfy. #isaconst("checks_sound_at") constrains only decided
and dead verdicts, so an analyzer answering `UNKNOWN` at every check satisfies
it at every node and store (#isathm("unknown_everywhere_sound")). Answering
`PROVED` everywhere violates it at the store $x = 1$, which reaches the check
`x == 0` (#isathm("proved_everywhere_unsound")). Any abstract remainder that
returns the constant 1 for $(1 + 2ZZ) mod 2$ violates the statement of
#isathm("congruence_mod_sound") at $-5$
(#isathm("prefix_congruence_mod_unsound"), @sec:eval-1161). Reading a callee's
result at the caller's own context meets #oblig("INIT"), #oblig("INTRA"),
#oblig("CALL"), #oblig("TOTAL") and a weakened #oblig("RETURN") and still
misses a store a run reaches (#isathm("return_at_caller_context_unsound"),
@sec:contract). Covering the caller's store and the entered store by different
alternatives excludes the value the run computes
(#isathm("unpaired_entry_cover_unsound"), @fig:unpaired-cover). A relation
that admits no context lets a claim meet #oblig("INIT"), #oblig("INTRA"),
#oblig("CALL") and #oblig("RETURN") while a store collected at a continuation
lies outside it (#isathm("total_dropped_unsound"), @sec:contract). These are
direct mutations of conditions we selected; they do not show that every
premise of the development is needed.

=== Non-vacuity <sec:nonvacuity>

_Evidence: machine-checked, with the concrete solves evaluated._ A theorem
whose premises no configuration meets holds vacuously. The end-to-end
theorem assumes an initial store, a source run, a terminating solve and an
#isaconst("Analysed") answer. As in
#cite(<marmsoler26stark>, form: "prose", supplement: [§9]), one small
executable instance shows that the assumptions can be met together.

The instance is the two-call program of @fig:program-to-equations under
Interval, entry-state contexts and warrowing. The theory builds the source run
that returns from `bump(5)` and `bump(4)` and stops before the first check,
discharges #isaconst("config_terminates") by evaluating the solve, and computes
the answer: both checks `PROVED`. #isathm("nv_source_certified") instantiates
#isathm("run_voblint_certified_source_sound") with every premise discharged,
and #isathm("nv_check_proved_sound") instantiates
#isathm("run_voblint_check_sound") at the check `a == 6`. For the reachability
claim, a second program sets `x = 1` and guards a check by `x < 0`; the
analyzer marks it `DEAD`, and #isathm("nv_dead_unreached") instantiates
#isathm("run_voblint_dead_check_unreached") to conclude that the collecting
semantics at that node is empty. The runs and the collecting-semantics facts
are proved by simplification. The answers and the termination premise are
proved by `eval` and therefore trust the code generator (@sec:trust-boundary).
The witnesses are informative because the verdicts they constrain are `PROVED`
and `DEAD`, which #isathm("unknown_everywhere_sound") shows to be the
non-trivial ones. Non-vacuity is a property of the premises: the witnesses do
not show that #isaconst("pstep") is the intended semantics of VIMP.

=== Precision witnesses: contexts, update rules, the product

Each witness below fixes the concrete behaviour first, then shows what one
mechanism keeps or loses, and supports a claim about its program only.

#let _k99 = claim-snapshot("cost-down-k99")
#let _k100 = claim-snapshot("cost-down-k100")

*Contexts.* _Evidence: executable, and evaluated._ The two calls of `bump` are
decided under entry-state contexts but not without them (@sec:eq-coarse,
@sec:eq-call). #isathm("sign_k2_strictly_more_precise_than_k1_at_g") proves a
strict separation on one program: the Sign value of a parameter at a procedure
entry is strictly lower under call strings of length 2 than under length 1,
with the component values computed by `eval`. The witness uses Sign because
its widening is its join and its narrowing returns the current value, so the
difference cannot come from widening. The gain from contexts is not
proportional to their cost. `down(100)` recurses to `down(0)`, so `n >= 0`
holds at every call. Call strings of length 100 give
#_k100.clusters.len() procedure copies, and the check is
#snapshot-verdict(_k100, "n >= 0"). Length 99 gives #_k99.clusters.len() copies, but one context still
stands for the deepest calls, widening removes the lower bound there, and the
check is #snapshot-verdict(_k99, "n >= 0") (claims `cost-down-k99` and
`cost-down-k100`).

*Update rules.* _Evidence: executable, and evaluated for a two-equation
system._ @fig:rules-programs runs the four update rules of @sec:update-rules on
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
timeout alone does not show this (@sec:trust-boundary).

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
    let rules = ("join", "per-origin", "warrow", "warrow-per-origin")
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
      columns: (1.7fr, 1fr, 1fr, 1fr, 1fr),
      align: (
        left + horizon,
        center + horizon,
        center + horizon,
        center + horizon,
        center + horizon,
      ),
      stroke: none,
      inset: (x: 3pt, y: 3pt),
      table.hline(stroke: 0.5pt),
      [*program*], [*join*], [*join per origin*], [*warrow*], [*warrow per origin*],
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
  caption: [Update rules on four programs (Interval, no contexts). Each cell is
    the verdict and state of the check row, read from the registered claims
    `rules-*`. Every check holds in every execution, so an `UNKNOWN` is lost
    precision. "No answer in 5 s" means the command-line `--timeout 5` stopped
    the solve.],
) <fig:rules-programs>

*The product.* _Evidence: executable._ In @fig:stride2 the reduced product
decides a check that none of its components decides alone.

=== Known imprecision, with mechanisms named

_Evidence: executable, except where marked._ Sign has no magnitude: in the
claim `sign-cannot-bound-magnitude`, `total` is 7 and Sign reports it as
positive, yet `total < 100` stays `UNKNOWN`. No context policy or update rule
can change this, because Sign's comparison has no case for a nonzero constant:
a positive value may lie on either side of 100. Intervals lose nonconvex
information, as the multiples of three of @fig:verdict-regions show. Pointwise
stores lose relations between variables: on `if (x < y)`, Interval learns
nothing at the true branch, evaluated in #isathm("demo_ivl_x_at_branch")
(@sec:relational), and a product of per-variable domains cannot recover the
relation. A call string of length $k$ merges paths deeper than $k$, as in
`down` above.

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

=== The regression suite <sec:eval-corpus>

_Evidence: executable._ The corpus holds #stat("corpus.cases") VIMP fixtures in
#stat("corpus.groups") groups. Each fixture states its command-line flags and
the verdict expected at each check; @app:regressions lists the groups. Cases in `precision/` must obtain a
definite answer. In `soundness/`, the program has executions on both sides of
the check, so `UNKNOWN` is the only sound answer. In `known-imprecision/`, the
concrete result is fixed but the abstraction cannot establish it, and the
header names the mechanism that loses the information; these two categories
separate genuine variation among executions from lost abstract information.
The remaining #stat("corpus.kinds.other") fixtures pin output other than a
definite verdict: snapshots of the rendered graph or state, rejection of
malformed input, and solves expected not to finish within their time limit.
The runner matches results by source line and distinguishes a missing report
row from a `DEAD` one, so a check the compiler dropped cannot pass as proved
unreachable. Some fixtures pin the conventions of @tab:vimp-vs-c at the
analyzer's output, for instance
#fixture("10-arithmetic/precision/07-signed_division_totalization.vimp") (truncating
division and remainder) and #fixture("04-globals/precision/01-global_default_zero.vimp")
(zero-initialized globals); they check verdicts, not concrete runs
(@sec:eval-absent). CI runs the whole corpus on every pull request and push to
the main branch.

_Limits of the evidence on necessity and precision._ Every precision witness concerns one program at
fixed configurations, and the evaluated ones trust the code generator. The
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
Voblint's D/G specification has the same four roles. @app:goblint-alignment
compares #alignment.rows.len() Goblint constructs with their counterparts:
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
global; only the ownership-split example of @sec:mixed-flow places program
globals there at all. Call targets are resolved statically in every instance.
Each run executes one analysis, with no query channel between analyses and no
threads.

No agreement rate between Voblint's verdicts and Goblint's is reported. The
fixtures adapted from Goblint's regression tests record Goblint's annotations
in their header comments, as prose the test runner does not read, and the
corpus has not been run through Goblint. A measured comparison would need those
annotations in machine-readable form and would have to fix Goblint's
configuration flags per test.

== Evidence not supplied <sec:eval-absent>

No measurement of analysis time or memory is reported. The only performance
statement the thesis makes is whether a solve finishes within a fixed limit,
as in @fig:rules-programs. Timings of the executable would mostly measure the
data representations it inherits from the proofs, whose cost grows faster than
linearly already on straight-line programs. Efficiency was outside the scope
of this work.

_Evidence: source inspection of the generated code._ The code generator turns
each defining equation into one target function and keeps the data
representation of the theories @haftmann10, so the asymptotic cost of the
equations carries over. Isabelle's default code setup represents a finite set
as an unordered list, so membership, insertion and removal take time linear in
its size. This affects four places. For $n$ statements, $N$ unknowns and
$v$ variables with an override:

- *Compilation.* #isaconst("compile") unites the edge sets of the two halves of
  a sequence, and the parser nests a statement list to the left. Each union
  inserts the edges of the prefix one by one into a growing set, testing
  membership each time, so compiling a straight-line program costs $O(n^3)$;
  #isaconst("csize") also recomputes the size of the prefix at every level. One
  run compiles the program three times, once for the equations, once for the
  root unknown and once for the readback.
- *Solver.* The vendored solver keeps the called and the stable unknowns as
  such lists and the influence map as an association list
  (#isaconst("fminsert")), so each step costs $O(N)$. Its value table is a
  function, and every update wraps the previous function in one more test, so
  a lookup costs time linear in the number of updates made so far.
- *States.* #isatype("resolved_st_q") keeps its overrides as a list
  (@ch:solving). Join, widening, narrowing and the order test each traverse
  the union of both supports with a lookup per location, $O(v^2)$ per
  operation; equality is two order tests.
- *Readback.* The solved keys form a list, #isaconst("lookup_context") tests
  membership in it, and the report does so for every node and context, which
  costs $O(n dot N)$ per context. No read value is cached, so every lookup
  reruns the readback through the value table.

The edge indexes of the equations are the exception: #isaconst("group_by_key")
files the edges of each node in a red-black tree from Isabelle's library, so a
predecessor lookup is logarithmic.

_Evidence: executable, measured once on one machine with scripts outside the
repository; an observation, not a benchmark._ On a chain of assignments to one
variable, each doubling of the chain from 500 to 2,000 multiplied the
wall-clock time of the analyzer by about 7, near the cubic factor of 8. One compilation
took about a third of the run at 2,000 assignments. The same chain built as a
syntax tree nested to the right, which avoids the cubic union, grew by a
factor of about 4 per doubling up to 4,000 assignments, the quadratic factor.
A chain of procedures, each calling the next, grew by a factor between 2.6 and
4.3 per doubling from 100 to 1,600 procedures.

Removing these costs amounts to a data refinement. Sets and maps keyed by unknowns
would become red-black trees, through the code setups for sets and mappings
that Isabelle's library provides. These need a linear order on unknowns, and
for entry-state contexts that means an order on abstract values. The solver's
value table would become a finite map with a default. That changes the state
of the vendored solver, so its partial-correctness proof would have to be
redone for the map or related to the function by a refinement proof. The rest
of the chain consumes the solver only through the post-solution certificate
(@sec:certificate) and would not change. #isaconst("compile") could accumulate
edges in a list with a proof that the list denotes the same set, and a run
could compile the program once. The readback and the state operations allow
the same treatment: the carrier layer of @ch:solving already proves executable
operations equal to their specifications under readback, and
#isathm("group_lookup_group_by_key") does so for the one tree the equations
use today. None of this is implemented in this work.

The fixtures are small, #stat("corpus.lines") lines over
#stat("corpus.cases") programs, so timing them would not support a claim about
larger programs even after such a refinement, and a throughput comparison with
Goblint would compare different input languages, configurations and checked
properties. The effort the development took is not recorded either: the line
counts above measure size, not person-time or build time.

The adequacy of #isaconst("pstep") rests on the comparison with C11 in
@sec:vimp-vs-c and on the concrete behaviour that fixture headers state. The
development contains no executable form of #isaconst("pstep"), and no test
runs VIMP programs concretely or compares them with a compiled C program, so
a departure from C11 missing from @tab:vimp-vs-c would go unnoticed by every
check in the repository.

The playground (@sec:playground) is illustrative evidence only. No study
measures whether it helps a reader understand a result.

== Threats to validity <sec:eval-threats>

The main threat to construct validity is definitional adequacy: whether
#isaconst("pstep") models the intended language is argued through its
departures from C11 (@sec:vimp-vs-c), and no concrete executor tests the
argument (@sec:eval-absent). The delivered guarantee trusts the parser, the
code generator, the compilers, runtimes and renderer (@sec:trust-boundary), and
every witness proved by `eval` also trusts the code generator's evaluation
oracle (@tab:oracles-audit, @sec:nonvacuity). The theorem is partial
correctness under a per-program termination premise (@sec:termination). The
empirical evidence has limited reach. The corpus is small, written for this
work, and its expected concrete behaviour is the author's reading of each
program (@sec:eval-corpus). Every precision witness and example concerns one
program at fixed configurations (the limits of @sec:eval-rq4), and the
playground is illustrative (@sec:playground). No agreement data with Goblint
exists, and the Goblint defect of @sec:eval-1161 was not re-run
(@sec:eval-goblint). No running time is measured (@sec:eval-absent). The
comparison with prior work rests on a targeted search rather than a
systematic review, so a missed work could narrow the scoped novelty claims
(@ch:related).

== What the mechanization revealed <sec:revealed>

The findings below are constraints that the formal statements force on the
design, or consequences of the source model that they make explicit. Each item
names the kind of its evidence and the section that argues it.

+ *A per-context statement can hold vacuously at a callee entry* if the callee
  is indexed by the caller's context, which is why #isaconst("trace_context")
  reads the context at the call. _Argument_; the current definitions exclude
  the situation. @sec:why-traces.

+ *Totality is a premise of the per-context theorem*, and for entry-state
  routing it must be discharged against the computed result. _Machine-checked_
  (#isathm("total_dropped_unsound")), with one evaluated analyzer run
  (#isathm("ov_empty_continuation_bot")). @sec:contexts, @sec:contract.

+ *Entry coverage must be paired, and a callee's result must be read at the
  callee's own context.* This fixes #isaconst("dgs_enter") as a list of pairs
  and the shape of #oblig("RETURN"). _Machine-checked_
  (#isathm("unpaired_entry_cover_unsound"),
  #isathm("return_at_caller_context_unsound")). @sec:calls, @sec:contract.

+ *Context selection and seed publication must use the same entered value.*
  _Evaluated_ for one call (#isathm("w0_seed_at_entered_frame"),
  #isathm("w0_no_seed_at_caller_frame")). @sec:eq-seed.

+ *A right-hand side may publish to a key only once per evaluation*, because
  the update rules record one contribution per origin. _Evaluated_ for the
  buffered system (#isathm("keyed_multiwrite_buffered_terminates")); the
  non-termination of the unbuffered one is expected, neither proved nor
  evaluated. @sec:eq-buffer.

+ *A domain obligation excludes a documented Goblint defect* for all operands,
  where the upstream regression test samples one program. _Machine-checked_
  (#isathm("prefix_congruence_mod_unsound")); the upstream behaviour is
  documented, not re-run. @sec:eval-1161.

+ *A `PROVED` verdict may depend on behaviour that C11 leaves undefined*:
  division by zero, and the zeroed locals of a callee (#isaconst("enter_state")),
  which no shipped analysis uses but the theorem would accept. _Source
  inspection_, and executable for the division (claim `pg-division-definite`:
  `quotient == 0` is
  #raw(claim-check("pg-division-definite", "quotient == 0").at(3))).
  @sec:vimp-vs-c, @sec:verdicts.
