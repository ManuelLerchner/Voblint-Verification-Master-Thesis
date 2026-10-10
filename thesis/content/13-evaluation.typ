#import "../lib/code.typ": *
#import "../lib/stats.typ": stat
#import "../lib/claims.typ": (
  claim-check, claim-ref, claim-snapshot, claim-timed-out, snapshot-verdict,
)
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": verdict

= Evaluation <ch:evaluation>

@ch:results proved that every report #isaconst("run_voblint") returns is
sound. A machine-checked theorem does not need testing to show that it holds, but it can
hold for uninteresting reasons. Its premises may never be met together, its
obligations may be weaker than they look, or it may exclude only errors that
no real analyzer makes. Following
#cite(<kim26regulatory>, form: "prose", supplement: [§6]), this chapter first asks two
questions about the theorem: whether its premises can hold together, and
whether its obligations exclude real errors. It then shows on concrete programs what precision the
analyzer reaches under the theorem, and how the code outside the theorem is
tested.

The evidence differs in strength. A _machine-checked_ result is an Isabelle
theorem and holds for every input its statement ranges over, under its
premises. An _evaluated_ result is an Isabelle fact proved by `eval`, which runs
the generated code of a concrete solve: Isabelle checks it, but it trusts the
code generator and concerns one input. An _executable_ result records that one
program, run with fixed analysis settings, produces one answer. Its run also
passes through the parser and renderer outside the theorem
(@sec:trust-boundary). A _source inspection_ or _repository measurement_
supports statements about the structure or size of the development.

== Non-vacuity #thy-badge("Voblint_Examples", "Example_Non_Vacuity") <sec:nonvacuity>

_Evidence: machine-checked, with the concrete solves evaluated._ A theorem
whose premises are unsatisfiable holds vacuously. The end-to-end
theorem assumes an initial store, a source run, and an
#isaconst("Analysed") answer, which the analyzer gives only if its solve
terminates.
#cite(<marmsoler26stark>, form: "prose", supplement: [§9]) shows with one small
executable instance that the locale assumptions of a formal model can be
satisfied. We use the same kind of instance for the premises of the end-to-end
theorem.

The instance is the two-call program of @fig:program-to-equations under
Interval, entry-state contexts, and warrowing. The theory builds the source run that returns from `bump(5)` and `bump(4)` and stops before the first check.
It computes the answer by evaluation: both checks are #verdict("PROVED").
#isathm("nv_source_certified") instantiates
#isathm("run_voblint_source_sound") with every premise discharged,
and #isathm("nv_check_proved_sound") instantiates
#isathm("run_voblint_check_sound") at the check `a == 6`. For the reachability
claim, a second program sets `x = 1` and guards a check by `x < 0`; the
analyzer marks it #verdict("DEAD"), and #isathm("nv_dead_unreached") instantiates
#isathm("run_voblint_dead_check_unreached") to conclude that the collecting
semantics at that node is empty. The source runs are proved by rule application, and the compiled graphs and the answers are proved by `eval`. The instances
cover a definite truth verdict, #verdict("PROVED"), and the reachability
verdict #verdict("DEAD").

== Do the obligations exclude real errors? <sec:eval-1161>

_Evidence: machine-checked, and executable against a defect documented
upstream._ The coverage contract and the domain obligations are long, so a
reader may ask whether each is needed. For two coverage conditions the
theories give a counterexample. Reading a callee's result at the caller's
context meets the remaining obligations (#isathm("ret_weak_obligations")) but
misses a store a run reaches (#isathm("return_at_caller_context_unsound")).
Dropping #oblig("TOTAL") admits a claim that meets the others
(#isathm("tot_weak_obligations")) but misses a store collected at a
continuation (#isathm("total_dropped_unsound"), @sec:contract). These are conditions we
selected, so they do not show that every premise of the development is needed.

A domain obligation, in turn, excludes a defect that occurred in Goblint.
@ch:intro opened with
#link("https://github.com/goblint/analyzer/issues/1156")[issue 1156], in which
Goblint claimed `c % 2 == 1` for $c in {-5, -7}$, although C's truncating
remainder gives $-1$ for both values.
#link("https://github.com/goblint/analyzer/pull/1161")[Pull request 1161]
restricted the cases in which the congruence domain returns a constant
remainder and added the program as regression test `37-congruence/14-negative.c`
@goblint1161, which marks the first check as unknown and the second,
`c % 2 == -1`, as not yet provable.

In Voblint, the pre-fix remainder cannot be proved sound. The Congruence remainder
must meet #isathm("congruence_mod_sound"): for any two concrete values, their
remainder #isaconst("c_mod") lies in the concretization of the abstract
remainder. #isaconst("c_mod") truncates toward zero, as C11 specifies
(@sec:vimp-vs-c). The pre-fix answer, the constant $1$ for $(1 + 2ZZ) mod 2$,
violates the obligation at $-5$ (#isathm("prefix_congruence_mod_unsound")). The
theorem holds for every abstract remainder that returns this constant. Pull request 1161 reports that Goblint's pre-fix operator returned it, so an
obligation of this form would have rejected that operator as well. Our fixture transliterates the test into VIMP, whose remainder also
truncates toward zero (@fig:goblint-1161). Congruence alone knows only
$c in 1 + 2ZZ$ and decides neither check. Int also knows that $c$ lies in
$[-7, -5]$, refutes the first check, and proves the second.

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

== Precision and cost on concrete programs <sec:eval-precision>

The theorem says nothing about precision, since an analyzer that answers
#verdict("UNKNOWN") everywhere satisfies it (#isathm("unknown_everywhere_sound")). We therefore show on concrete programs what each mechanism gains. Each example below fixes the concrete behavior first, then
shows what one mechanism keeps or loses, and supports a claim about its program
only.

#let _k99 = claim-snapshot("cost-down-k99")
#let _k100 = claim-snapshot("cost-down-k100")

*Contexts.* _Evidence: executable, and evaluated._ @fig:eq-policies showed
which calls each context policy separates. #isathm("sign_k2_strictly_more_precise_than_k1_at_g") proves a
strict separation on one program: the Sign value of a parameter at a procedure
entry is strictly lower under call strings of length 2 than under length 1,
with the component values computed by `eval`. The theorem uses Sign because
its widening is its join and its narrowing returns the current value, so the
difference cannot come from widening.

The gain from contexts is not proportional to their cost. `down(100)` recurses to `down(0)`, so `n >= 0`
holds at every call. Call strings of length 100 give
#_k100.clusters.len() procedure copies, and the check is
#snapshot-verdict(_k100, "n >= 0"). Length 99 gives #_k99.clusters.len() copies, but one context still
stands for the deepest calls, widening removes the lower bound there, and the
check is #snapshot-verdict(_k99, "n >= 0") (claims #claim-ref("cost-down-k99") and
#claim-ref("cost-down-k100")).

*Modularity.* _Evidence: source inspection._ Adding the order analysis required three proofs about its local
specification (#isathm("order_spec_sound"), #isathm("single_entry_order_spec"),
#isathm("relc_qry_sound")), a lattice instance, an entry in the analysis manifest
(@ch:tooling), and a few class instances for the command-line layer. No theory of the framework or of the numeric domains refers to
it outside document text. A new numeric domain proves its lattice laws and its
forward, backward, and query operations sound once
(#isalocale("sound_nonrelational_ops")), and the generic construction derives
its transfer functions and their soundness (@sec:instances-supply).

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
    narrowing at its default bound 5), as on the
    #link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/#globals")[project site],
    where each cell opens its run in the playground. Each cell is
    the verdict and state of the check row. Every check holds in every execution, so an #verdict("UNKNOWN") is lost
    precision. "No answer in 5 s" means the command-line `--timeout 5` stopped
    the solve.],
) <fig:rules-programs>

*Update rules.* _Evidence: executable, and evaluated for a system
with two writers to one global._ @fig:rules-programs runs the five update rules of @sec:update-rules on
four programs whose checks hold in every execution. In the first row `p(1)`
and `p(2)` publish to the same entry seed. Warrow joins the two contributions
before widening, so the second looks like growth, and the upper bound goes to
$+infinity$. Per-origin warrowing widens each call site's contribution
separately. Each origin writes one constant, so nothing grows.
#isathm("two_writer_slot_warrow_loses_upper_bound") and
#isathm("two_writer_slot_warrow_per_origin_exact") prove the same effect on a
system with two writers to one global by `eval`. No rule is best on every row. In the last row the
fixture header attributes the loss to the recursive call's own contribution:
per-origin warrowing widens it to $-infinity$, `a + 2` may then be zero, and
the division loses all information. We attribute Warrow's result to the fact that it joins in `main`'s argument $-1$ first, which keeps the lower bound. On the growing recursion the joining
rules give no answer within the limit. The argument grows without bound, so we
expect, without a proof, that their solve diverges (@sec:termination); the
timeout alone does not show this (@sec:trust-boundary). Bounded narrowing, at
its default bound 5, reaches the verdicts of per-origin warrowing on all four
programs.


#let _z(name) = claim-check(name, "z == 1")

*Refinement inside Int.* _Evidence: executable._ Int combines the four base
domains in one value and refines them against each other (@sec:reduced-product).
In the program below, `q` is $4n + 1$ for some $n in [0, 20]$, so `r` is $1$.

#let _r(name) = claim-check("int-refine-" + name, "r == 1")
#listing(lang: "c", claim: "int-refine-int", ```
fun main() {
  n = __voblint_nondet_int();
  if (0 <= n && n <= 20) {
    q = (12 * n + 3) / 3;
    r = q % 4;
    __voblint_check(r == 1);
    __voblint_check(r > 0);
    __voblint_check(r % 2 == 1);
  }
}
```)

Interval alone bounds `r` to #raw(_r("interval").at(4).split("r=").at(1)) and reports
#verdict(_r("interval").at(3)) at `r == 1`. Congruence alone keeps
`r` in #raw(_r("congruence").at(4).split("r=").at(1)), which admits $-3$ for a
negative `q`, and reports #verdict(_r("congruence").at(3)). Int intersects the
two to #raw(_r("int").at(4).split("r=").at(1)) and proves the check (claims
#claim-ref("int-refine-*")). @fig:goblint-1161 and @fig:stride2 show the same
effect.

*Queries between analyses.* _Evidence: executable, and evaluated._ Separate
analyses refine each other only through queries (@ch:cooperation). In the
following program they do so in both directions:

#listing(lang: "c", claim: "coop-mutual-both", ```
fun main() {
  c = __voblint_nondet_int();
  if (0 < c) { x = 0; y = 10; } else { x = 20; y = 30; }
  z = (x <= y);
  __voblint_check(z == 1);
}
```)

Int alone joins the branches, so `z` lies only in
#raw(_z("coop-mutual-int").at(4).split("intervals:").at(1).split(";").at(0)) and the check is #verdict(_z("coop-mutual-int").at(3)). The order analysis alone
cannot compare a variable with a constant and reports
#verdict(_z("coop-mutual-order").at(3)). Together, at both assignments to `y`
the order analysis asks Int whether $x$ is at most the assigned constant and
records the pair $(x, y)$ on both branches. At `z = (x <= y)` Int asks the
query #isaconst("EvalInt") $(x <= y)$, the order analysis answers $1$, and the
check is #verdict(_z("coop-mutual-both").at(3)) (claims
#claim-ref("coop-mutual-*")). Int asks at every assignment, and at `z = (x <= y)`
the answer is decisive. On a check of `x <= y` itself, the order analysis
would answer the check directly, though it still needs Int's answers at the
assignments to `y`. On two related programs with Interval in place of Int,
#isathm("coop_demo_needs_both"), #isathm("order_asks_interval_alone"),
#isathm("order_asks_order_alone"), and #isathm("order_asks_needs_both") prove by
`eval`, one direction each, that the check is proved only with both
analyses.

== Tests of the unverified parts <sec:eval-corpus>

_Evidence: executable, and repository measurement._ For Voblint's handwritten
code around the generated analyzer (@sec:trust-boundary), tests are the only
project-local evidence. The theories under
#link(repo-blob + "src")[`src/`] contain #stat("isabelle.lines") physical lines
in #stat("isabelle.theories") files, including comments and document text but excluding generated theories, and
the analyzer that runs is the #stat("generated_ocaml")-line generated OCaml
module. Around it lie #stat("handwritten_ocaml") lines of handwritten OCaml
under #link(repo-blob + "cli")[`cli/`], not counting the lexer, parser, and printer that a
script generates from a grammar description.

A #link(repo-blob + "tests/regression")[regression corpus] runs the analyzer
end to end, and property tests exercise the frontend. Part of the corpus is
adapted from Goblint's regression tests, whose origin the fixture header
records.
The corpus holds #stat("corpus.cases") VIMP fixtures in
#stat("corpus.groups") groups. Each fixture states its command-line flags and
the verdict expected at each check. Cases in `precision/` pin the exact verdict at each
check, which is usually definite. In `soundness/`, the program has executions on both sides of
the check, so #verdict("UNKNOWN") is the only sound answer. In `known-imprecision/`, the
concrete result is fixed, but the abstraction cannot establish it, and the
header names the mechanism that loses the information. The playground's
_Examples_ menu opens every fixture with its settings, so a reader can inspect
its solve and change the analysis parameters.
The remaining #stat("corpus.kinds.other") fixtures pin output other than a
definite verdict: snapshots of the rendered graph or state, rejection of
malformed input, and solves expected not to finish within their time limit.
The runner matches results by source line, which tests the position
bookkeeping of @sec:ocaml-boundary, and distinguishes a missing report row
from a #verdict("DEAD") one, so a check the compiler dropped cannot pass as proved
unreachable. Some fixtures pin the conventions of @tab:vimp-vs-c at the
analyzer's output, for instance
#fixture("10-arithmetic/precision/07-signed_division_totalization.vimp") (truncating
division and remainder). They check verdicts, not concrete runs, since the
development has no executable form of #isaconst("pstep"). #link(repo-blob + "tests/solver-trace")[Golden files] pin the
solver trace (@sec:tracing) of three programs step by step and expose changes in the generated solver's execution order. When
#link(
  "https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/pull/256",
)[pull request 256]
published a call's seed before reading its exit at nodes where one call
returns, as Goblint does at every call, the trace of the running example
(Interval, entry-state contexts, warrowing) shrank from 241 to 155 solver
steps. The playground
replays such a trace on the graph (@fig:replay-still).

The parser is trusted to hand the analyzer the program the user wrote. A
parser bug could make the analyzer report verdicts for a different program. Property tests therefore print random syntax trees built from the constructors exported from Isabelle, the type the generated analyzer receives, and require the parser to read back the same tree. They also require the parser to finish on mutated programs without a crash. A round trip cannot
detect a misreading of the grammar that parser and printer share, and no test
relates the parsed tree to the program a user meant to write. CI runs the
corpus and the property tests on every pull request and push to the main
branch.

Together, these results show that the end-to-end theorem applies to a concrete
run, that two selected coverage conditions cannot simply be dropped, and that
one domain obligation excludes a real defect. Each precision example concerns one
program, the tests reach only what the corpus covers, and none of this shows
that #isaconst("pstep") is the intended
semantics of VIMP (@sec:limitations).
