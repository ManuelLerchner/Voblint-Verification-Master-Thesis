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
analyzer reaches under the theorem and where it ends, and how the code outside
the theorem is tested.

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
#isathm("run_voblint_source_sound") with every premise discharged. Its
conclusion gives a node $v$ that the simulation #isaconst("csim") relates to
the stopped run, at which the run's store reaches $v$, a reported state
describes the store, and $v$ is not #verdict("DEAD"). In the same way,
#isathm("nv_check_proved_sound") instantiates
#isathm("run_voblint_check_sound") at the check `a == 6`. For the reachability
claim, a second program sets `x = 1` and guards a check by `x < 0`; the
analyzer marks it #verdict("DEAD"), and #isathm("nv_dead_unreached") concludes,
from the same report guarantees #isathm("run_voblint_dead_unreached") rests on,
that no store reaches that node. The source runs are proved by rule application, and the compiled graphs and the answers are proved by `eval`. The instances
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

*Contexts.* _Evidence: executable._ @fig:eq-policies showed
which calls each context policy separates.
A nested call separates call strings of length 1 and 2: through
#isaconst("run_voblint"), length 2 proves two checks that length 1 leaves
unknown (#isathm("call_string_depth_verdicts")).

The gain from contexts is not proportional to their cost. `down(100)` recurses to `down(0)`, so `n >= 0`
holds at every call. Call strings of length 100 give
#_k100.clusters.len() procedure copies, and the check is
#snapshot-verdict(_k100, "n >= 0"). Length 99 gives #_k99.clusters.len() copies, but one context still
stands for the deepest calls, widening removes the lower bound there, and the
check is #snapshot-verdict(_k99, "n >= 0") (claims #claim-ref("cost-down-k99") and
#claim-ref("cost-down-k100")).

*Modularity.* _Evidence: source inspection._ Adding the order analysis required
proofs about its local specification and its query (#isathm("ord_spec_sound"),
#isathm("ord_query_sound"), #isathm("single_entry_ord_spec")), a lattice
instance, and its registration in the command-line layer: a constructor of the
#isatype("analysis") datatype, a field of the combined state, and the cases of
the registry proofs. No theory of the framework or of the numeric domains refers to
it outside document text. A new numeric domain instantiates the class
#isalocale("kind_int_domain"), proving its lattice laws and its operations
sound once, and the generic construction derives its transfer functions and
their soundness (#isathm("nonrel_exec_spec_sound"), @sec:instances-supply).

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
    the verdict and state of the check row. Except in the growing recursion,
    every check holds in every execution, so an #verdict("UNKNOWN") there is lost
    precision. "No answer in 5 s" means the command-line `--timeout 5` stopped
    the solve.],
) <fig:rules-programs>

*Update rules.* _Evidence: executable._ @fig:rules-programs runs the five update rules of @sec:update-rules on
four programs. In the first row `p(1)`
and `p(2)` publish to the same entry seed. Warrow joins the two contributions
before widening, so the second looks like growth, and the upper bound goes to
the largest 32-bit value. Per-origin warrowing widens each call site's
contribution separately. Each origin writes one constant, so nothing grows.
Evaluation pins the effect on two producers of one global: warrowing after
the join loses the upper bound, and per-origin warrowing keeps it
(#isathm("two_writer_slot_warrow_loses_upper_bound"),
#isathm("two_writer_slot_warrow_per_origin_exact")).
On the shrinking recursion every rule proves the check, but the rules that
widen per origin keep a weaker state: the recursive call's own contribution is
widened, and the division `9 / (a + 2)` brings the lower bound back only to
$-9$, where the joining rules and Warrow keep $-1$. The growing recursion is
the one row whose check does not hold in every execution. At 32 bits `x + 1`
wraps, so after $2^31$ nested calls `f` receives $-2^31$ and the check fails.
The widening rules therefore lose nothing by reporting #verdict("UNKNOWN"). The
joining rules raise the bound one value per round and give no answer within
the limit. The timeout shows only that, and neither divergence nor termination
of their solve (@sec:termination, @sec:trust-boundary). Bounded narrowing, at
its default bound 5, reaches the verdicts of per-origin warrowing on all four
programs.


#let _z(name) = claim-check(name, "z == 1")

*Refinement inside Int.* _Evidence: executable._ Int combines Interval and
Congruence in one value and refines them against each other (@sec:reduced-product).
In the program below, `q` is $4n + 1$ for some $n in [0, 20]$, so `r` is $1$.

#let _r(name) = claim-check("int-refine-" + name, "r == 1")
#listing(lang: "c", claim: "int-refine-int", ```
fun main() {
  i32 n = __voblint_nondet_int();
  if (0 <= n && n <= 20) {
    i32 q = (12 * n + 3) / 3;
    i32 r = q % 4;
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

*Queries between analyses.* _Evidence: executable._ Separate
analyses refine each other only through queries (@ch:cooperation). In the
following program they do so in both directions:

#listing(lang: "c", claim: "coop-mutual-both", ```
fun main() {
  i32 c = __voblint_nondet_int();
  i32 x, y;
  if (0 < c) { x = 0; y = 10; } else { x = 20; y = 30; }
  i32 z = (x <= y);
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
assignments to `y`.
For one program, evaluation shows that a check needs both analyses: Interval
and Order together prove it, and each alone leaves it unknown
(#isathm("coop_verdicts")).

== Where precision ends <sec:eval-flavors>

The examples above were chosen to show what a mechanism gains, so they say
little about what Voblint cannot prove. For that we use programs chosen by
someone else. Monniaux's tutorial on the flavors of abstract interpretation
walks through finite lattices, relational domains, widening, and exact
solving, and gives for each a small program that defeats it @monniaux24. We
pinned each of its programs that VIMP can express as a fixture of
#link(repo-blob + "tests/regression/28-flavors")[`28-flavors`], at `i32`.
Every check in them holds in every run, so each #verdict("UNKNOWN") below is
lost precision. No combination of Voblint's analyses, signed-overflow
policies (@sec:domain-kinds), and refinement modes proves the absolute-value,
foiled-narrowing, reset, and non-inductive checks below. For comparison we ran Goblint, at the
revision this thesis links, on C versions of the same programs with the
options that target each loss
(#link(repo-blob + "thesis/shared/code/goblint-flavors")[`goblint-flavors`],
@tab:flavors). Two differences matter. In C, signed
overflow is undefined, and Goblint by default assumes it does not happen,
whereas VIMP wraps. Goblint's relational domains come from the Apron library,
which our build of Goblint does not include, so @tab:flavors shows only its
non-relational domains.

#let _gob = {
  let rows = (:)
  for line in read("../shared/code/goblint-flavors/results.tsv").split("\n") {
    let cells = line.split("\t")
    if cells.len() == 3 { rows.insert(cells.at(0) + "/" + cells.at(1), cells.at(2)) }
  }
  rows
}
// The verdict of the first check of one Goblint run, in the thesis's words.
#let _gv(prog, config) = {
  let out = _gob.at(prog + "/" + config)
  verdict(if out.split(";").first().ends-with("will succeed") { "PROVED" } else { "UNKNOWN" })
}
#let _vv(name, cond) = verdict(claim-check(name, cond).at(3))

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    let configs = (
      "interval",
      "interval+gas10",
      "int+gas3",
      "interval+thresholds",
      "interval+thresholds-comparisons",
    )
    let progs = (
      ([vanilla, Sign], "flavors-vanilla-sign", "z < 0", "vanilla"),
      ([not inductive, Int], "flavors-sign-not-inductive-int", "i > 0", "sign_not_inductive"),
      ([absolute value], "flavors-coffee-bounded-order", "x != 0", "coffee_bounded"),
      ([widening, narrowing], "flavors-fudge", "i == 10", "fudge"),
      ([narrowing works], "flavors-narrowing-reset", "i <= 9", "narrow_works"),
      ([narrowing foiled], "flavors-blackcurrant", "i <= 9", "blackcurrant"),
      ([reset at equality], "flavors-reset-eq", "i <= 9", "reset_eq"),
    )
    table(
      columns: 7,
      align: (left + horizon,) + (center + horizon,) * 6,
      stroke: none,
      inset: (x: 3pt, y: 2.5pt),
      table.hline(stroke: 0.5pt),
      [*program*], [*Voblint*], table.cell(colspan: 5)[*Goblint*],
      [], [], [interval], [delay 10], [Int, delay 3], [thresholds], [comparisons],
      table.hline(stroke: 0.4pt),
      ..progs
        .map(((what, claim, cond, gprog)) => (
          what,
          _vv(claim, cond),
          ..configs.map(c => _gv(gprog, c)),
        ))
        .flatten(),
      table.hline(stroke: 0.5pt),
    )
  },
  kind: table,
  caption: [The flavors programs @monniaux24 in Voblint, with the analysis
    their claim names, and in Goblint at `i32` (`int`), where "will succeed"
    is shown as #verdict("PROVED"). Goblint columns: Interval;
    widening delayed 10 times (`solvers.td3.widen_gas`); Interval with
    Congruence and their refinement, delayed 3 times; threshold widening on
    every constant of the program; on the constants of comparisons only. The
    absolute-value row runs Voblint with Int and the order analysis. Goblint's
    outputs are recorded in `results.tsv` beside its programs.],
) <tab:flavors>

*Finite lattices.* _Evidence: executable._ The rule of signs says that the
sum of two negative numbers is negative @monniaux24[slide 8]. At a machine
kind it fails, since the sum of two negative `i32` values may wrap to a
nonnegative one. A sign bounds no magnitude, so Sign cannot exclude the wrap
even for constants:

#listing(lang: "c", claim: "flavors-vanilla-sign", ```
fun main() {
  i32 x = -5;
  i32 y = -10;
  i32 z = x + y;
  __voblint_check(z < 0);
}
```)

Sign reports #_vv("flavors-vanilla-sign", "z < 0"), and Interval keeps
$z = -15$ and proves the check (claims #claim-ref("flavors-vanilla-*")).
Nothing is missing here. Sign alone could prove the check only by assuming
that the sum does not overflow, which VIMP's wrapping semantics does not
justify.

*Invariants that are not inductive.* _Evidence: executable._ An abstract
fixpoint is at best the least _inductive_ invariant the domain can express,
and a property may hold without being inductive @monniaux24[slide 27]. In the
following loop `i` takes the values $4$ and $2$ at the check, so `i > 0`
holds there. Sign describes these values as positive, but `i - 2` of a
positive value may have any sign, so positivity is not preserved by the loop
and Sign reaches every sign at the loop head:

#listing(lang: "c", claim: "flavors-sign-not-inductive", ```
fun main() {
  i32 i = 6;
  i = i - 2;
  while (i != 0) {
    __voblint_check(i > 0);
    i = i - 2;
  }
}
```)

The domain itself is at fault only for Sign. Interval and Congruence together
can express an inductive invariant, $i in [0, 4]$ and $i$ even, from which the
guard `i != 0` leaves $[2, 4]$. Voblint's Int still reports
#_vv("flavors-sign-not-inductive-int", "i > 0"), because widening at the loop
head sends the lower bound to the `i32` limit, where `i - 2` may overflow,
and the value becomes the kind's top (claims
#claim-ref("flavors-sign-not-inductive*")). Goblint proves the check with
Interval and Congruence once their refinement runs and widening is either
delayed three times (@tab:flavors) or stopped at the threshold $0$ of the
guard.

*Paths and convexity.* _Evidence: executable._ The tutorial's coffee example
computes an absolute value and checks that it is positive only for a nonzero
argument @monniaux24[slide 38]:

#listing(lang: "c", claim: "flavors-coffee-bounded-order", ```
fun main() {
  i32 x;
  i32 y = 0;
  if (-1000 <= x && x <= 2000) {
    if (x < 0) {
      y = -x;
    } else {
      y = x;
    }
    if (y >= 1) {
      __voblint_check(x != 0);
    }
  }
}
```)

After the branch, the strongest statement true on both paths is that $y$ is
at least $|x|$. The check needs the converse, $y lt.eq |x|$, which holds only
as the disjunction of $y = x$ on one path and $y = -x$ on the other. A
non-relational domain loses both relations. A convex relational domain joins
the two branches into their convex hull @cousot78[§4.4], which keeps
$y gt.eq |x|$ and loses $y lt.eq |x|$, so polyhedra fail as well
@monniaux24[slides 42--43]. Voblint's order analysis ends with $x lt.eq y$, and
the check is #_vv("flavors-coffee-bounded-order", "x != 0") (claims
#claim-ref("flavors-coffee*"); the fixture
#fixture(
  "28-flavors/known-imprecision/02-coffee_absolute_value.vimp",
  label: "02-coffee_absolute_value.vimp",
)
is the same program without the bounds on `x`). Goblint reports the check
unknown in every configuration we ran. What is needed is a disjunction kept
until the check: trace partitioning keeps the states of the two branches
apart @rival07[§1.1] @blanchet03[§7.1.5], and path partitioning does so for
the last outcome of each conditional @mine17[§6.3.4]. In Voblint, either
would be a local state indexed by the path taken, with its own soundness
obligation that every run belongs to some part. No shipped analysis keeps
such a state (@sec:outlook-extending).

*Widening and narrowing.* _Evidence: executable._ The tutorial's two
widening examples that narrowing repairs are both
#verdict(claim-check("flavors-fudge", "i == 10").at(3)) in Voblint (claims
#claim-ref("flavors-fudge") and #claim-ref("flavors-narrowing-reset")). The
second is a counter that resets once it reaches $10$:

#listing(lang: "c", claim: "flavors-narrowing-reset", ```
fun main() {
  i32 i = 0;
  while (1) {
    i = i + 1;
    if (i >= 10) {
      i = 0;
    }
    __voblint_check(i <= 9);
  }
}
```)

Narrowing recovers the upper bound $9$ @monniaux24[slide 59], but the check is proved over
#raw(claim-check("flavors-narrowing-reset", "i <= 9").at(4).split("i=").at(1)).
Widening reaches the `i32` limit, where `i + 1` may overflow, so the lower
bound is lost and narrowing cannot bring it back. Goblint loses the same lower
bound, although it assumes that signed overflow does not happen: it leaves
#link(repo-blob + "thesis/shared/code/goblint-flavors/narrow_works_lb.c")[a check of `i >= 0`]
at the same point unknown.

*Narrowing foiled.* _Evidence: executable._ The same counter breaks
narrowing in two ways. In the first, a nondeterministic branch may skip the
increment @monniaux24[slide 60]:

#listing(lang: "c", claim: "flavors-blackcurrant", ```
fun main() {
  i32 i = 0;
  i32 c;
  while (1) {
    c = __voblint_nondet_int();
    if (c) {
      i = i + 1;
      if (i >= 10) {
        i = 0;
      }
    }
    __voblint_check(i <= 9);
  }
}
```)

The skipping path carries the loop-head value back unchanged. Every interval
$[0, c]$ with $c gt.eq 9$ is then a fixpoint, the widened value included, and
a decreasing iteration cannot descend below a fixpoint
@mine17[§4.7.3, Ex. 4.7] @halbwachs12. In the second, the counter resets on
`i == 10` instead of `i >= 10` @monniaux24[slide 77]:

#listing(lang: "c", claim: "flavors-reset-eq", ```
fun main() {
  i32 i = 0;
  while (1) {
    i = i + 1;
    if (i == 10) {
      i = 0;
    }
    __voblint_check(i <= 9);
  }
}
```)

The equality test removes no bound from an interval, so nothing stops the
widened bound at $9$. Both checks are
#_vv("flavors-blackcurrant", "i <= 9") in Voblint (claims
#claim-ref("flavors-blackcurrant") and #claim-ref("flavors-reset-eq")).

The literature offers three repairs. A delayed widening joins for a fixed
number of rounds before it widens @blanchet03[§7.1.3] @mine17[§4.7.4].
Goblint's top-down solver can delay widening at each widening point, and with
a delay of $10$ it proves both checks, while a delay of $9$ does not suffice
(@tab:flavors). The delay must exceed the loop bound, so it repairs these
loops and not loops with large or unknown bounds. Threshold widening stops at
constants of the program before it jumps to the limit @blanchet03[§7.1.2].
Goblint proves both checks with thresholds only when they include every
constant of the program, which here includes the $9$ of the check itself.
With the constants of comparisons, or with the check written as `i < 10`, it
does not. Finally, methods that avoid the decreasing iteration compute the
fixpoint directly. Policy iteration descends through the fixpoints of simpler
systems @costan05 but need not reach the least one @monniaux24[slide 73], and
max-strategy iteration reaches the least solution in its domain
@gawlitza12lmcs[Lemma 6.5]. Restarting the iteration from a fixpoint
projected onto chosen seed points recovers the bound lost to a self-loop
@henry14[§4.1.2]. Guided static analysis applies a standard analysis to a sequence
of restricted versions of the program @gopan07, and on the reset example it
yields $[0, 9]$ @monniaux24[slide 78]. Each repair changes how the solver iterates, so in
Voblint each would be a change to the vendored solver and its
partial-correctness proof (@sec:outlook-extending).

The tutorial's last flavor, completeness relative to a domain, concerns
arrays and maps @monniaux24[slide 81]. VIMP has no arrays, so this flavor has no
VIMP version.

Voblint thus proves the checks that non-relational domains with a standard
widening and narrowing prove, and it loses the ones these techniques are
known to lose. Goblint recovers three of them only through options that
Voblint lacks, and neither analyzer proves the absolute-value example with
the domains we ran. Each missing technique is a separate soundness
obligation, on a domain for partitioning and on the solver for the iteration
strategies.

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
