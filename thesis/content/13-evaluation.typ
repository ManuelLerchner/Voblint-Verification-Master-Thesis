#import "../lib/math.typ": ctor
#import "../lib/code.typ": *
#import "../lib/stats.typ": stat
#import "../lib/claims.typ": (
  claim-check, claim-ref, claim-snapshot, claim-timed-out, snapshot-verdict,
)
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": verdict

= Evaluation <ch:evaluation>

@ch:results proved that every report #isaconst("run_voblint") returns is
sound. A machine-checked theorem can still hold for uninteresting reasons. Its
premises may never be met together, its obligations may be weaker than they
look, or it may exclude only errors that no real analyzer makes.
#cite(<kim26regulatory>, form: "prose", supplement: [§6]) validates a
mechanized model in two ways. Concrete witnesses show that the premises of its
theorems can be met, and direct falsification removes one condition and checks
that the theorem relying on it fails. Following this method, we first ask
whether the premises can hold together and whether the obligations exclude
real errors.
We then show on concrete programs what precision the analyzer reaches under the
theorem and where it ends, and how the code outside the theorem is tested.

The evidence differs in strength. A _machine-checked_ result is an Isabelle
theorem and holds, under its premises, for every input its statement ranges
over. An _evaluated_ result is an Isabelle fact proved by `eval`, which runs the
generated code of one concrete solve and therefore trusts the code generator.
An _executable_ result records the answer of one program at fixed analysis
settings, obtained through the parser and renderer outside the theorem
(@sec:trust-boundary). _Source inspection_ and _repository measurement_
support statements about the structure or size of the development.

== Non-vacuity #thy-badge("Voblint_Examples", "Example_Non_Vacuity") <sec:nonvacuity>

_Evidence: machine-checked, with the concrete solves evaluated._ A theorem
whose premises are unsatisfiable holds vacuously. The end-to-end
theorem assumes an initial store, a source run, and an
#isaconst("Analysed") answer, which the analyzer gives only if its solve
terminates.
#cite(<marmsoler26stark>, form: "prose", supplement: [§9]) shows with one small
executable instance that the locale assumptions of a formal model can be
satisfied, and we discharge the premises of the end-to-end theorem in the same
way.

The instance is the two-call program of @fig:program-to-equations under
Interval, entry-state contexts, and warrowing, with the source run that returns
from `bump(5)` and `bump(4)` and stops before the first check. Evaluation
computes an answer in which both checks are #verdict("PROVED"), and
#isathm("nv_source_certified") instantiates #isathm("run_voblint_source_sound")
with every premise discharged. The run's store thus reaches the graph node $v$
of the stopped run, a reported state describes it, and $v$ is not
#verdict("DEAD"). Likewise, #isathm("nv_check_proved_sound") instantiates
#isathm("run_voblint_check_sound") at the check `a == 6`. For the reachability
claim, a second program sets `x = 1` and guards a check by `x < 0`, which the
analyzer marks #verdict("DEAD"), and #isathm("nv_dead_unreached") derives from this verdict
that no store reaches that node, by the lemma behind
#isathm("run_voblint_check_sound") that a reached check is never
#verdict("DEAD"). The source runs are proved by rule
application, and the compiled graphs and the answers by `eval`. No such
instance discharges the premises of the arithmetic theorems
#isathm("run_voblint_arithmetic_safe") and
#isathm("run_voblint_arithmetic_refuted") on a concrete program.

== Do the obligations exclude real errors? <sec:eval-1161>

_Evidence: machine-checked, and executable against a defect documented
upstream._ For three coverage conditions the theories give a counterexample
to a weakened form. Two of them use a program whose `main` calls `f(1)` and then `f(5)`, with the entry
value of `f`'s parameter as the callee's context. #oblig("RETURN") combines
the caller's store at a call in context $c$ with a result of the callee in a
context $c'$ that the call admits, here $c' = 1$ for `f(1)`. A weakened
#oblig("RETURN") reads the callee's result in the caller's context $c = 0$
instead. A claim that covers `f` in every context except $0$ leaves its result in
context $0$ empty, so the weakened obligation holds vacuously after
the first call. This claim meets the weakened obligation and all the
others (#isathm("ret_weak_obligations")) but covers no store after `f(1)`, although
the run reaches that point with $a = 1$
(#isathm("return_at_caller_context_unsound")). #oblig("TOTAL") requires every
call to admit at least one callee context. Without it, a context relation may
admit none, so #oblig("CALL") and #oblig("RETURN") hold vacuously. A claim
that stops at the first call site then meets the others
(#isathm("tot_weak_obligations")) but misses the store at which the run
resumes after the call (#isathm("total_dropped_unsound"), @sec:contract).
The third drops the pairing of entry coverage (#isaconst("entry_pairs_cover")).
For `y = p(x)` with `x = 1` and a procedure `p` that returns its formal, an
answer may then cover the caller's store with one pair and the entered store
with another, and combining each pair's callee result with its own
continuation excludes the run's $y = 1$
(#isathm("unpaired_entry_cover_unsound")). These three selected conditions do
not show that every premise of the development is needed.

A domain obligation, in turn, excludes a defect that occurred in Goblint. In
#link("https://github.com/goblint/analyzer/issues/1156")[issue 1156]
(@ch:intro), Goblint claimed `c % 2 == 1` for $c in {-5, -7}$, although C's
truncating remainder gives $-1$ for both values.
#link("https://github.com/goblint/analyzer/pull/1161")[Pull request 1161]
restricted when the congruence domain returns a constant remainder and added
the program as regression test `37-congruence/14-negative.c` @goblint1161.
Its annotations require Goblint to leave the first check unknown and mark the
second, `c % 2 == -1`, as true but beyond Goblint's current precision. We did
not re-run the pre-fix Goblint, and the evidence for its behavior is the
upstream report.

In Voblint, the pre-fix remainder cannot be proved sound. The Congruence
remainder must meet #isathm("congruence_mod_sound"), which requires the
truncating concrete remainder #isaconst("c_mod") (@sec:vimp-vs-c) of any two
values to lie in the concretization of the abstract remainder. The pre-fix
answer, the constant $1$ for $(1 + 2ZZ) mod 2$, violates this obligation at
$-5$ (#isathm("prefix_congruence_mod_unsound")). The theorem holds for every
abstract remainder that returns this constant, and Goblint's pre-fix operator
returned it according to pull request 1161, so an obligation of this form would
have rejected that operator as well. Our fixture transliterates the test into
VIMP (@fig:goblint-1161). Congruence alone knows only
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

*Adding an analysis.* _Evidence: source inspection._ The obligations are
also local to each analysis. Adding the order analysis took soundness proofs
for its local specification and its query (#isathm("ord_spec_sound"),
#isathm("ord_query_sound")), a lattice instance, and the case, field and
selection cases of the combined state that @sec:instances-supply lists. No
theory of the framework or of the numeric domains refers to it outside
document text. A new numeric domain proves its lattice laws and operations
sound once, as an instance of #isalocale("kind_int_domain"), and the generic
construction derives its transfer functions and their soundness.

== Precision on concrete programs <sec:eval-precision>

The theorem says nothing about precision, since an analyzer that answers
#verdict("UNKNOWN") everywhere satisfies it (#isathm("unknown_everywhere_sound")).
Each example below therefore fixes the concrete behavior first, then shows what
one mechanism keeps or loses, and supports a claim about its program only.

#let _k99 = claim-snapshot("cost-down-k99")
#let _k100 = claim-snapshot("cost-down-k100")

*Contexts.* _Evidence: evaluated and executable._ @fig:eq-policies showed
which calls each context policy separates. Evaluation shows the gain on two
programs. When `main` calls one procedure from two sites, call strings of
length 1 prove the two checks after the calls, which the context-insensitive
analysis leaves unknown (#isathm("call_string_verdicts")). When the two calls
reach a procedure only through a second procedure, length 2 proves two checks
that length 1 leaves unknown (#isathm("call_string_depth_verdicts")).
Precision does not improve gradually with the length, however. In the
following program `down(100)` recurses to `down(0)`, so `n >= 0` holds at
every call:

#listing(lang: "c", claim: "cost-down-k100", ```
fun down(i32 n) {
  __voblint_check(n >= 0);
  if (n > 0) {
    down(n - 1);
  }
}

fun main() {
  down(100);
}
```)

A call string of length $k$ keys an activation by its last $k$ call sites, so
it separates the first $k$ recursion depths. With $k = 100$, each of the $101$
activations of `down` has its own string, the graph has #_k100.clusters.len()
procedure copies including `main`, and the check is
#snapshot-verdict(_k100, "n >= 0"). With $k = 99$, the two deepest activations
share the string of $99$ recursive call sites, so this context calls itself
and its entry receives the decreasing values of `n`. Widening removes the
lower bound there, the graph has #_k99.clusters.len() copies, and the check is
#snapshot-verdict(_k99, "n >= 0") (claims #claim-ref("cost-down-k99") and
#claim-ref("cost-down-k100")).

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
  caption: [Verdict and state of each row's check under five update rules
    (Interval, no contexts, bounded narrowing at its default bound 5), as on the
    #link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/#globals")[project site],
    where each cell opens its run in the playground. Except in the growing
    recursion, every check holds in every execution. "No answer in 5 s" means
    the command-line `--timeout 5` stopped the solve.],
) <fig:rules-programs>

*Update rules.* _Evidence: executable._ @fig:rules-programs runs the five
update rules of @sec:update-rules on four programs. In the first row, `p(1)`
and `p(2)` publish to the same entry seed. Warrow joins the two contributions
before widening, so the second looks like growth and the upper bound goes to
the largest 32-bit value. Per-origin warrowing widens each call site's constant
contribution separately, so nothing grows. Evaluation proves the same contrast
on a system with two writers to one global
(#isathm("two_writer_slot_warrow_loses_upper_bound"),
#isathm("two_writer_slot_warrow_per_origin_exact")). On the shrinking recursion,
where `a` concretely takes only $-1$ and $9$, every rule proves the check.
Warrowing per origin and bounded narrowing, however, widen the recursive
call's own contribution and lose precision, reaching the lower bound $-9$
where the other three rules keep $-1$. Once widening has lowered `a`, the
divisor `a + 2` may be negative, and `9 / (a + 2)` then ranges down to $-9$. Only the check of the growing recursion fails in some execution, because
at 32 bits `x + 1` wraps after $2^31$ nested calls, so #verdict("UNKNOWN") loses
nothing there. The joining rules raise the bound one value per round and give
no answer within the limit, which shows neither divergence nor termination of
their solve (@sec:termination). Bounded narrowing reaches the verdicts of
per-origin warrowing on all four programs.

#let _z(name) = claim-check(name, "z == 1")

*Refinement inside Int.* _Evidence: executable._ Int combines Interval and
Congruence in one value and refines them against each other (@sec:reduced-product).
The following program needs both directions of this exchange. Here `q` is
$4n + 1$ for some $n in [0, 20]$, so `r` is $1$.

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
#verdict(_r("interval").at(3)) at `r == 1`. Congruence alone cannot exclude
that `12 * n` wraps under #ctor("Assume_Top") (@sec:domain-kinds), keeps `r`
at #raw(_r("congruence").at(4).split("r=").at(1)), and reports
#verdict(_r("congruence").at(3)). In Int, the interval bounds `q` to
$[1, 81]$, so no operation wraps and the congruence keeps $q in 1 + 4ZZ$.
Since `q` is also nonnegative, its truncating remainder modulo $4$ is exactly
$1$, and Int proves the check with
#raw(_r("int").at(4).split("r=").at(1)) (claims #claim-ref("int-refine-*")).

*Queries between analyses.* _Evidence: executable._ Separate analyses refine
each other only through queries (@ch:cooperation), and in the following
program they do so in both directions:

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
#claim-ref("coop-mutual-*")). For one program, evaluation also shows that
Interval and Order together prove a check that each alone leaves unknown
(#isathm("coop_verdicts")).

== Where precision ends <sec:eval-flavors>

The examples above were chosen to show what a mechanism gains. To find what
Voblint cannot prove, we use programs chosen independently of it. Monniaux's
tutorial on the flavors of abstract
interpretation walks through finite lattices, relational domains, widening,
and exact solving, and gives for each a small program that defeats it
@monniaux24. We pinned each of its programs that VIMP can express as a
regression fixture at `i32`.
Every check in them holds in every run, so each #verdict("UNKNOWN") below is
lost precision. No combination of Voblint's analyses, signed-overflow policies
(@sec:domain-kinds), and refinement modes proves the non-inductive,
absolute-value, skipped-increment, and reset-at-equality checks below. For
comparison we ran Goblint at revision `5320a6b` on C versions of the same
programs with the options that target each loss (@tab:flavors). In C, signed
overflow is undefined. Goblint's default setting `assume_top` of
`sem.int.signed_overflow`, which our runs keep, sends a signed result that may
overflow to the top of its type, as Voblint's #ctor("Assume_Top") does, whereas
VIMP's semantics wraps. Our build of Goblint lacks the
Apron library that provides its relational domains, so @tab:flavors shows only
its non-relational domains.

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
      ([rule of signs#super[a]], "flavors-vanilla-sign", "z < 0", "vanilla"),
      ([not inductive], "flavors-sign-not-inductive-int", "i > 0", "sign_not_inductive"),
      ([absolute value], "flavors-coffee-bounded-order", "x != 0", "coffee_bounded"),
      ([bounded loop], "flavors-fudge", "i == 10", "fudge"),
      ([reset at bound], "flavors-narrowing-reset", "i <= 9", "narrow_works"),
      ([skipped increment], "flavors-blackcurrant", "i <= 9", "blackcurrant"),
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
  caption: [The flavors programs @monniaux24 (fixtures
    #link(repo-blob + "tests/regression/28-flavors")[`28-flavors`]) in Voblint
    with Interval, except Int for the invariant that is not inductive and Int
    with the order analysis for the absolute value. #super[a]Voblint runs Sign
    here, which Goblint lacks, and Voblint's Interval proves the check as
    Goblint's does. Goblint ran at `i32` (`int`) on the C programs of
    #link(repo-blob + "thesis/shared/code/goblint-flavors")[`goblint-flavors`],
    and its assertion verdict "will succeed" is shown as #verdict("PROVED"),
    "is unknown" as #verdict("UNKNOWN"). Goblint columns: Interval; widening
    delayed 10 times (`solvers.td3.widen_gas`); Interval with Congruence and
    their refinement, delayed 3 times; Interval with threshold widening on every
    constant of the program; on the constants of comparisons only. Goblint's outputs are
    recorded in `results.tsv` beside its programs.],
) <tab:flavors>

*Finite lattices.* _Evidence: executable._ The rule of signs says that the
sum of two negative numbers is negative @monniaux24[slide 8]. At a machine
kind the sum of two negative `i32` values may wrap to a nonnegative one, and
since a sign bounds no magnitude, Sign cannot exclude the wrap even for
constants:

#listing(lang: "c", claim: "flavors-vanilla-sign", ```
fun main() {
  i32 x = -5;
  i32 y = -10;
  i32 z = x + y;
  __voblint_check(z < 0);
}
```)

Sign reports #_vv("flavors-vanilla-sign", "z < 0"), and Interval keeps
$z = -15$ and proves the check (claims #claim-ref("flavors-vanilla-*")). This
loss needs no repair, because Sign could prove the check only by assuming that
the sum does not overflow, which VIMP's wrapping semantics does not justify.

*Invariants that are not inductive.* _Evidence: executable._ An abstract
fixpoint is at best the least _inductive_ invariant the domain can express,
and a property may hold without being inductive @monniaux24[slide 27]. In the
following loop `i` takes the values $4$ and $2$ at the check, so `i > 0`
holds there. However, `i - 2` of a positive value may have any sign, so the
loop does not preserve positivity and Sign reaches every sign at the loop head:

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

Interval and Congruence together can express an inductive invariant that
proves the check, $i in [0, 4]$ and $i$ even, from which the guard `i != 0`
leaves $[2, 4]$. Voblint's Int still reports
#_vv("flavors-sign-not-inductive-int", "i > 0"), because widening at the loop
head sends the lower bound to the `i32` limit, where `i - 2` may overflow,
and the value becomes the kind's top (claims
#claim-ref("flavors-sign-not-inductive*")). Goblint proves the check with
refined Interval and Congruence when widening is delayed three times
(@tab:flavors) or stopped at the threshold $0$ of the guard. The threshold
columns of @tab:flavors use Interval alone, which leaves the check unknown, so
the threshold run with Int is recorded only in `results.tsv`.

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

The check needs $y lt.eq |x|$ after the branch, which holds only as the
disjunction of $y = x$ on one path and $y = -x$ on the other. A non-relational
domain loses both relations, and a convex relational domain joins the branches
into their convex hull @cousot78[§4.4], which keeps $y gt.eq |x|$ but loses
$y lt.eq |x|$, so polyhedra fail as well @monniaux24[slides 42--43]. Voblint's
order analysis ends with $x lt.eq y$, and the check is
#_vv("flavors-coffee-bounded-order", "x != 0") (claims
#claim-ref("flavors-coffee*"), and the fixture
#fixture(
  "28-flavors/known-imprecision/02-coffee_absolute_value.vimp",
  label: "02-coffee_absolute_value.vimp",
)
is the same program without the bounds on `x`). Goblint reports the check
unknown in every configuration we ran. Proving it requires keeping the
disjunction, as trace partitioning does by keeping the states of the two
branches apart @rival07[§1.1] @blanchet03[§7.1.5] and path partitioning does
for the last outcome of each conditional @mine17[§6.3.4]. In Voblint, either
would be a local state indexed by the path taken, with its own soundness
obligation that every run belongs to some part, and no shipped analysis keeps
such a state.

*Widening and narrowing.* _Evidence: executable._ The tutorial's two
widening examples that narrowing repairs are both
#verdict(claim-check("flavors-fudge", "i == 10").at(3)) in Voblint (claims
#claim-ref("flavors-fudge") and #claim-ref("flavors-narrowing-reset")). The
first, the bounded loop, counts `i` up to $10$ and checks `i == 10` after the
loop. The second, the reset at bound, is a counter that resets once it
reaches $10$:

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

Narrowing recovers the upper bound $9$ @monniaux24[slide 59], and the check is
proved over
#raw(claim-check("flavors-narrowing-reset", "i <= 9").at(4).split("i=").at(1)).
The lower bound is lost because widening reaches the `i32` limit, where `i + 1`
may overflow, and narrowing cannot bring it back. With Interval alone, Goblint
loses the same lower bound for the same reason and leaves
#link(repo-blob + "thesis/shared/code/goblint-flavors/narrow_works_lb.c")[a check of `i >= 0`]
at the same point unknown. A widening delay of $10$, threshold widening, or Int
with a delay of $3$ proves that check (`results.tsv`).

*Narrowing foiled.* _Evidence: executable._ Two variants of the same
counter defeat narrowing. In the first, the skipped increment, a
nondeterministic branch may skip the increment @monniaux24[slide 60]:

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

Because the skipping path carries the loop-head value back unchanged, every
interval $[0, c]$ with $c gt.eq 9$ is a fixpoint, the widened value included,
and a decreasing iteration cannot descend below a fixpoint
@mine17[§4.7.3, Ex. 4.7] @halbwachs12. In the second, the reset at equality,
the counter resets on `i == 10` instead of `i >= 10` @monniaux24[slide 77]:

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

The literature repairs this loss in several ways. A delayed widening joins for
a fixed number of rounds before it widens @blanchet03[§7.1.3] @mine17[§4.7.4].
Goblint's top-down solver can delay widening at each widening point. A delay of
$10$ proves both checks (@tab:flavors) and a delay of $9$ does not
(`results.tsv`), so the
delay must exceed the loop bound and does not repair loops with large or
unknown bounds. Threshold widening stops at constants of the program before it
jumps to the limit @blanchet03[§7.1.2]. Goblint proves both checks with
thresholds only when they include every constant of the program, here
including the $9$ of the check itself, and not with the constants of
comparisons or with the check written as `i < 10`. Finally, some methods avoid
the decreasing iteration. Policy iteration descends through the fixpoints of
simpler systems @costan05 but need not reach the least one
@monniaux24[slide 73], and max-strategy iteration reaches the least solution in
its domain @gawlitza12lmcs[Lemma 6.5]. Restarting the iteration from a fixpoint
projected onto chosen seed points recovers the bound lost to a self-loop
@henry14[§4.1.2], and guided static analysis of a sequence of restricted
versions of the program @gopan07 yields $[0, 9]$ on the reset at equality
@monniaux24[slide 78]. Each repair changes how the solver iterates, so in
Voblint each would be a change to the vendored solver and its
partial-correctness proof. The tutorial's last flavor, completeness relative to
a domain, concerns arrays and maps @monniaux24[slide 81], which VIMP lacks.

Voblint therefore proves the checks that non-relational domains with a standard
widening and narrowing prove, and it loses those on which these techniques are
known to lose precision. Goblint recovers three of them only through options
that Voblint lacks, and neither analyzer proves the absolute-value example with
the domains we ran. Each missing technique is a separate soundness obligation,
on a domain for partitioning and on the solver for the iteration strategies.

== Tests of the unverified parts <sec:eval-corpus>

_Evidence: executable, and repository measurement._ For the handwritten code
around the generated analyzer (@sec:trust-boundary), tests are the only
project-local evidence. The theories under #link(repo-blob + "src")[`src/`]
contain #stat("isabelle.lines") physical lines in #stat("isabelle.theories")
files, including comments and document text but excluding generated theories.
The analyzer that runs is the #stat("generated_ocaml")-line generated OCaml
module, surrounded by #stat("handwritten_ocaml") lines of handwritten OCaml
under #link(repo-blob + "cli")[`cli/`], not counting the lexer, parser, and
printer generated from a grammar description.

A #link(repo-blob + "tests/regression")[regression corpus] runs the analyzer
end to end. Part of it is adapted from Goblint's regression tests, whose
origin the fixture header records. The corpus holds #stat("corpus.cases") VIMP
fixtures in #stat("corpus.groups") groups, each stating its command-line flags
and the verdict expected at each check. Cases in `precision/` pin the exact,
usually definite, verdict. In `soundness/` the program has executions on both
sides of the check, so #verdict("UNKNOWN") is the only sound answer. In
`known-imprecision/` the concrete result is fixed but the abstraction cannot
establish it, and the header names the mechanism that loses the information.
Of the remaining #stat("corpus.kinds.other") fixtures, the
#stat("corpus.by_group.26-machine-kinds") in
#link(repo-blob + "tests/regression/26-machine-kinds")[`26-machine-kinds`] pin
verdicts, diagnostics, and rejections at machine kinds, and most others pin
snapshots of the rendered graph or state, rejection of malformed input, or
solves expected not to finish within their time limit. The runner matches results by
source line, which tests the position bookkeeping of @sec:ocaml-boundary, and
distinguishes a missing report row from a #verdict("DEAD") one, so a check the
compiler dropped cannot pass as proved unreachable. Some fixtures pin the
conventions of @tab:vimp-vs-c at the analyzer's output, for instance
#fixture("10-arithmetic/precision/07-signed_division_totalization.vimp")
(truncating division and remainder). They check verdicts, not concrete runs,
since the development has no executable form of #isaconst("pstep").
#link(repo-blob + "tests/solver-trace")[Golden files] pin the solver trace
(@sec:tracing) of three programs step by step and expose changes in the
generated solver's execution order.

The parser is trusted to hand the analyzer the program the user wrote, and a
parser bug could make the analyzer report verdicts for a different program.
Property tests therefore print random syntax trees, built from the constructors
Isabelle exports, and require the parser to read back the same tree, and they
require it to finish without a crash on mutated programs. A round trip cannot
detect a misreading of the grammar that parser and printer share, and no test
relates the parsed tree to the program a user meant to write. CI runs the
corpus and the property tests on every pull request and push to the main
branch.

Together, these results show that the end-to-end theorem applies to a concrete
run, that three selected coverage conditions cannot simply be dropped, and that
one domain obligation excludes a real defect. Each precision example concerns
one program, the tests reach only what the corpus covers, and none of this
shows that #isaconst("pstep") is the intended semantics of VIMP
(@sec:vimp-vs-c).
