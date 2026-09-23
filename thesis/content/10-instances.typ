#import "../lib/code.typ": fixture, isaconst, isalocale, isasession, isathm, isatype, listing
#import "../lib/math.typ": *

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
#let verdict(name, loc) = raw(claim-row(name, loc).verdict)
#let state(name, loc) = raw(claim-row(name, loc).state)


= Five Domains and a Relational Witness <ch:instances>

@ch:domains claimed that a numeric domain must prove laws about integers only, with no
reference to contexts, routing or the solver. This chapter tests that claim of
RQ3 and K3 on the instances. Five domains prove the laws, and each is
interpreted into the analysis assembly of @sec:engineering, so the source-level
theorem of @sec:headline covers it under every context policy and update rule.
Each domain tests a different part of the interface. Sign is finite, so
its join serves as its widening. Interval is infinite and needs widening and
narrowing. Parity has no backward filter. Congruence has an exact meet. The
product Int combines the four under a partial reduction. A relational carrier
(@sec:relational) asks whether the contract depends on pointwise states at all.

Precision is compared on regression programs where the difference decides a
check. Every quoted verdict and state is a registered claim that the build
re-runs against the analyzer, which makes it executable evidence in the sense
of @ch:evaluation, and each shows a gain on one program only. Goblint's integer
domain is a tuple of optional components, among them definite values with
exclusion sets, intervals and congruences. Sign and Parity have no upstream
counterpart, and exclusion sets, enumerations, interval sets and bitfields have
none here (@app:goblint-alignment). Exclusion sets are ruled out by the
least-upper-bound requirement of @ch:domains.

== What an instance supplies

A domain instance proves the laws of @tab:domain-contract for its carrier and
supplies a branch transfer, either the generic filter of
#isalocale("backward_domain") or the identity. The locale
#isalocale("nonrelational_transfer") packages these pieces. The step from
generic to concrete is an interpretation: for each domain, one interpretation
per context family discharges the contracts of #isalocale("routed_dg_analysis")
(@fig:assembly), and the source-level theorem about #isaconst("run_voblint")
is proved from these interpretations.

== One loop, five answers <sec:stride2>

The loop below is the fixture #fixture("12-widening/known-imprecision/05-mine_ex410_stride2_parity.vimp", label: "05-mine_ex410_stride2_parity.vimp"), adapted
from Goblint's regression test #link("https://github.com/goblint/analyzer/blob/d155e9e/tests/regression/56-witness/29-mine-tutorial-ex4.10.c")[`56-witness/29-mine-tutorial-ex4.10.c`] (revision
`d155e9e`), which names Example 4.10 of Miné's tutorial @mine17 as its source.
Goblint's test asserts only bounds on $v$ and, according to its comment, reads
an invariant from a witness file "to have no narrowing". The VIMP fixture has
no witness input, so Interval must recover the bound $52$ by narrowing; the
check `v == 51` is added here. Concretely, $v$ runs through the odd numbers
$1, 3, dots, 51$ and the loop exits with $v = 51$, so every check holds.

#listing(lang: "c", claim: "dom-stride2-int", ```
fun main() {
  v = 1;
  while (v < 51) {
    __voblint_check(v >= 1);
    v = v + 2;
    __voblint_check(v <= 52);
  }
  __voblint_check(v >= 51);
  __voblint_check(v <= 52);
  __voblint_check(v == 51);
}
```)

#let _s(dom, loc) = state("dom-stride2-" + dom, loc)
#let _v(dom, loc) = verdict("dom-stride2-" + dom, loc)
#let _adds = (
  sign: [sign of a value; finite],
  interval: [bounds; infinite, needs widening],
  parity: [evenness],
  congruence: [residue modulo $m$],
  int: [all four, reduced],
)
#figure(
  table(
    columns: (auto, auto, 1fr, auto, auto),
    align: (left, left, left, left, left),
    stroke: none,
    table.hline(),
    [*domain*], [*records*], [*state at the exit*], [`v >= 51`], [`v == 51`],
    table.hline(stroke: 0.5pt),
    ..("sign", "interval", "parity", "congruence", "int")
      .map(d => (
        [#d],
        _adds.at(d),
        _s(d, "25:3"),
        _v(d, "23:3"),
        _v(d, "25:3"),
      ))
      .flatten(),
    table.hline(),
  ),
  caption: [The stride-2 loop under each domain (claims `dom-stride2-*`). No
    single component proves `v == 51`: Interval has the bound, Parity and
    Congruence have the oddness. The reduced product `int` combines them.],
) <fig:stride2>

Sign is finite, so a plain join serves as its widening. Finiteness does not
discharge the termination premise, because no vendored termination theorem
covers the side-effecting solver (@sec:termination).

An interval with possibly infinite ends records a range, which makes the
carrier infinite: the loop head sees $ivl(1, 1)$, $ivl(1, 3)$, $ivl(1, 5)$,
and plain joins would grow without end on an unbounded loop. The widening
#isaconst("widen_ivl_core") replaces a bound that moved by an infinity, and the
narrowing #isaconst("narrow_ivl_td"), which replaces only infinite bounds,
brings the head back to $ivl(1, 52)$. The exit state
#_s("interval", "25:3") contains 52, which no execution reaches, and an
interval is convex, so it cannot say "odd".

Parity records only evenness. For `x = 2 * n; y = 2 * n + 1` with `n`
unconstrained, Interval answers #verdict("dom-even-odd-interval", "20:3") on
`x != y`, while Parity derives #state("dom-even-odd-parity", "20:3") and
answers #verdict("dom-even-odd-parity", "20:3"). Parity is also the domain
without backward filtering: its branch transfer #isaconst("branch_parity") is
the identity, sound because a guard only selects a subset of the incoming
stores. On the contradictory guard of @fig:domain-reachability, Sign reports
the branch #verdict("dom-disjunct-sign", "13:5"), Parity
#verdict("dom-disjunct-parity", "16:5"). The interface therefore admits an
instance without the precision mechanism of @ch:domains. Filtering improves
precision, but soundness does not require it.

Congruence analysis goes back to Granger @granger89. A value denotes
$setcomp(n, n equiv c med (mod m))$, with $m = 0$ meaning the single integer
$c$; Parity is the case $m = 2$. Larger moduli matter when classes meet: under
`x == y` with $x = 4n + 1$ and $y = 6m + 3$, the common value is
$9 med (mod 12)$ by the Chinese remainder theorem, so a nested test `x == 13`
is unreachable. Parity knows only that both are odd and answers
#verdict("dom-crt-parity", "21:7")\; Congruence filters with
#isaconst("intersect_congruence") and answers
#verdict("dom-crt-congruence", "21:7"). The intersection is exact
(#isathm("gamma_intersect_congruence")).

== The reduced product

Combined, the four domains should prove facts that none proves alone. The
carrier
#isatype("int_dom") holds a Sign, an Interval, a Parity and a Congruence value
and denotes the intersection of their meanings. Running the four side by side
is sound but does not prove `v == 51`: the exit tuple holds
$ivl(51, 52)$ and "odd", which no component decides alone, although together
they denote exactly $setof(51)$. A _reduction_ lets components tighten each
other, as in the reduced product @cousot79 @rival20[§5.1.2]: the oddness moves
the upper bound from 52 to 51, and the product reports #_s("int", "25:3") and
#_v("int", "25:3").

The reduction is partial. One round applies #isaconst("refine_interval"),
which tightens Sign, Interval and Parity from the interval bounds, and then
#isaconst("refine_congruence"), which tightens Interval, Parity and Congruence
from the residue class. No step refines Congruence from Interval or Sign from
Congruence.

The policy #isatype("refine_mode") chooses no reduction, one round, or rounds
until the value stops changing. In every mode reduction preserves the denoted
set (#isathm("refine_exact")) and only moves down in the order
(#isathm("refine_reductive")). Monotonicity is proved only for the two
non-fixpoint modes (#isathm("refine_nonfixpoint_mono")). The public analyzer
uses the fixpoint mode. Its soundness needs no monotonicity of reduction,
because no obligation of @ch:domains asks for monotone transfers. The fixpoint
mode is total in HOL, returning its input if the iteration never stabilizes,
while the generated code iterates until the value stops changing. That it
always stops is not proved, so reduction is a second place, besides the solve,
where the executable may fail to return (@sec:trust-boundary).

== Why narrowing does not reduce <sec:no-refining-narrow>

Reducing after every operation, including narrowing, would break the solver's
narrowing law, which requires $b lle a narrow b lle a$ whenever $b lle a$.
Reduction only moves down, so the upper half survives; the lower half fails
whenever reduction lowers the narrowed value below $b$. Take $a = ltop$ and let
$b$ hold Sign $ltop$, interval $ivl(-1, 0)$ and even parity. Together these
denote only zero, but Sign still says $ltop$. Componentwise narrowing returns a
value between $b$ and $a$, and one round of reduction afterwards lowers its
Sign component below $b$'s $ltop$. The lemma
#isathm("post_narrow_refinement_would_violate_narrow_ge") checks this by
evaluation.

A stability argument would fix the step if every value reaching narrowing
were already reduced: then monotone reduction would keep $b$ below the result.
The carrier does not maintain that invariant. Join and widening do not reduce,
so a value that reaches narrowing through a widened solver state need not be
stable, and a narrowing built on the invariant would violate the class law at
the instance. The instance therefore narrows componentwise and reduces only
inside transfers and filters. So the solver's class law is an actual
obligation on the instance, and it decides where the product may reduce.

== A relational carrier <sec:relational>

Every domain so far is pointwise, and a pointwise state forgets relations
between variables. The question is whether that limitation belongs to the
framework or only to these domains, that is, whether a relational local state
needs any change to the generic interface. The type #isatype("relc") answers
it. A value is an explicit empty element or a set of variable pairs, where
$(x, y)$ asserts $x <= y$; the order is reverse inclusion. No function from
variables to abstract integers appears in the carrier.

The specification #isaconst("rel_order_spec") discharges the analysis soundness
contract #isalocale("sound_dg_spec_core") of the numeric analyses without any
change to the framework, because the contract already ranges over arbitrary
local and shared carriers with a joint concretization (@ch:analysis-interface).
On `if (x < y) { z = 1; } else { z = 0; }` with $x$ and $y$ unconstrained,
Interval learns nothing at the true branch (#isathm("demo_ivl_x_at_branch")),
while the relational carrier records $(x, y)$ there
(#isathm("demo_rel_learns_xy")); both facts are proved by evaluating the
generated solver inside Isabelle. The carrier forgets a variable on
assignment, forgets everything across calls and does not close its pairs under
transitivity, so it is not a useful analysis. It only shows that the proved
interface admits a relational local state. Its session
#isasession("Voblint_Analysis_Relational") builds on
#isasession("Voblint_Exec") and does not import
#isasession("Voblint_Nonrelational"), which holds the pointwise transfer
theories the numeric domains share. The executable assembly of
@sec:engineering fixes a reachability-lifted store of per-variable values, so
the witness is not selectable in the analyzer.

The chapter gives the instance side of RQ3 and K3. Five domains prove the
laws of @ch:domains with facts about integers alone, and one interpretation per
domain and context family makes the source-level theorem hold for each. The
instances show that the interface asks for no backward filter (Parity), no
monotone reduction (Int in the fixpoint mode) and no pointwise store
(#isaconst("rel_order_spec")), while the solver's narrowing law does constrain
where the product may reduce. The precision differences of this chapter are
executable evidence about single programs; @ch:evaluation collects them with
the machine-checked precision witnesses.
