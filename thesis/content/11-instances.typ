#import "../lib/theme.typ": vb
#import "../lib/code.typ": fixture, isaconst, isalocale, isathm, isatype, listing, thy-badge
#import "../lib/figures.typ": int-axis, int-strip, printed-set, verdict as verdict-chip
#import "../lib/math.typ": *
#import "../lib/claims.typ": claim-ref

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


= Five Domains and an Order Analysis <ch:instances>

@ch:results proved that a report is sound whichever analyses produced it. A
user can choose among the numeric domains Sign, Interval, Parity and
Congruence, their combination Int, and the relational order analysis. The four
base domains are textbook material, and the project site lets readers
#link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/index.html#values")[try them interactively],
so this chapter treats them briefly. Most of it describes Int, which combines
the four base domains and gains precision by letting them exchange facts. The
formalization proves that this exchange preserves a value's meaning and shows
why narrowing must skip it.

== The implemented domains <sec:instances-supply>

The four base domains, Sign #thy-badge("Voblint_Domain", "Sign_Lattice"),
Interval #thy-badge("Voblint_Domain", "Interval_Lattice"), Parity
#thy-badge("Voblint_Domain", "Parity_Lattice") and Congruence
#thy-badge("Voblint_Domain", "Congruence_Lattice"), are the classical
non-relational domains @mine17;
congruences go back to Granger @granger89. @fig:gamma shows one value of each
and the integers it stands for. Sign and Parity are finite, and a congruence
class cannot grow forever either: growing from a single integer gives it a
positive modulus, and every later strict growth replaces that modulus by a
proper divisor @mine17[§4.8]. This argument is not mechanized
here. All three use the join as their widening and keep the old value as their narrowing.
Only Interval has a widening that jumps ahead and a narrowing that refines
(@sec:domain-carrier-laws).

#figure(
  {
    set text(size: 8.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let (lo, hi) = (-6, 10)
    let row(domain, value, shown: none) = {
      let inside = printed-set(value)
      (
        domain,
        if shown == none { raw(value) } else { shown },
        ..int-strip(lo, hi, x => if inside(x) { "extra" } else { none }),
      )
    }
    table(
      columns: (auto, auto) + (auto,) * (hi - lo + 3),
      column-gutter: (5pt, 5pt) + (0pt,) * (hi - lo + 2),
      stroke: none,
      inset: (x: 0.9pt, y: 1.8pt),
      align: (left + horizon, left + horizon) + (center + horizon,) * (hi - lo + 3),
      table.hline(stroke: 0.5pt),
      [*domain*], [*value*], table.cell(colspan: hi - lo + 3)[*the integers it denotes*],
      [], [], ..int-axis(lo, hi, step: 2),
      table.hline(stroke: 0.4pt),
      ..row([Sign], "≥0"),
      ..row([Interval], "[-2,5]"),
      ..row([Parity], "1+2ℤ", shown: [`1+2ℤ` (odd)]),
      ..row([Congruence], "2+3ℤ"),
      ..row(
        [Int],
        claim-row("int-reduction-fixpoint", "68:7").state.split("x=").at(1),
        shown: claim-row("int-reduction-fixpoint", "68:7")
          .state
          .split("x=")
          .at(1)
          .split("; ")
          .map(c => raw(c.split(":").at(1)))
          .join([, ]),
      ),
      table.hline(stroke: 0.5pt),
    )
  },
  kind: image,
  placement: none,
  caption: [One value of each implemented domain, as the analyzer prints it, and
    the integers it denotes between $-6$ and $10$. Congruence and Parity values
    print as $c + m ZZ$, the integers congruent to $c$ modulo $m$ ($m ZZ$ when
    $c = 0$). An end cell is filled when
    the set continues beyond the window. The values are illustrative. The Int value,
    the reduced state of $x$ in @tab:reduction, denotes the intersection of its
    components' meanings, here ${1, 5, 9}$.],
) <fig:gamma>

Adding a domain mainly requires class instances for its carrier and a
soundness proof for its operations: it supplies the record #isatype("nonrelational_ops") of
@sec:domain-contract and interprets #isalocale("sound_nonrelational_ops").
The generic construction then derives the abstract and executable transfer
functions and their agreement, and
#isathm("sound_nonrelational_ops.dg_analysis_execI") makes the domain a sound
component of the combined state (@ch:cooperation). Of the lemma's premises,
only one concerns the domain's values: its initial state must cover the
initial stores (for Parity, #isathm("parity_cinit_gamma")).

== One loop, five answers <sec:stride2>

The loop below is the fixture #fixture("12-widening/known-imprecision/05-mine_ex410_stride2_parity.vimp", label: "05-mine_ex410_stride2_parity.vimp"),
adapted from Goblint's regression test #link("https://github.com/goblint/analyzer/blob/d155e9e/tests/regression/56-witness/29-mine-tutorial-ex4.10.c")[`56-witness/29-mine-tutorial-ex4.10.c`]
(revision `d155e9e`) after Example 4.10 of Miné's tutorial @mine17. In every
run $v$ takes the odd values $1, 3, dots, 51$ and the loop exits with
$v = 51$, so every check holds.

#listing(
  lang: "c",
  claim: "dom-stride2-int",
  highlights: (
    (line: 8, start: 3, end: none, fill: vb.accent, tag: [line 8]),
    (line: 10, start: 3, end: none, fill: vb.accent, tag: [line 10]),
  ),
  ```
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
  ```,
)

#let _v(dom, loc) = verdict("dom-stride2-" + dom, loc)
// The domain column already names the domain, so the cell drops the printer's prefix.
#let _s-cell(dom, loc) = raw(
  claim-row("dom-stride2-" + dom, loc).state.split(": ").slice(1).join(": "),
)
#let _adds = (
  sign: [sign of a value; finite],
  interval: [bounds; infinite ascending chains],
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
    [*domain*],
    [*records*],
    [*state at the exit*],
    [`v >= 51` \ #text(size: 0.85em)[line 8]],
    [`v == 51` \ #text(size: 0.85em)[line 10]],
    table.hline(stroke: 0.5pt),
    ..("sign", "interval", "parity", "congruence", "int")
      .map(d => (
        [#d],
        _adds.at(d),
        _s-cell(d, "25:3"),
        _v(d, "23:3"),
        _v(d, "25:3"),
      ))
      .flatten(),
    table.hline(),
  ),
  caption: [The stride-2 loop under each domain (claims
    #claim-ref("dom-stride2-*")), at the two highlighted checks of the listing. Only Int, which combines the bound and the
    oddness, proves `v == 51`.],
) <fig:stride2>

Each base domain records a different property of $v$. Interval finds the bound
through widening and narrowing, but its exit state still allows $52$, and an
interval has no way to say "odd". Parity and Congruence know that $v$ is odd
but nothing about its size, and Sign knows only that $v$ is positive. Every
answer is sound, yet none of the four proves `v == 51`. Only Int, which puts
the bound and the oddness together, does (@sec:reduced-product).

== The reduced product #thy-badge("Voblint_Domain", "Int_Lattice") <sec:reduced-product>

An Int value (#isatype("int_dom")) holds one value of each base domain and
stands for the integers that all four allow. Running the four side by side
would be sound, but each would work with its own value only, so a fact that
needs two of them would not be found. @fig:stride2 shows this: no
base domain alone proves `v == 51`. In the program below, the guards keep
$x$ between $-2$ and $10$, and the assignment makes $x$ one more than a
multiple of $4$. Only $1$, $5$ and $9$ satisfy both, so `x >= 1 && x <= 9`
holds. Yet the interval alone still allows $-2$ and the residue class alone
allows $-3$, so neither component can decide the check. A _reduction_ lets
the components sharpen each other, as in the reduced product @cousot79
@mine17[Def. 6.3, Ex. 6.2]. Here the residue class moves the interval's bounds
to the nearest values that are $1$ modulo $4$, giving $ivl(1, 9)$, and the now
positive interval makes the sign positive. The reduced value stands for the
same integers and decides the check (@tab:reduction). Goblint uses a
similar reduced-tuple design for integers. Its
#link(
  "https://github.com/goblint/analyzer/blob/5503dec/src/cdomain/value/cdomains/int/intDomTuple.ml",
)[`IntDomTuple`]
combines up to six optional components, among them definite values with
exclusion sets, intervals, enumerations and congruences, each enabled by an
option. Its `ana.int.refinement` setting offers the same three reduction modes
as Int. Goblint defaults to no reduction, and Voblint defaults to the
fixpoint mode.

#listing(lang: "c", claim: "int-reduction-fixpoint", ```
fun main() {
  n = __voblint_nondet_int();
  x = 4 * n + 1;
  if (x >= -2) {
    if (x <= 10) {
      __voblint_check(x >= 1 && x <= 9);
    }
  }
}
```)

#let _red(mode) = {
  let row = claim-row("int-reduction-" + mode, "68:7")
  let comps = row.state.split("x=").at(1).split("; ").map(c => c.split(":").at(1))
  (comps, row.verdict)
}
#figure(
  {
    let (never, v-never) = _red("never")
    let (fix, v-fix) = _red("fixpoint")
    table(
      columns: 3,
      align: (left, center, center),
      stroke: none,
      table.hline(),
      [*component of* $x$], [*without reduction*], [*with reduction*],
      table.hline(stroke: 0.5pt),
      ..("Sign", "Interval", "Parity", "Congruence")
        .enumerate()
        .map(((i, n)) => ([#n], raw(never.at(i)), raw(fix.at(i))))
        .flatten(),
      table.hline(stroke: 0.5pt),
      [verdict of the check], verdict-chip(v-never), verdict-chip(v-fix),
      table.hline(),
    )
  },
  placement: none,
  caption: [The value of $x$ at the check of the program above, without
    reduction and with the default reduction (claims #claim-ref("int-reduction-never") and
    #claim-ref("int-reduction-fixpoint")). Both columns describe the integers $1$, $5$
    and $9$ in the guard's range, but only the reduced value decides the check.],
) <tab:reduction>

Reduction is also what proves `v == 51` in @fig:stride2. Inside the loop, the
guard `v < 51` leaves $ivl(1, 50)$, and together with "odd" the reduction
shrinks this to $ivl(1, 49)$. The increment then gives $ivl(3, 51)$ instead of
Interval's $ivl(3, 52)$, the loop head settles at $ivl(1, 51)$, and after the
loop only $51$ remains.

A reduction round has two steps. #isaconst("refine_interval") first combines
the range information of Sign and Interval and uses the result to sharpen
Sign, Interval and Parity. #isaconst("refine_congruence") then uses the
residue class, intersected with the parity, to sharpen Interval, Parity and Congruence. Through
#isatype("refine_mode") the user chooses whether to reduce never, once, or
until nothing changes, which is the default. Every mode keeps the integers a
value stands for (#isathm("refine_exact")) and only ever makes the value
smaller (#isathm("refine_reductive")).

The default mode repeats rounds until the value stops changing. In Isabelle
this is a total function: if the rounds never settle, it returns its input.
The generated OCaml instead keeps iterating, and no proof shows that it always
stops. On some input the analyzer might therefore run forever instead of
returning a report, just as it would if the solver did not terminate
(@sec:trust-boundary). Soundness is unaffected, because the theorem only
speaks about reports that are returned.

Int reduces the result of every arithmetic operation and of the intersections
and inverse operators of the guard filter. Join, widening and narrowing work
componentwise, and for join and widening Goblint makes the same choice. For
narrowing, Voblint's solver contract forces the choice. The verified solver relies on the bracket
laws $b lle a narrow b lle a$ for $b lle a$ (@sec:widening), and reduction,
which only makes values smaller, can push a narrowed value below $b$
(#isathm("post_narrow_refinement_would_violate_narrow_ge"), checked by
evaluation). Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5503dec/src/cdomain/value/cdomains/int/intDomTuple.ml#L421-L431",
)[`IntDomTuple`]
does reduce after narrowing. No proof obliges its lattices to satisfy the
bracket laws, so Goblint can make this choice and Voblint cannot.

== The order analysis #thy-badge("Voblint_Analysis_Relational", "Rel_Order_Local") <sec:relational>

None of these domains can express that $x lt.eq y$, because each describes
the variables one at a time. The order analysis keeps a set of such pairs, the
relational state of @sec:rel-state. A guard between two variables adds a pair.
An assignment first forgets the pairs involving the changed variable. It then
asks the shared query channel how the new value relates to each variable, and
every active analysis, the order analysis included, may contribute an answer
(@sec:coop-catalogue). In the program below, the guard `x < y` tells Interval
nothing about either variable, so it keeps
#state("order-alone-interval", "12:5") and reports
#verdict("order-alone-interval", "12:5") at the first check. The order
analysis records #state("order-alone-order", "12:5") and reports
#verdict("order-alone-order", "12:5").

#listing(lang: "c", claim: "order-alone-order", ```
fun main() {
  x = __voblint_nondet_int();
  y = __voblint_nondet_int();
  z = __voblint_nondet_int();
  if (x < y) {
    __voblint_check(x <= y);
    if (y <= z) {
      __voblint_check(x <= z);
    }
    y = y + 1;
    __voblint_check(x <= y);
  }
  w = x;
  __voblint_check(w == x);
}
```)

Because the analysis does not combine pairs transitively, it cannot prove
`x <= z` under `y <= z`: it holds #state("order-alone-order", "14:7") there
and answers #verdict("order-alone-order", "14:7") (@sec:rel-state). The assignment
`y = y + 1` throws away every pair involving $y$, leaving
#state("order-alone-order", "17:5"). A copy, in contrast, yields pairs in both
directions. At `w = x` the assignment asks, for the variable $x$ itself,
whether `x <= x` holds in each direction. The order analysis answers yes to
both, because it treats a variable as ordered with itself, so it records
#state("order-alone-order", "20:3") and proves `w == x`, where Interval
answers #verdict("order-alone-interval", "20:3"). The analysis contract of
@ch:analysis-interface accepts this state as it is, even though it is not a
map from variables to values.

The base domains record different properties, Int lets them share these
facts, and the order analysis proves relations that no domain over single
variables can express. The order analysis can also run together with the
numeric domains in one combined state (@ch:cooperation). At each assignment it
then asks them how the new value compares with the other variables, and a
check is decided by the meet of all their answers. @sec:eval-precision shows
that Interval and the order analysis together prove a check that neither
proves alone.
