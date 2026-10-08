#import "../lib/theme.typ": vb
#import "../lib/code.typ": fixture, isaconst, isalocale, isathm, isatype, listing
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

@ch:results showed that every report #isaconst("run_voblint") returns is
sound, whichever analyses its configuration selects. This chapter compares what
those analyses prove. A numeric domain enters the theorem by proving the laws
of @ch:domains with facts about integers alone and, once registered
(@sec:coop-catalogue), is covered by #isathm("run_voblint_source_sound").

Sign is finite, so its join serves as its widening; Interval is infinite and
needs widening and narrowing; Parity and Congruence record residues; the
reduced product Int combines all four; and the order analysis of
@ch:cooperation records relations between variables (@sec:relational). Every verdict and analyzer state quoted in the text is
output on a regression program (@ch:evaluation), and each example shows a precision difference on one program only.

== What a numeric domain must provide <sec:instances-supply>

A new numeric domain supplies the record #isatype("nonrelational_ops") of
@sec:domain-contract and proves it sound. @fig:gamma shows one
value of each carrier and the integers it denotes.

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
        "signs:+; intervals:[1,9]; parities:1+2ℤ; congruences:1+4ℤ",
        shown: [`+`, `[1,9]`, `1+2ℤ`, `1+4ℤ`],
      ),
      table.hline(stroke: 0.5pt),
    )
  },
  kind: image,
  placement: none,
  caption: [One value of each shipped domain, as the analyzer prints it, and
    the integers it denotes between $-6$ and $10$. Congruence and Parity values
    print as $c + m ZZ$, the integers congruent to $c$ modulo $m$ ($m ZZ$ when
    $c = 0$). An end cell is filled when
    the set continues beyond the window. The values are illustrative. The Int value,
    the state of $x$ in @tab:reduction, denotes the intersection of its
    components' meanings, here ${1, 5, 9}$.],
) <fig:gamma>

The soundness proof interprets the locale #isalocale("sound_nonrelational_ops").
The generic construction of @sec:domain-contract then derives the abstract
transfer functions, their executable counterparts and their agreement, and
#isathm("sound_nonrelational_ops.dg_analysis_execI") turns them into a sound
component of the combined state (@ch:cooperation). Of its other premises,
which concern routing and keys (@sec:eq-routing) and the solver contracts
(@sec:cert-param), only one is about the domain's values: the initial state covers the initial stores (for
Parity, #isathm("parity_cinit_gamma")). All five refine guards with the same
filter (@sec:branches) and differ in the inverse operators, truth test and
intersection they supply; an inverse that cannot sharpen its operands returns
them unchanged (the shared #isaconst("inv_conservative") or a domain's own
identity). Their operations are monotone;
for Int this is proved only outside the fixpoint mode
(#isalocale("mono_nonrelational_ops"), #isathm("int_dom_mono_ops")). No
soundness theorem assumes it.

== One loop, five answers <sec:stride2>

The loop below is the fixture #fixture("12-widening/known-imprecision/05-mine_ex410_stride2_parity.vimp", label: "05-mine_ex410_stride2_parity.vimp"), adapted
from Goblint's regression test #link("https://github.com/goblint/analyzer/blob/d155e9e/tests/regression/56-witness/29-mine-tutorial-ex4.10.c")[`56-witness/29-mine-tutorial-ex4.10.c`] (revision
`d155e9e`), whose name refers to Example 4.10 of Miné's tutorial @mine17.
Goblint's test, marked to be skipped, loops while `v <= 50`, asserts only
bounds on $v$ and reads an invariant from a witness file. The VIMP fixture
loops while `v < 51` and has no witness, so Interval must recover the
bound $52$ by narrowing. The check `v == 51` is added here. In every run $v$
takes the odd values $1, 3, dots, 51$ and the loop exits with $v = 51$, so
every check holds.

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
        _s(d, "25:3"),
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

Interval's carrier is infinite. Plain joins would give the loop head
$ivl(1, 1)$, $ivl(1, 3)$, $ivl(1, 5)$, and on an unbounded loop they would grow
without end. The
widening and narrowing of @sec:domain-carrier-laws bring the head back to
$ivl(1, 52)$. The exit state
#_s("interval", "25:3") contains 52, which no execution reaches, and an
interval is convex, so it cannot say "odd".

Sign distinguishes negative, zero and positive values. Its carrier is finite,
so the join serves as widening. Sign loses magnitude and residue and keeps only
that $v$ is positive at the loop exit. It still detects contradictory sign
facts (@fig:domain-reachability).

Parity records only evenness. For `x = 2 * n; y = 2 * n + 1` with `n`
unconstrained, Interval answers #verdict("dom-even-odd-interval", "20:3") on
`x != y`, while Parity derives #state("dom-even-odd-parity", "20:3") and
answers #verdict("dom-even-odd-parity", "20:3"). Parity also refines guards
through its inverses. On `x + 1 == y` with `y` even, the inverse of `+`
(#isaconst("inv_plus_parity")) makes `x` odd
(#isathm("bfilter_parity_plus_narrows"), checked by evaluation), while
Interval, whose inverse of `+` is the identity, learns nothing about `x`.

Congruence analysis goes back to Granger @granger89 @mine17[§4.8]. A value
$c + m ZZ$ denotes $setcomp(n in ZZ, n equiv c med (mod m))$, with $m = 0$
meaning the single integer $c$. Parity is the case $m = 2$. The carrier is infinite, but its widening is the join
(#isaconst("widen_congruence")). Ascending chains still stabilize. A class that
strictly grows from a singleton ($m = 0$) gets a positive modulus, and every
further strict growth replaces the modulus by a proper divisor, which can
happen only finitely often. The argument follows @mine17[§4.8] and is not
mechanized.

Larger moduli matter when classes meet. Under `x == y` with $x in 1 + 4ZZ$ and
$y in 3 + 6ZZ$, the common value lies in $9 + 12ZZ$ (generalized Chinese
remainder theorem), so the true arm of a nested `if (x == 13)` is unreachable.
On the `__voblint_check(false)` in that arm, Parity knows only that both are
odd and answers #verdict("dom-crt-parity", "21:7"). Congruence filters
with #isaconst("inf_congruence") and answers
#verdict("dom-crt-congruence", "21:7"), and the intersection it computes is
exact (#isathm("gamma_inf_congruence")).

== The reduced product <sec:reduced-product>

The carrier #isatype("int_dom") holds a Sign, an Interval, a Parity and a
Congruence value and denotes the intersection of their meanings. Running the
four side by side is sound, but it misses facts that follow only from two
components together. In the program below, $x$ lies in
$ivl(-2, 10)$ at the check by the guards and is $1$ modulo $4$ by its
definition. Together these allow only $1$, $5$ and $9$, yet neither component
alone decides `x >= 1 && x <= 9`. A _reduction_ lets components tighten each
other, as in the reduced product @cousot79 @mine17[Def. 6.3, Ex. 6.2]. The residue class
moves the interval's bounds onto values that are $1$ modulo $4$, giving
$ivl(1, 9)$, and the positive interval then makes the sign positive. The
reduced value denotes the same integers and decides the check
(@tab:reduction).

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

Checks themselves do not reduce. As in Goblint's
#link("https://github.com/goblint/analyzer/blob/5503dec/src/cdomain/value/cdomains/int/intDomTuple.ml#L457-L473")[`IntDomTuple`],
a comparison is decided when one component decides it
(#isaconst("int_less_true")), so reduction reaches a check only through its
operands, that is, the stored values and the reduced results of evaluating
the operand expressions. The
same reduction proves `v == 51` in the loop of @sec:stride2, though it acts
inside the loop. On the true arm of `v < 51` the interval $ivl(1, 50)$ meets
"odd", so the reduction lowers it to $ivl(1, 49)$, and the increment yields
$ivl(3, 51)$ instead of Interval's $ivl(3, 52)$. The loop head therefore holds
$ivl(1, 51)$, the exit guard leaves only 51, and the product reports
#_s("int", "25:3") and #_v("int", "25:3").

The reduction is partial. One round first applies #isaconst("refine_interval"):
it intersects the intervals that Sign and Interval allow and tightens Sign,
Interval and Parity with the result. It then applies
#isaconst("refine_congruence"), which tightens Interval, Parity and Congruence
from the residue class and the parity. No step refines Sign directly from Congruence, but a later round passes such
facts on through Interval. From Interval, Congruence learns only the parity of
a singleton interval, so $ivl(4, 4)$ gives $2ZZ$, not $4$.

The policy #isatype("refine_mode") chooses no reduction, one round, or rounds
until the value stops changing, and the analyzer uses the last by default. In
every mode reduction preserves the denoted set (#isathm("refine_exact")) and
only moves down in the order (#isathm("refine_reductive")). Monotonicity is
proved only for the two non-fixpoint modes (#isathm("refine_nonfixpoint_mono")),
and soundness does not need it, because no soundness obligation of the domain interface, the analysis
contract or the solver asks for monotone transfers.

The fixpoint mode is total in HOL, returning its input if the iteration never
stabilizes, while the generated code iterates until the value stops changing.
That it always stops is not proved, so reduction is a second place, besides the
solve, where the executable may fail to return (@sec:trust-boundary).

Int's narrowing does not reduce. Reducing after a narrowing would break
the solver's narrowing law, which requires $b lle a narrow b lle a$ whenever
$b lle a$, because reduction moves down and can move the narrowed value below $b$. Take
$a = ltop$ and let $b$ hold Sign $signval(top)$, interval $ivl(-1, 0)$, even
parity and Congruence $ltop$, which together denote only zero. Componentwise narrowing returns a value
between $b$ and $a$, and one round of reduction then lowers its Sign component
below $b$'s $signval(top)$
(#isathm("post_narrow_refinement_would_violate_narrow_ge"), checked by
evaluation). Join and widening do not reduce, so a value reaching narrowing is
not necessarily reduced, and the law cannot be rescued by assuming it is. The
instance therefore narrows componentwise and reduces only inside
transfers and filters.

== The order analysis in practice <sec:relational>

The numeric domains are pointwise and cannot express that $x lt.eq y$. The
order analysis keeps the relational state of @sec:rel-state, a set of pairs
$x lt.eq y$, as a local specification proved sound in @sec:coop-catalogue. In
the program below, the guard `x < y` says nothing about either variable alone,
so Interval keeps #state("order-alone-interval", "12:5") and reports
#verdict("order-alone-interval", "12:5") at the first check, while the order
analysis holds #state("order-alone-order", "12:5") and reports
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

The other two checks show the limits of the representation and of its
transfers (@sec:rel-state). Under
`y <= z` it holds #state("order-alone-order", "14:7") and still reports
#verdict("order-alone-order", "14:7") for `x <= z`, and after `y = y + 1` it
holds #state("order-alone-order", "17:5") and reports
#verdict("order-alone-order", "17:5"). A copy, by contrast, is kept in both
directions. At `w = x` the analysis asks whether $x$ is at most and at least
each variable, and it answers `x <= x` itself, so it records
#state("order-alone-order", "20:3") and proves `w == x`, which Interval leaves
#verdict("order-alone-interval", "20:3"). It also forgets everything across calls
and alone cannot compare a variable with a constant, so it is useful mainly
together with Interval (@sec:eval-precision).

The carrier of this state is not a map from variables to values. The analysis
contract ranges over any local and shared carriers that are join semilattices
with a least element, with a joint concretization (@ch:analysis-interface), so
the global-channel specification #isaconst("rel_order_spec") interprets it
without any change to the framework. Each field of the combined state is a
#isatype("local_spec") without globals, and #isaconst("rel_order_spec")
publishes an analysis global, so it does not fit a field. The shipped
#isaconst("order_spec") is a local form of it. Unlike it, #isaconst("order_spec")
asks the other analyses after each assignment; like it, it keeps no facts
across calls (@sec:coop-catalogue).

Five domains prove the laws of @ch:domains with facts about integers alone,
and the source-level theorem covers each as a field of the combined state
(#isathm("run_voblint_source_sound")). Each domain proves facts the others miss on
some program, reduction moves facts between the numeric components, and the
order analysis proves relations no pointwise domain can express. The interface admits the identity for any
inverse operator (Sign and Interval for arithmetic, Parity and Congruence for `<`), needs no monotone reduction (Int in the fixpoint mode) and needs
no pointwise store (#isaconst("rel_order_spec"), #isaconst("order_spec")).
