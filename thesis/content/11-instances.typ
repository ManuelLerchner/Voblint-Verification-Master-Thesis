#import "../lib/theme.typ": vb
#import "../lib/code.typ": fixture, isaconst, isalocale, isathm, isatype, listing, site, thy-badge
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

@ch:results proved that a report is sound regardless of which analyses
produced it. A user can choose among the numeric domains Sign, Interval,
Parity, and Congruence, their combination Int, and the relational order
analysis. The four base domains are textbook material, and the project site
lets readers
#link(site("index.html#values"))[try them interactively].
Int combines Interval and Congruence and gains precision by letting them
exchange facts. The formalization proves that this exchange keeps every
integer a value stands for and shows why narrowing must skip it.

== The implemented domains <sec:instances-supply>

The four base domains, Sign #thy-badge("Voblint_Domain", "Sign_Lattice"),
Interval #thy-badge("Voblint_Domain", "Interval_Lattice"), Parity
#thy-badge("Voblint_Domain", "Parity_Lattice"), and Congruence
#thy-badge("Voblint_Domain", "Congruence_Lattice"), are the classical
non-relational domains @mine17, shown with one value each in @fig:gamma.
Sign and Parity are finite. A congruence class cannot grow forever either,
because growing from a single integer gives it a positive modulus and every
later strict growth replaces that modulus by a proper divisor @mine17[§4.8], an
argument not mechanized here. Sign, Parity and Congruence therefore widen by
the join, and only Interval has a widening that jumps ahead
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
        claim-row("int-reduction-fixpoint", "74:7").state.split("x=").at(1),
        shown: claim-row("int-reduction-fixpoint", "74:7")
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
    the set continues beyond the window. The values are illustrative. The Int value
    denotes the intersection of its
    components' meanings, here ${1, 5, 9}$.],
) <fig:gamma>

Each of the five domains is an instance of the class
#isalocale("kind_int_domain") (@sec:domain-contract), and the order analysis
proves the laws of its local specification (#isathm("ord_spec_sound")). The
generic construction derives sound transfer functions for every instance of
the class, first on function-valued states (#isathm("nonrel_spec_sound")) and
then on their executable representation (#isathm("nonrel_exec_spec_sound"),
@sec:represented-function). Hence #isathm("run_voblint_source_sound") covers
every selection of these analyses. Making a new domain selectable, however,
is not generic. It needs a new case of the #isatype("analysis") datatype, a
field of the combined state, and the cases that give the field its lens, its
concretization and its answers (@ch:cooperation). The proofs about the combined
state, an instance of the locale #isalocale("mcp_registry"), proceed by cases
on the analysis and must cover the new case.

== One loop, five answers <sec:stride2>

The loop below is the fixture #fixture("12-widening/known-imprecision/05-mine_ex410_stride2_parity.vimp", label: "05-mine_ex410_stride2_parity.vimp"),
adapted from Goblint's regression test #link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/tests/regression/56-witness/29-mine-tutorial-ex4.10.c")[`56-witness/29-mine-tutorial-ex4.10.c`]
after Example 4.10 of Miné's tutorial @mine17. In every
run $v$ takes the odd values $1, 3, dots, 51$ and exits with $v = 51$, so
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
    i32 v = 1;
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
  int: [bounds and residue, reduced],
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
    #claim-ref("dom-stride2-*")), at the two highlighted checks of the listing,
    under the default signed-overflow policy #ctor("Assume_Top"). Only Int, which
    combines the bound and the oddness, proves `v == 51`.],
) <fig:stride2>

Each base domain records a different property of $v$. Interval finds the
bound through widening and narrowing, but its exit state still allows $52$,
and an interval cannot express "odd". Parity knows that $v$ is odd but
nothing about its size, and Sign knows only that $v$ is positive. Congruence
alone loses even the oddness, because under #ctor("Assume_Top") it cannot
exclude that `v + 2` wraps and returns its top (@sec:domain-kinds). Int keeps
the class, because its interval shows that no value wraps, and by putting the
bound and the oddness together it proves `v == 51` (@sec:reduced-product).

== The reduced product #thy-badge("Voblint_Analysis_Int", "Int_Tuple_Kind") <sec:reduced-product>

An Int value (#isatype("int_tuple")) holds one interval and one congruence and
stands for the integers that both allow. Running the two side by side would be
sound, but a fact that needs both of them would not be found. In the program
below, the guards keep $x$ between $-2$ and $10$, and the assignment makes $x$
one more than a multiple of $4$. Only $1$, $5$, and $9$ satisfy both, so
`x >= 1 && x <= 9` holds. Yet the interval alone still allows $-2$ and the
residue class alone allows $-3$, so neither component decides the check. A
_reduction_ lets the components sharpen each other, as in the reduced product
@cousot79 @mine17[Def. 6.3, Ex. 6.2]. Here the residue class moves the
interval's bounds to the nearest values that are $1$ modulo $4$, giving
$ivl(1, 9)$. The reduced value stands for the same integers and decides the
check (@tab:reduction).

#listing(lang: "c", claim: "int-reduction-fixpoint", ```
fun main() {
  i32 n = __voblint_nondet_int();
  i32 x = 4 * n + 1;
  if (x >= -2) {
    if (x <= 10) {
      __voblint_check(x >= 1 && x <= 9);
    }
  }
}
```)

// Each printed component of x as (label, value), so the rows follow the printer.
#let _red(mode) = {
  let row = claim-row("int-reduction-" + mode, "74:7")
  let comps = row
    .state
    .split("x=")
    .at(1)
    .split("; ")
    .map(c => {
      let parts = c.split(":")
      (parts.at(0), parts.slice(1).join(":"))
    })
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
      ..never.zip(fix).map((((n, a), (_, b))) => ([#n], raw(a), raw(b))).flatten(),
      table.hline(stroke: 0.5pt),
      [verdict of the check], verdict-chip(v-never), verdict-chip(v-fix),
      table.hline(),
    )
  },
  placement: none,
  caption: [The value of $x$ at the check of the program above, without
    reduction and with the default reduction (claims #claim-ref("int-reduction-never") and
    #claim-ref("int-reduction-fixpoint")), both under wraparound overflow
    (#ctor("Assume_Wraparound")). Since `4 * n` may overflow, #ctor("Assume_Top") would
    drop the class (@sec:domain-kinds). Both columns describe the integers $1$, $5$
    and $9$ in the guard's range, but only the reduced value decides the check.],
) <tab:reduction>

Reduction also proves `v == 51` in @fig:stride2. Inside the loop, the guard
`v < 51` leaves $ivl(1, 50)$, and together with "odd" the reduction shrinks
this to $ivl(1, 49)$. The increment then gives $ivl(3, 51)$ instead of
Interval's $ivl(3, 52)$, the loop head settles at $ivl(1, 51)$, and after the
loop only $51$ remains.

A reduction round has two steps. The first sharpens the residue class with a
finite interval, so a class that meets the interval in one value becomes that
value, and one that meets it in none becomes empty. The second moves the
interval's bounds to the nearest members of the class. Through
#isatype("refine_mode") the user chooses whether to skip reduction, reduce
once, or reduce until nothing changes. Every mode keeps every integer a value
stands for (#isathm("it_refine_mode_sound")). Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/cdomain/value/cdomains/int/intDomTuple.ml",
)[`IntDomTuple`]
uses a similar reduced-tuple design with up to six optional components. Int
corresponds to it restricted to the interval and congruence components,
reduces in the same order, and offers the three modes of Goblint's
`ana.int.refinement` setting. Goblint defaults to no reduction, and Voblint to
reducing until nothing changes.

The default mode iterates with HOL's while combinator, which in the logic
returns no result when the rounds never settle, and Int then keeps the
unreduced value. HOL can define this case because a definition may ask whether
some number of rounds reaches a stable value without computing the answer.
Its code equation instead runs the rounds until
they settle, so the generated OCaml may loop where the HOL function returns.
The code equation is a theorem, so, up to the trusted code generator, every
value the generated code does return equals the HOL value, and the soundness theorem, which speaks only about
reports that are returned, applies unchanged. A run that loops gives no
report, as a solve that does not terminate gives none (@sec:termination).

At a machine kind (@sec:domain-kinds), Int's arithmetic computes the interval
first. When the mathematical interval lies in the kind's range, no value
wraps, and the congruence keeps its classical class even where Congruence
alone would return its top
(#fixture("27-signed-overflow/precision/04-int_no_ov_keeps_class.vimp", label: "04-int_no_ov_keeps_class")).
In @fig:domain-kinds, Int keeps $a in 4 ZZ$ and rounds its interval to
$ivl(0, 2^32 - 4)$ (claim #claim-ref("dom-kinds-int")).

Int reduces the result of every conversion, every arithmetic operation, and
every step of the guard refinement. Join, widening, and narrowing work
componentwise, as in Goblint for join and widening. For narrowing, the solver contract forces the choice. The verified
solver relies on the bracket laws $b lle a narrow b lle a$ for $b lle a$
(@sec:widening). Reduction keeps the integers a value stands for but can make
its components smaller in the componentwise order, so a reduced narrowing can
fall below $b$ when $b$ itself is not reduced. The domain library's product of
a sign, an interval, a parity and a congruence (#isatype("int_dom")) gives an
evaluated example. There $b = (top, ivl(-1, 0), "even", top)$ denotes only $0$
and is narrowed against $top$. Reducing the result lets the exact interval
bound sharpen the sign to non-positive, strictly below the sign $top$ of $b$
(#isathm("post_narrow_refinement_would_violate_narrow_ge")). Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/cdomain/value/cdomains/int/intDomTuple.ml#L416-L426",
)[`IntDomTuple`]
does reduce after narrowing. No proof obliges its lattices to satisfy the
bracket laws, so Goblint can make this choice and Voblint cannot.

== The order analysis #thy-badge("Voblint_Analysis_Order", "Order_Analysis") <sec:relational>

None of these domains can express that $x lt.eq y$, because each describes
the variables one at a time. The order analysis keeps a set of such pairs, the
relational state of @sec:rel-state. A guard between two variables adds a pair.
An assignment forgets the pairs involving the changed variable and then asks
the shared query channel how the new value relates to each variable, and every
active analysis, the order analysis included, may answer
(@sec:coop-catalogue). In the program below, the guard `x < y` removes only
the extreme values of the kind from Interval's ranges, so Interval keeps
#state("order-alone-interval", "12:5") and reports
#verdict("order-alone-interval", "12:5") at the first check. The order
analysis records #state("order-alone-order", "12:5") and reports
#verdict("order-alone-order", "12:5").

#listing(lang: "c", claim: "order-alone-order", ```
fun main() {
  i32 x = __voblint_nondet_int();
  i32 y = __voblint_nondet_int();
  i32 z = __voblint_nondet_int();
  if (x < y) {
    __voblint_check(x <= y);
    if (y <= z) {
      __voblint_check(x <= z);
    }
    y = y + 1;
    __voblint_check(x <= y);
  }
  i32 w = x;
  __voblint_check(w == x);
}
```)

Because the analysis does not combine pairs transitively, it cannot prove
`x <= z` under `y <= z`. It holds #state("order-alone-order", "14:7") there
and answers #verdict("order-alone-order", "14:7") (@sec:rel-state). The
assignment `y = y + 1` throws away every pair involving $y$, leaving
#state("order-alone-order", "17:5"). Forgetting is necessary, since at
$y = 2^31 - 1$ the increment wraps to $-2^31$ and `x <= y` fails for $x = 0$.
A copy `w = x` between two variables of one kind, in contrast, records both
orders and gives $w$ the pairs of $x$. The analysis then holds
#state("order-alone-order", "20:3") and proves `w == x`, where Interval answers
#verdict("order-alone-interval", "20:3").

The base domains record different properties, Int lets two of them share
facts, and the order analysis proves relations that no domain over single
variables can express. Run with the numeric domains in one combined state
(@ch:cooperation), it asks them at each assignment how the new value compares
with the other variables, and a check is decided by the meet of all answers.
