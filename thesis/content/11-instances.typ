#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": fixture, isaconst, isalocale, isathm, isatype, listing, site, thy-badge
#import "../lib/figures.typ": int-axis, int-strip, printed-set, verdict as verdict-chip
#import "../lib/math.typ": *
#import "../lib/claims.typ": claim-ref, claim-row

#let verdict(name, loc) = verdict-chip(claim-row(name, loc).verdict)
#let state(name, loc) = absval(raw(claim-row(name, loc).state))


= Numeric and Relational Analyses <ch:instances>

The preceding chapters stated what a domain, an analysis, and a combination of
analyses must prove, and @ch:results showed that every report is sound,
whichever analyses produced it. This chapter introduces and describes the analyses that Voblint currently
implements. A user selects among the
non-relational domains Sign, Interval, Parity, and Congruence, their reduced product
Int, and a relational order analysis. The chapter compares the four base
domains on one loop, then describes how Int lets them exchange facts and how
the order analysis tracks relations between variables, which shows that the
framework is not limited to one value per variable.

== Four non-relational numeric domains <sec:instances-supply>

The four base domains, Sign #thy-badge("Voblint_Domain", "Sign_Lattice"),
Interval #thy-badge("Voblint_Domain", "Interval_Lattice"), Parity
#thy-badge("Voblint_Domain", "Parity_Lattice"), and Congruence
#thy-badge("Voblint_Domain", "Congruence_Lattice"), are the classical
non-relational domains @mine17;
congruences go back to Granger @granger89. The fifth domain, Int, combines all
four. Its value holds one value of each base domain and denotes the
intersection of their meanings (@sec:reduced-product). All five are
non-relational: they describe each variable separately, and the relational
state of the order analysis follows in @sec:rel-state. @fig:gamma shows one
value of each and the integers it stands for.

#figure(
  {
    set text(size: 8.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let (lo, hi) = (-6, 10)
    let row(domain, value, shown: none) = {
      let inside = printed-set(value)
      (
        domain,
        absval(if shown == none { raw(value) } else { shown }),
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
      ..row([Parity], "1+2ℤ", shown: raw("odd")),
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
  caption: [One value of each non-relational domain, as the analyzer prints it, and
    the integers it denotes between $-6$ and $10$. Congruence values print as
    $c + m ZZ$, the integers congruent to $c$ modulo $m$ ($m ZZ$ when $c = 0$),
    and the Parity value shown is that of the odd integers. An end cell is filled when
    the set continues beyond the window. The values are illustrative. The Int value,
    the reduced state of $x$ in the program of @sec:reduced-product, denotes the intersection of its
    components' meanings, here ${1, 5, 9}$.],
) <fig:gamma>

Each of these domains enters Voblint through the interface of
@sec:domain-contract. It instantiates the order classes for its carrier,
supplies its operations as the record #isatype("nonrelational_ops"), and proves
them sound once
(#isalocale("sound_nonrelational_ops")). From this proof, a generic construction
derives the transfer functions of @ch:analysis-interface together with their
executable versions, and makes the domain a sound component of the product
state of @ch:cooperation
(#isathm("sound_nonrelational_ops.dg_analysis_execI")). The only further
obligation concerns the initial state, which must describe the initial stores.

The loop below is the fixture #fixture("12-widening/known-imprecision/05-mine_ex410_stride2_parity.vimp", label: "05-mine_ex410_stride2_parity.vimp"),
adapted from Goblint's regression test #link("https://github.com/goblint/analyzer/blob/d155e9e/tests/regression/56-witness/29-mine-tutorial-ex4.10.c")[`56-witness/29-mine-tutorial-ex4.10.c`]
(revision `d155e9e`) after Example 4.10 of Miné's tutorial @mine17. In every
run, $v$ takes the odd values $1, 3, dots, 51$ and the loop exits with
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
#let _s-cell(dom, loc) = {
  let s = claim-row("dom-stride2-" + dom, loc).state
  absval(raw(if dom == "parity" { parity-name(s) } else { s }))
}
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
        [#(upper(d.first()) + d.slice(1))],
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

== Combining the domains in a reduced product #thy-badge("Voblint_Domain", "Int_Lattice") <sec:reduced-product>

An Int value (#isatype("int_dom")) holds one value of each base domain and
stands for the integers that all four allow. Running the four side by side
would be sound, but each would work only with its own value, so a fact that
needs two of them would not be found. @fig:stride2 shows this: no
base domain alone proves `v == 51`. In the program below, the guards keep
$x$ between $-2$ and $10$, and the assignment makes $x$ one more than a
multiple of $4$. Only $1$, $5$, and $9$ satisfy both, so `x >= 1 && x <= 9`
holds. Yet the interval alone still allows $-2$, and the residue class alone
allows $-3$, so neither component can decide the check.

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

#let _red-verdict(mode) = claim-row("int-reduction-" + mode, "68:7").verdict

A _reduction_ lets the components sharpen each other, as in the reduced product
@cousot79 @mine17[Def. 6.3, Ex. 6.2]. Here the residue class moves the
interval's bounds to the nearest values that are $1$ modulo $4$, giving
$absval(ivl(1, 9))$, and the now-positive interval makes the sign positive.
The reduced value stands for the same integers but decides the check. Without
reduction, the analyzer reports #verdict-chip(_red-verdict("never")) there, and
with it #verdict-chip(_red-verdict("fixpoint")) (claims
#claim-ref("int-reduction-never") and #claim-ref("int-reduction-fixpoint")).
Reduction also proves `v == 51` in @fig:stride2. Inside the loop, "odd"
shrinks $absval(ivl(1, 50))$ to $absval(ivl(1, 49))$, so the loop head settles
at $absval(ivl(1, 51))$ and only $51$ remains after the loop.

Int thus combines its components differently from the cooperating analyses of
@ch:cooperation. There, separate analyses keep separate states and exchange
facts only through answers to queries, where a transfer asks one. Int is a
single domain whose value holds all four components, and it reduces after
every arithmetic operation and guard. A fact such as "odd" therefore sharpens
the interval stored in the value itself, inside expression evaluation, and not
just the answer to one query. Goblint draws the same line. Its integer
domains form one value domain inside its base analysis, whereas its MCP
combines whole analyses.

A reduction round passes information in two steps. It first combines the range
information of Sign and Interval and uses it to sharpen Sign, Interval, and
Parity. It then intersects the residue class with the parity and uses the
result to sharpen Interval, Parity, and Congruence. The user chooses how often
these rounds run: never, once, or until the value stops changing, which is the
default. Every mode keeps the integers a value stands for and only makes the
value smaller (#isathm("refine_exact"), #isathm("refine_reductive")).

The design follows Goblint's integer domain
#link("https://github.com/goblint/analyzer/blob/5503dec/src/cdomain/value/cdomains/int/intDomTuple.ml")[`IntDomTuple`] at revision `5503dec`. Goblint combines up to six optional components, each enabled by an option. Int always carries
its four components, and Sign and Parity have no counterpart there. Goblint's
option `ana.int.refinement` offers the same three modes, but Goblint defaults
to no reduction, whereas Voblint defaults to repeating rounds until nothing
changes.

In the generated OCaml, the default mode iterates without a termination proof,
so on some inputs the analyzer might not return. Soundness is unaffected, since
the theorem only speaks about returned reports (@fig:intro-trust).

Int reduces the result of every arithmetic operation and of the guard filter,
but not the result of a join, a widening, or a narrowing, which all work
componentwise. For join and widening, Goblint makes the same choice. After a
narrowing, however, Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5503dec/src/cdomain/value/cdomains/int/intDomTuple.ml#L421-L431",
)[`IntDomTuple`]
performs a reduction that Voblint cannot mirror. The verified TD solver requires the narrowing
$a narrow b$ of values $b lle a$ to lie between $b$ and $a$ (@sec:widening).
Reduction only makes a value smaller, so it can push the narrowed value below
$b$ and break this law
(#isathm("post_narrow_refinement_would_violate_narrow_ge")). Goblint is not bound by the law, because no proof constrains its lattices,
and its answers may thus be more precise.

== Order constraints as a relational state #thy-badge("Voblint_Domain", "Order_Lattice") <sec:rel-state>

#let _order = 0.7pt + vb.neutral
None of the earlier domains can express that $x <= y$, because each describes the
variables one at a time (@fig:rel-vs-nonrel). A relational state records such relations, so its concretization maps the
whole state to a set of stores at once. A value of type #isatype("relc") is a
set $P$ of variable pairs, where $(x, y)$ stands for $x <= y$, and describes
the stores that satisfy every pair (#isaconst("gamma_relc")):
$
  conc(ctor("RelC")(P)) = setcomp(s, forall (x, y) in P. s(x) <= s(y)),
  quad conc(ctor("RelBot")) = emptyset.
$
Below, the pair $(x, y)$ is written $x <= y$.

More pairs describe fewer stores, so the order is reverse inclusion:
$ctor("RelC")(P) lle ctor("RelC")(Q)$ exactly when $Q subset.eq P$
(#isaconst("less_eq_relc")), with #ctor("RelBot") below every value and
$ltop = ctor("RelC")(emptyset)$, which constrains nothing. The join keeps the
pairs both operands share,
$ctor("RelC")(P) ljoin ctor("RelC")(Q) = ctor("RelC")(P inter Q)$
(#isaconst("sup_relc")).

The carrier does not close its pairs under transitivity (@fig:rel-state). The
values $absval({x <= y, y <= z})$ and $absval({x <= y, y <= z, x <= z})$ therefore denote the
same stores but are different values. The join can also forget an implied
relation. The join of $absval({x <= y, y <= z})$ and $absval({x <= y, x <= z})$ keeps only
their common pair and is $absval({x <= y})$, although both operands imply $x <= z$. The
order analysis is therefore not as precise as a closed relational domain could
be. It demonstrates that the framework supports relational
states.

Pairs enter only at guards, and an assignment to $x$ removes every pair that
mentions $x$, so $P$ is finite in every value the analysis constructs, and generated code can
store it as a list.

#let _rnode(pos, name, body) = node(pos, text(size: 7pt, body), name: name, inset: 3pt)
#figure(
  diagram(
    spacing: (5mm, 6mm),
    _rnode((1.5, 0), <r-top>, absval($ltop = ctor("RelC")(emptyset)$)),
    _rnode((0, 1), <r-xy>, absval(${x <= y}$)),
    _rnode((1.5, 1), <r-yz>, absval(${y <= z}$)),
    _rnode((3, 1), <r-xz>, absval(${x <= z}$)),
    _rnode((0, 2), <r-xy-yz>, absval(${x <= y, y <= z}$)),
    _rnode((1.5, 2), <r-xy-xz>, absval(${x <= y, x <= z}$)),
    _rnode((3, 2), <r-yz-xz>, absval(${y <= z, x <= z}$)),
    _rnode((1.5, 3), <r-all>, absval(${x <= y, y <= z, x <= z}$)),
    _rnode((0.5, 4), <r-all-yx>, absval(${x <= y, y <= z, x <= z, y <= x}$)),
    _rnode((2.5, 4), <r-all-zy>, absval(${x <= y, y <= z, x <= z, z <= y}$)),
    _rnode((3.6, 4), <r-all-more>, $dots.c$),

    _rnode((0.5, 4.8), <r-down1>, $dots.v$),

    _rnode((2.5, 4.8), <r-down2>, $dots.v$),

    _rnode((1.5, 5.6), <r-nine>, [all nine pairs, $x = y = z$]),

    _rnode((1.5, 6.4), <r-bot>, absval(ctor("RelBot"))),
    ..(<r-xy>, <r-yz>, <r-xz>).map(n => edge(<r-top>, n, "-", stroke: _order)),
    edge(<r-xy>, <r-xy-yz>, "-", stroke: _order),
    edge(<r-xy>, <r-xy-xz>, "-", stroke: _order),
    edge(<r-yz>, <r-xy-yz>, "-", stroke: _order),
    edge(<r-yz>, <r-yz-xz>, "-", stroke: _order),
    edge(<r-xz>, <r-xy-xz>, "-", stroke: _order),
    edge(<r-xz>, <r-yz-xz>, "-", stroke: _order),
    edge(<r-xy-yz>, <r-all>, "-", stroke: _order),
    edge(<r-xy-xz>, <r-all>, "-", stroke: _order),
    edge(<r-yz-xz>, <r-all>, "-", stroke: _order),
    edge(<r-all>, <r-all-yx>, "-", stroke: _order),
    edge(<r-all>, <r-all-zy>, "-", stroke: _order),
    edge(<r-all-yx>, <r-down1>, "-", stroke: _order),
    edge(<r-all-zy>, <r-down2>, "-", stroke: _order),
    edge(<r-down1>, <r-nine>, "-", stroke: _order),
    edge(<r-down2>, <r-nine>, "-", stroke: _order),
    edge(<r-nine>, <r-bot>, "-", stroke: _order),
  ),
  kind: image,
  placement: auto,
  caption: [The relational states over the variables $x$, $y$, and $z$,
    ordered bottom to top by reverse inclusion. Each #ctor("RelC") value is
    drawn as its set of pairs. The upper part shows all values built from
    $x <= y$, $y <= z$ and $x <= z$. Values with other pairs, such as $y <= x$, are
    drawn only below the lowest of these, and the dots stand for the rest.
    Nine pairs exist, including $x <= x$, so the values are finitely many, and
    the lowest #ctor("RelC") value holds all nine and denotes the stores with
    $x = y = z$.],
) <fig:rel-state>

The emptiness
test only compares with #ctor("RelBot") (#isathm("is_empty_relc_gamma")).
Unlike the pointwise state, the carrier has a single representation of
unreachability, so it needs no lifting.

A relational state stores no value per variable, so it cannot evaluate an
expression to an abstract value, and its transfers work on the pairs
directly. An assignment to $x$ invalidates every relation that involves $x$,
so it forgets every pair that mentions $x$. New relations come from guards. On
the true arm of `if (x < y)`, the analysis knows that $x$ is smaller than $y$
and records this by meeting its state with $absval(ctor("RelC"){x <= y})$
(#isaconst("assume_step")). Since the carrier stores only non-strict pairs, it
keeps $x <= y$ and loses the strictness, which costs precision but not
soundness. This guard filter meets the same soundness statement as the
numeric guard filter of @sec:branches (#isathm("relc_branch_step_sound")). The type
instantiates the solver's classes and #isalocale("executable_domain") of
@fig:domain-carrier, but it is not a numeric domain.

== Proving order relations between variables #thy-badge("Voblint_Analysis_Relational", "Rel_Order_Local") <sec:relational>

@sec:rel-state introduced the relational state as an abstract domain. This
section builds the order analysis on top of it and demonstrates it on a
program. After an
assignment has forgotten the pairs involving the changed variable, it asks the
shared channel how the new value relates to each variable, and
every selected analysis, the order analysis included, may give an answer
(@sec:coop-mcp). In the program below, the guard `x < y` tells Interval
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
`x <= z` under `y <= z`. It holds #state("order-alone-order", "14:7") there
and answers #verdict("order-alone-order", "14:7") (@sec:rel-state). The assignment
`y = y + 1` throws away every pair involving $y$, leaving
#state("order-alone-order", "17:5"). A copy, in contrast, yields pairs in both
directions. At `w = x`, the assignment asks, for the variable $x$ itself,
whether `x <= x` holds in each direction. The order analysis answers yes to
both, because it treats a variable as ordered with itself, so it records
#state("order-alone-order", "20:3") and proves `w == x`, where Interval
answers #verdict("order-alone-interval", "20:3").

The base domains record different properties, Int lets them share these
facts, and the order analysis proves relations that no non-relational
domain can express. A user does not have to choose between them. The
product state and the channel of @ch:cooperation let Int and the order
analysis run together. They exchange facts
through queries, and every check is decided by the meet of their answers. Selecting both gets the most out of the analyses Voblint currently
ships, although no theorem guarantees that a combination is more precise than
its parts (@sec:coop-mcp).
