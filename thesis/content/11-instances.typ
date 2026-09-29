#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": fixture, isaconst, isalocale, isasession, isathm, isatype, listing
#import "../lib/figures.typ": int-axis, int-strip, printed-set
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


= Five Domains and an Order Analysis <ch:instances>

@ch:domains claimed that a numeric domain must prove laws about integers only, with no
reference to contexts, routing or the solver. This chapter tests that claim on the
instances. Five domains prove the laws, and each is
interpreted into the analysis assembly of @sec:engineering, so the source-level
theorem of @sec:headline covers it under every context policy and update rule.
Each domain tests a different part of the interface. Sign is finite, so
its join serves as its widening. Interval is infinite and needs widening and
narrowing. Parity refines guards through parity alone. Congruence has an exact meet. The
product Int combines the four under a partial reduction. A relational carrier
(@sec:relational) asks whether the contract depends on pointwise states at all,
and as the order analysis it cooperates with the numeric domains through the
queries of @ch:cooperation.

Precision is compared on regression programs where the difference decides a
check. Every quoted verdict and state is analyzer output, executable evidence
in the sense of @ch:evaluation, and each shows a gain on one program only. Goblint's integer
domain is a tuple of optional components, among them definite values with
exclusion sets, intervals and congruences. Sign and Parity have no upstream
counterpart, and exclusion sets, enumerations, interval sets and bitfields have
none here (@app:goblint-alignment). Exclusion sets are ruled out by the
least-upper-bound requirement of @ch:domains.

== What an instance supplies <sec:instances-supply>

A numeric domain supplies its operations as one record of primitive choices,
#isatype("nonrelational_ops"): the evaluator, the two comparison queries, the
refinement operations of @ch:domains (a truth test, one inverse each for `<`,
`==`, `+`, `-` and `*`, and an intersection), the abstract `min` and `max`, and
the whole-value element. @fig:gamma shows one value of each carrier and the
integers it denotes.

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
  placement: auto,
  caption: [One value of each shipped domain, as the analyzer prints it, and
    the integers it denotes between $-6$ and $10$; an end cell is filled when
    the set continues beyond the window. The Int value denotes the intersection
    of its components' meanings, here ${1, 5, 9}$.],
) <fig:gamma>

The domain proves one certificate about its record,
#isalocale("sound_nonrelational_ops"), whose parts @fig:domain-carrier draws:
the refinement operations form a backward domain whose intersection lies below
both operands (#isalocale("sound_refinement")), the queries are sound checks
over the evaluator (#isalocale("sound_check_query")), and the abstract `min`
and `max` are sound (#isalocale("sound_minmax_ops")). The whole-value element
is the top of the carrier. Everything else is derived
once, inside the locale, from the record: the guard filters and the branch transfer, the check
classifier, the transfer of every edge, procedure entry, and executable
versions of the transfer and entry over the store representation of
@ch:solving. The abstract and the executable versions are computed from the
same primitives and agree on every live store
(#isathm("sound_nonrelational_ops.tf_st_for_commute"),
#isathm("sound_nonrelational_ops.enter_st_for_commute")), so no second
implementation needs its own agreement proof. Deriving forward and backward
transfer from certified value operations follows the generic abstract
interpreter of Nipkow and Klein @nipkow14[Sect. 13.5, 13.7]. The executable
counterpart, its commutation and the registration described next are
Voblint's. @fig:instance-pipeline shows the chain.

The certificate asks for soundness alone.
#isalocale("mono_nonrelational_ops") adds that the evaluator, `min`, `max` and
the refinement operations are monotone (#isalocale("mono_minmax_ops"),
#isalocale("mono_refinement")), and derives monotone transfer functions
(#isathm("mono_refinement.branch_mono")). Sign, Interval, Parity and
Congruence interpret the monotone locale. Int interprets the sound one once,
parametric in its refinement mode. Monotonicity is proved for the two modes
without fixpoint iteration (#isathm("int_dom_mono_ops")) and not for the
fixpoint mode (@sec:reduced-product). No soundness theorem uses these
monotonicity facts. They match the hypotheses of
#isathm("routed_node_rhs_mono_eq"), which prepares the vendored least-solution
theorem for the solver without widening, and the analyzer does not use that
solver.

Registering a certified domain with the pipeline of @sec:engineering is one
rule. #isathm("sound_nonrelational_ops.dg_analysis_execI") discharges every
obligation of #isalocale("dg_analysis_exec") that concerns the domain:
soundness of the transfer, the two commutations with the readback, and
correctness of the check classifier. Six obligations remain, and each domain's
generated registration discharges them: the routing agreement, that the seeds differ from the analysis global, three facts about the solver (its
result is a partial post-solution, its solved domain is finite, and a
successful executable run lies in that domain), and soundness of the initial
state. Only the last is a fact about the domain's values (for Parity,
#isathm("parity_cinit_gamma")). Each numeric domain is registered once, at the
unit context. Interval is also registered at the entry-state and call-string
contexts. The registration's component is the executable local specification
#isaconst("exec_spec"), and the registration proves it sound
(#isaconst("sound_local_spec")). That component becomes one field of the
combined state of @ch:cooperation. The order analysis of @sec:relational enters
the combined state at the same level, as a local specification with its own
soundness theorem (#isathm("order_spec_sound")). The analyzer interprets
#isalocale("dg_analysis") once per context family for the combination of any
activation list (#isathm("mcp_comp_sound"), @fig:assembly), and the
source-level theorem about #isaconst("run_voblint") is proved from these
interpretations.

#figure(
  {
    set text(size: 7.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let step(pos, name, body, color: vb.neutral) = node(
      pos,
      align(center, body),
      name: name,
      stroke: 0.7pt + color,
      fill: color.lighten(93%),
      corner-radius: 2pt,
      inset: 4pt,
    )
    let note(body) = text(size: 7pt, fill: vb.muted, body)
    let lab(body) = text(size: 7pt, fill: vb.muted, body)
    let arrow(from, to, ..args) = edge(from, to, "->", stroke: 0.6pt + vb.neutral, ..args)
    diagram(
      spacing: (8mm, 7mm),
      step((1, 0), <ip-ops>, [primitives #isatype("nonrelational_ops") \
        #note[evaluator, queries, refinement operations, `min`, `max`, top]]),
      step(
        (1, 1),
        <ip-cert>,
        [certificate #isalocale("sound_nonrelational_ops") \
          #note[optionally #isalocale("mono_nonrelational_ops")]],
        color: vb.proved,
      ),
      step((0, 2), <ip-abs>, [abstract operations \ #note[branch, checks, transfer, entry]]),
      step((2, 2), <ip-exec>, [executable operations \ #note[transfer, entry]]),
      step(
        (1, 3),
        <ip-reg>,
        [registration #isalocale("dg_analysis_exec") \
          #note[by #isathm("sound_nonrelational_ops.dg_analysis_execI") and six obligations]],
        color: vb.proved,
      ),
      step((1, 4), <ip-field>, [sound local specification \
        #note[one field of the combined state]]),
      step((2.6, 4), <ip-order>, [order analysis \ #isaconst("order_spec")]),
      arrow(<ip-ops>, <ip-cert>),
      arrow(<ip-cert>, <ip-abs>, label: lab[derives], label-side: right),
      arrow(<ip-cert>, <ip-exec>, label: lab[derives], label-side: left),
      edge(
        <ip-abs>,
        <ip-exec>,
        "<->",
        stroke: (paint: vb.proved, thickness: 0.6pt, dash: "dotted"),
        label: lab[agree on live stores],
        label-side: left,
      ),
      arrow(<ip-abs>, <ip-reg>),
      arrow(<ip-exec>, <ip-reg>),
      arrow(<ip-reg>, <ip-field>, label: lab(isaconst("exec_spec")), label-side: left),
      arrow(<ip-order>, <ip-field>, label: lab(isathm("order_spec_sound")), label-side: right),
    )
  },
  kind: image,
  placement: auto,
  caption: [How a numeric domain becomes a field of the combined state. Solid
    arrows lead from what is supplied to what is derived from it; the dotted
    arrow is the commutation of the abstract and executable operations. Green
    boxes are the two proofs a domain passes through. The order analysis
    supplies its local specification directly. Schematic.],
) <fig:instance-pipeline>

Every domain refines guards with the same generic filter, so the domains'
guard precision differs only in which refinement operations are precise
(@fig:refine-profile). An inverse that a domain cannot sharpen returns its
operands unchanged, as #isaconst("inv_conservative") does, and the interface
admits this for every operator.
Sign and Interval refine comparisons and equalities and leave the operands of
arithmetic unchanged (#isaconst("ivl_refine_ops")). Parity and Congruence do
the reverse: a comparison says nothing about a residue class, while an
equality, a sum, a difference or a product can fix one operand's class from the
other's (#isaconst("parity_refine_ops")). In both, an equality refines only
when it held. Parity refines a product only when it is odd, since then both
factors are odd (#isaconst("inv_times_parity")). Int refines through its
components; its arithmetic inverses are those of its Parity and Congruence components.

#figure(
  {
    set text(size: 8.5pt)
    let r = [refines]
    let i = [identity]
    table(
      columns: 6,
      align: (left,) + (center,) * 5,
      stroke: none,
      table.hline(),
      [*domain*], [`<`], [`==`], [`+`], [`-`], [`*`],
      table.hline(stroke: 0.5pt),
      [Sign], r, r, i, i, i,
      [Interval], r, r, i, i, i,
      [Parity], i, r, r, r, r,
      [Congruence], i, r, r, r, r,
      [Int], r, r, r, r, r,
      table.hline(),
    )
  },
  placement: auto,
  caption: [Which inverse operator of each domain can shrink an operand
    ("refines") and which returns its operands unchanged ("identity"). Read
    from the refinement operations in the theories.],
) <fig:refine-profile>

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
answers #verdict("dom-even-odd-parity", "20:3"). Parity also refines guards
through the generic filter (@fig:refine-profile). On `x + 1 == y` with `y` even,
the inverse of `+` (#isaconst("inv_plus_parity")) makes `x` odd, which
#isathm("bfilter_parity_plus_narrows") checks by evaluation. Interval, whose
inverse of `+` is the identity, learns nothing about `x` there. Under the guard
`y + 1 == 3` of @fig:pg-int-refinement, Parity derives
#state("pg-int-refinement-parity", "4:5"). On the contradictory guard of
@fig:domain-reachability, `x == 1` makes `x` odd and `x == 0` then empties it,
so Parity reports the branch #verdict("dom-disjunct-parity", "12:5"), as Sign
does (#verdict("dom-disjunct-sign", "13:5")).

Congruence analysis goes back to Granger @granger89. A value denotes
$setcomp(n, n equiv c med (mod m))$, with $m = 0$ meaning the single integer
$c$; Parity is the case $m = 2$. Larger moduli matter when classes meet: under
`x == y` with $x = 4n + 1$ and $y = 6m + 3$, the common value is
$9 med (mod 12)$ by the Chinese remainder theorem, so a nested test `x == 13`
is unreachable. Parity knows only that both are odd and answers
#verdict("dom-crt-parity", "21:7")\; Congruence filters with
#isaconst("inf_congruence") and answers
#verdict("dom-crt-congruence", "21:7"). The intersection is exact
(#isathm("gamma_inf_congruence")).

== The reduced product <sec:reduced-product>

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
runs the fixpoint mode by default, and its option `--int-refinement` selects
another. Each mode is registered as an analysis of its own
(#isaconst("Int_Analysis"), #isaconst("Int_Once_Analysis"),
#isaconst("Int_Never_Analysis")), because the combined state of @ch:cooperation
keeps one field per analysis. Its soundness needs no monotonicity of reduction,
because no obligation of @ch:domains asks for monotone transfers.

On programs, one round and the fixpoint give the same results in every case we
know of. A chain of refinements is at most two rounds long, since Congruence
never learns from Interval and Parity learns from Interval only at a singleton.
A guard refines twice, once in its inverse operator and once in the
intersection, and the bounds of an arithmetic result already agree with its
congruence. The difference one round leaves shows only on operands no stored
state has (#isathm("mode_never_ne_fixpoint")). No reduction at all differs
visibly: the regression fixtures
#fixture(
  "16-composite-domain/precision/12-refinement_never_keeps_guard_facts_apart.vimp",
  label: "16-composite-domain/precision/12",
)
to
#fixture(
  "16-composite-domain/precision/14-refinement_fixpoint_agrees_with_once.vimp",
  label: "…/14",
)
leave a check unproved without reduction that one round proves. This argument
is not machine-checked. Checks themselves do not reduce: as in Goblint's
`IntDomTuple`, a comparison is decided when one component decides it on its own
value (#isaconst("int_less_true")), so the mode reaches a check only through the
values the transfers stored. Without reduction, a remainder that is $[0, 5]$ in
Interval and $1$ modulo $6$ in Congruence leaves `r == 1` unproved
(#fixture(
  "16-composite-domain/precision/15-refinement_never_answers_checks_per_component.vimp",
  label: "…/15",
)). The fixpoint
mode is total in HOL, returning its input if the iteration never stabilizes,
while the generated code iterates until the value stops changing. That it
always stops is not proved, so reduction is a second place, besides the solve,
where the executable may fail to return (@sec:trust-boundary).

== Why narrowing does not reduce <sec:no-refining-narrow>

Reducing after every operation, including narrowing, would break the solver's
narrowing law, which requires $b lle a narrow b lle a$ whenever $b lle a$.
Reduction only moves down, so the upper half survives; the lower half fails
whenever reduction lowers the narrowed value below $b$. Take $a = ltop$ and let
$b$ hold Sign $signval(top)$, interval $ivl(-1, 0)$ and even parity. Together these
denote only zero, but Sign still says $signval(top)$. Componentwise narrowing returns a
value between $b$ and $a$, and one round of reduction afterwards lowers its
Sign component below $b$'s $signval(top)$. The lemma
#isathm("post_narrow_refinement_would_violate_narrow_ge") checks this by
evaluation.

A stability argument would fix the step if every value reaching narrowing
were already reduced: then monotone reduction would keep $b$ below the result.
The carrier does not maintain that invariant. Join and widening do not reduce,
so a value that reaches narrowing through a widened solver state need not be
stable, and a narrowing built on the invariant would violate the class law at
the instance. The instance therefore narrows componentwise and reduces only
inside transfers and filters. The solver's narrowing law thus determines
where the product may reduce.

== A relational carrier <sec:relational>

Every domain so far is pointwise. The relational state #isatype("relc") of
@sec:rel-state tests whether a relational local state needs any change to the
generic interface. No function from variables to abstract integers appears in
it.

The specification #isaconst("rel_order_spec") discharges the analysis soundness
contract #isalocale("analysis_contract") of the numeric analyses without any
change to the framework, because the contract already ranges over arbitrary
local and shared carriers with a joint concretization (@ch:analysis-interface).
On `if (x < y) { z = 1; } else { z = 0; }` with $x$ and $y$ unconstrained,
Interval learns nothing at the true branch (#isathm("demo_ivl_x_at_branch")),
while the relational carrier records $(x, y)$ there
(#isathm("demo_rel_learns_xy")); both facts are proved by evaluating the
generated solver inside Isabelle. The analysis forgets a variable on
assignment and everything across calls, and its carrier does not close its
pairs under transitivity, so it is not a useful analysis. It only shows that the proved
interface admits a relational local state. Its session
#isasession("Voblint_Analysis_Relational") builds on
#isasession("Voblint_Exec") and does not import
#isasession("Voblint_Nonrelational"), which holds the pointwise transfer
theories the numeric domains share.

The specification #isaconst("rel_order_spec") reads and publishes the shared
component, so it cannot join the combined state of @ch:cooperation, whose
components are pure. The same carrier therefore has a second, local form, the
order analysis (#isaconst("order_spec")), which the analyzer runs as
`order`. It is a local specification directly, built from the conservative
defaults of #isaconst("conservative_local_spec"), with its own soundness
theorem (#isathm("order_spec_sound")); it has no operation record and no
registration of its own (@fig:instance-pipeline). It answers comparisons between variables it has ordered, and at an
assignment $x := e$ it asks the other active analyses how $e$ compares with
each variable and records the pairs the answers confirm (@sec:coop-catalogue).
At calls it keeps no facts, so that it isolates cooperation from relational
call boundaries. Alone it proves little: it cannot compare a variable with a
constant. Its use is as a partner of Interval, in both directions
(#isathm("coop_demo_needs_both"), #isathm("order_asks_needs_both")).

Five domains prove the laws of @ch:domains with facts about integers alone.
Each supplies one operation record, proves one certificate about it and is
registered once; the source-level theorem covers it as a field of the combined
state under every context policy. The instances show that the interface admits
the identity for any inverse operator (Sign and Interval for arithmetic, Parity
and Congruence for comparisons), needs no monotone reduction (Int in the
fixpoint mode) and needs no pointwise store (#isaconst("rel_order_spec"),
#isaconst("order_spec")). The solver's narrowing law restricts where the
product may reduce. The precision differences of this chapter are
executable evidence about single programs; @ch:evaluation collects them with
the machine-checked precision witnesses.
