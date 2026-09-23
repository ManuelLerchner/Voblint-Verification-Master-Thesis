#import "../lib/math.typ": *
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/figures.typ": int-axis, int-strip, printed-set
#import "../lib/sources.typ": thy
#import "../lib/theme.typ": vb

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

= Abstract Domains <ch:domains>

@ch:traces reduced soundness to five obligations over arbitrary sets of stores.
An analyzer computes with finite descriptions instead, and its solver
(@ch:solving) compares, joins, widens and narrows them without knowing what
they mean. A lattice of descriptions is not enough: an order unrelated to
meaning lets the solver certify a bound that drops a store, and a state can
denote no store without being the lattice's bottom, so a structural test loses
dead code at the next assignment or join (@sec:lift). For RQ3 the question is
which laws a domain must satisfy so that the solver's order inequalities
discharge the obligations, stated so that they mention neither contexts nor the
solver. This chapter derives these laws and names those it deliberately omits.

== What an abstract value means

An abstract integer is useful only through the set of integers it stands for.
The concretization $conc$ assigns that set: the Sign value #signval("≥0")
denotes $setcomp(n, n >= 0)$, the interval $ivl(1, 5)$ denotes
${1, 2, 3, 4, 5}$. @fig:gamma shows one value of each carrier instantiated in
@ch:instances.

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

The solver never touches these sets. Its certificate (@ch:background) is a
family of order inequalities $d lle sol(x)$, while the coverage obligations are
set inclusions. If an edge transfer produces $d$ covering every successor store
and the solver certifies $d lle sol(v)$, concluding that the successor stores
lie in $conc(sol(v))$ needs exactly
$ a lle b quad ==> quad conc(a) subset.eq conc(b). $
Without this law, the order says nothing about the denoted sets. If intervals
were ordered by their lower bounds alone, $ivl(0, 5) lle ivl(0, 3)$ would hold
and a store with value five would disappear. The same law gives joins their
meaning: since $a lle a ljoin b$, it yields
$conc(a) union conc(b) subset.eq conc(a ljoin b)$ (#isathm("gamma_sup_ub1")),
which preserves both predecessors at a merge, so no separate join law is
assumed. Two boundary laws complete the meaning: $conc(lbot) = emptyset$ lets a
contradictory guard answer "no value", and $conc(ltop) = ZZ$ makes "unknown" a
sound answer, for instance for a nondeterministic input. The type class
#isalocale("sound_domain") collects these laws (@fig:domain-contract).

#figure(
  thy("sound_domain"),
  placement: auto,
  caption: [The numeric domain contract, verbatim. The parent class
    #isalocale("executable_domain") supplies order, join, $lbot$, $ltop$, the
    emptiness test #isaconst("is_empty") and the printer
    #isaconst("to_string")\; #isalocale("sound_domain") adds $conc$ and its
    laws, which generated code never needs (@sec:engineering).],
) <fig:domain-contract>

The law for #isaconst("is_empty") makes emptiness a semantic test. A structural
test $a = lbot$ would be sound but would miss empty values: an interval whose
lower bound exceeds its upper bound denotes nothing without being the canonical
bottom, and the interval operations do not normalize such pairs away. Goblint's
lattice signature `Lattice.Bot` likewise declares its bottom test per domain.
Soundness uses only the direction
$#isaconst("is_empty") (a) ==> conc(a) = emptyset$, which justifies discarding
a state. The converse makes the test exact, and exactness is what lets the
analyzer report the unreachability verdicts of @ch:results at all.

Intervals contain infinite ascending chains, so the solver extrapolates
(@sec:widening), and its update rules require the carrier to instantiate
#isalocale("bounded_warrowing"). Its laws are order laws: $a lle a widen b$ and
$b lle a widen b$, and $b lle a narrow b lle a$ whenever $b lle a$. Either
branch of warrowing therefore bounds the value it was given, and monotonicity
of $conc$ turns that bound into set inclusion. Stabilization is not a class
law, and termination becomes a premise (@sec:termination).

These laws are everything a domain value must satisfy for soundness
(@tab:domain-contract). Three familiar requirements are absent. No transfer has
to be monotone: neither the per-operation rules of @sec:whole-state nor the
analysis soundness contract of @sec:sound-core mention monotonicity, and the
vendored solver's partial-correctness argument does not assume it.
Monotonicity would matter for termination, which is a premise. No abstraction
function is needed, since no claim of optimal precision is made
(@ch:background), and widening need not stabilize. One requirement goes beyond
what the proofs use: the vendored solver works over a bounded join semilattice,
so joins must be least, although soundness uses only their upper-bound half.
This restricts the carriers. Over unbounded integers, two distinct singletons ${x}$
and ${y}$ have no least upper bound among cofinite exclusion sets: every
$ZZ without {p}$ with $p in.not {x, y}$ bounds both, and no two of these are
comparable. The Int product therefore cannot carry an exclusion-set component
like Goblint's `DefExc` (@app:goblint-alignment).

== From values to stores

The simplest store description assigns one abstract value to each variable.
The type #isatype("abs_state") is such a function, and
#isaconst("gamma_state") reads it as
$ sem(a) = setcomp(s, forall x. s(x) in conc(a(x))). $
Order and join are pointwise, and the meaning is a Cartesian product, so the
construction forgets every relation between variables: joining $(x, y) = (2, 2)$
and $(7, 7)$ admits $(2, 7)$. @sec:relational shows that the framework does not
require this form. A product with one empty factor is empty, so $sem(a)$ is
empty exactly when some $conc(a(x))$ is
(#isathm("is_empty_state_iff_gamma_state_empty")). That test quantifies over
all variable names; @ch:solving supplies a finite equivalent.

== Unreachable program points <sec:lift>

A check is reported dead when no execution reaches it, so the analyzer must
recognize unreachability reliably. The pointwise form offers two encodings, and
neither suffices. The all-bottom state is too narrow: backward filtering
(below) typically empties one variable, and ${x |-> lbot, y |-> ltop}$ is empty
without being all-bottom. Any empty state is too fragile: the assignment
`x = 1` turns that state into ${x |-> signval("+"), y |-> ltop}$ and makes dead
code live again, and a pointwise join of two differently empty arms restores both
variables (@fig:domain-reachability). Both failures are sound but lose the
reachability fact.

#let _r = claim-row("dom-disjunct-sign", "13:5")
#figure(
  table(
    columns: (auto, 1fr, 1fr),
    align: (left, left, left),
    stroke: none,
    table.hline(),
    [*after*], [*pointwise states only*], [*lifted and normalized*],
    table.hline(stroke: 0.5pt),
    [`x == 0 && x == 1`], [${x |-> lbot, y |-> ltop}$], [#ctor("Bot")],
    [`y == 0 && y == 1`], [${x |-> ltop, y |-> lbot}$], [#ctor("Bot")],
    [join of both arms], [${x |-> ltop, y |-> ltop}$], [#ctor("Bot")],
    [check `x == 5`], [`UNKNOWN`], [#raw(_r.verdict)],
    table.hline(),
  ),
  placement: auto,
  caption: [Sign states inside
    `if ((x == 0 && x == 1) || (y == 0 && y == 1))` with $x$, $y$
    unconstrained. The middle column is a hand calculation; the last verdict is
    the analyzer's output (claim `dom-disjunct-sign`).],
) <fig:domain-reachability>

The fix keeps reachability apart from the store description. The datatype #isatype("lifted") adds an
outer constructor #ctor("Bot"), meaning "unreachable", below every
#ctor("Lifted") payload, with $conc(ctor("Bot")) = emptyset$. #ctor("Bot") is
the identity of the lifted join, and #isaconst("transfer_lift") passes it
through without running the payload transfer. On a #ctor("Lifted") payload it
runs the transfer and then #isaconst("normalize_lift"), which replaces a result
the emptiness test classifies as empty by #ctor("Bot"). This is Goblint's
`Deadcode` exception turned into a value: a Goblint transfer raises it on
reaching bottom, and a lifted transfer returns #ctor("Bot"). Joins preserve
normalization (#isathm("normalized_lift_sup")), and for a normalized value,
denoting no store is the same as being #ctor("Bot")
(#isathm("normalized_state_lift_bot_iff")), so the structural test is exact and
dead code stays dead. No theorem states the invariant for solved values. The
published result instead canonicalizes each value it reads back
(#isaconst("canonicalize_lift")), which leaves its concretization unchanged.
Normalization is a precision device: soundness of a lifted transfer reduces to
soundness of the payload transfer and to the sound direction of the emptiness
law, and a `DEAD` verdict needs only $conc(ctor("Bot")) = emptyset$.

== Branches: learning from a guard

A guard changes no variable, yet the stores that pass it satisfy it. In

#align(center, block(width: 80%, listing(
  "x = __voblint_nondet_int();\nif (0 < x) { y = x; } else { y = 0 - x; }\n__voblint_check(y >= 0);",
  lang: "c",
  claim: "dom-guard-sign",
)))

$y$ is always $|x|$. A branch transfer that only evaluates the guard keeps
$x = ltop$ in both arms, and the check is `UNKNOWN`. The locale
#isalocale("backward_domain") asks a domain for inverse operators: given
abstract operands and a required result, return refined operands that still
contain every concrete pair producing it. It also asks for a forward evaluator
#isai("aval_abs") of expressions, a truth test #isai("tobool") that may answer
definitely true or false, and an intersection that keeps every concrete value
both operands share (#isalocale("semantic_intersection")) without having to be
the lattice meet. Sign refines $x$ to #signval("+") on
the true arm and #signval("≤0") on the false arm, $y$ joins to #signval("≥0"),
#let _g = claim-row("dom-guard-sign", "18:3")
and the analyzer reports #raw(_g.verdict) with #raw(_g.state).

The generic filters #isaconst("afilter") and #isaconst("bfilter") push these
requirements through an expression once for every domain, with contract
#isathm("bfilter_sound"):
#align(
  center,
  isai(
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = res \<Longrightarrow> s \<in> \<lbrakk>bfilter e res \<sigma>\<rbrakk>",
  ),
)
A filter may keep stores that fail the guard but never drops one that passes. A
disjunction filters each arm and joins. Before joining, #isaconst("bfilter")
drops an arm that the forward gate #isaconst("feasible") rejects, one whose
forward value is empty or whose truth test contradicts the required polarity,
as Goblint's backward evaluation of guards drops a contradictory arm. The gate
looks only forward, so an arm can pass it and still be emptied by backward
refinement, and the pointwise join then produces the leak of
@fig:domain-reachability. The lifted filter #isaconst("bfilter_lifted")
therefore normalizes each arm to #ctor("Bot") before the join. The correction
cannot be placed in #isaconst("bfilter"): emptiness of a pointwise state quantifies
over all variable names and has no code equation, so it would make every case
of the filter non-executable. The executable filter uses the finite emptiness
test of @ch:solving instead.

The inverse operators form a locale, while $conc$ is a type-class operation: a
carrier has one meaning but may have several sound backward interpretations,
as Int has one per reduction policy #isatype("refine_mode") (@ch:instances).

== Checks: asking instead of assuming

A branch assumes its condition. A check must decide whether the current
description already implies it. Filtering answers the wrong question, since it
refines the state whether or not the condition was known. The locale
#isalocale("abstract_numeric_queries") adds comparison queries answering
definitely true, definitely false, or unknown. A definite answer $r$ for
less-than must hold for every pair of represented operands:
$ i in conc(a) and j in conc(b) quad ==> quad (i < j) = r, $
and equality has the same obligation. A domain gets these queries without
extra work: every #isalocale("backward_domain") yields sound queries by reading four
judgments (definitely less, definitely not less, and the same for equality)
off its inverse operators, defined once in
#isalocale("numeric_query_judgments"). Int uses these derived queries; Sign
and Interval supply more precise judgments. Queries may be incomplete: Congruence
#let _c = claim-row("dom-even-odd-congruence", "20:3")
stores the disjoint classes #raw(_c.state) for `x = 2 * n; y = 2 * n + 1`, yet
its equality query decides only between single integers, so `x != y` stays
#raw(_c.verdict).

An empty operand makes every definite answer vacuously sound, so a verdict
never implies that its check is reached (@sec:verdicts).

#figure(
  table(
    columns: (46%, 1fr),
    align: (left, left),
    stroke: none,
    inset: (x: 4pt, y: 3pt),
    table.hline(),
    [*requirement*], [*what the proofs use it for*],
    table.hline(stroke: 0.5pt),
    [$a lle b ==> conc(a) subset.eq conc(b)$],
    [turns each certified inequality $d lle sol(x)$ into an inclusion; with
      $a lle a ljoin b$ it keeps both predecessors at a merge],
    [$conc(lbot) = emptyset$], [lets $lbot$ answer "no value" for a contradictory guard],
    [$conc(ltop) = ZZ$],
    [makes $ltop$ sound for nondeterministic input and for callee locals at entry],
    [#isaconst("is_empty") $a ==> conc(a) = emptyset$],
    [discarding a state, normalizing to #ctor("Bot") (@sec:lift)],
    [$conc(a) = emptyset ==>$ #isaconst("is_empty") $a$],
    [exactness: `DEAD` is reported for every empty state (@sec:verdicts)],
    [order laws of #isalocale("bounded_warrowing")],
    [each solver update bounds the value it was given],
    [least upper bounds], [the vendored solver's value class; soundness uses only the upper bound],
    [sound inverse operators], [#isathm("bfilter_sound"): a guard drops no store that passes it],
    [sound comparison queries], [definite check verdicts (@sec:verdicts)],
    table.hline(stroke: 0.5pt),
    [_not required:_ monotone transfers, stabilizing widening],
    [only termination would use them (@sec:termination)],
    [_not required:_ abstraction function, lattice meet],
    [no optimality claim is made; #isalocale("semantic_intersection") suffices],
    table.hline(),
  ),
  placement: auto,
  caption: [The domain contract. Each requirement is listed with the proof step
    that uses it; the last two rows name what a domain does not need to provide.],
) <tab:domain-contract>

The chapter fixes the domain's share of RQ3 and of K3: the requirements of
@tab:domain-contract. From them follow the join bound
(#isathm("gamma_sup_ub1")), exact unreachability of normalized lifted values
(#isathm("normalized_state_lift_bot_iff")) and the filter contract
(#isathm("bfilter_sound")). None of them mentions a context, an equation or a
solver, so a domain proves them once for every configuration.
@ch:analysis-interface turns these per-value laws into the per-edge form of
#oblig("INTRA") and asks what else an analysis must supply at calls.
