#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "../lib/math.typ": *
#import "../lib/code.typ": (
  decode-isabelle, isabelle-scripts, isaconst, isai, isalocale, isathm, isatype, listing, oblig,
)
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": definition, theorem
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
they mean. Recall from @sec:abs-int that an abstract value $a$ denotes a set
$conc(a)$ of concrete values. For the numeric domains of this chapter,
$conc(a) subset.eq ZZ$, and @sec:domain-states lifts this meaning pointwise to
stores. An arbitrary lattice of descriptions is not enough, for two reasons.
First, the order must agree with the meaning. The solver only proves
inequalities $a lle b$ in the abstract order, while the obligations of
@ch:traces are inclusions between sets. The class law
$ a lle b ==> conc(a) subset.eq conc(b) $
turns each such inequality into an inclusion (@fig:sign-conc). Second, a
description can describe no store at all without being the lattice's bottom
element: in the state ${x |-> lbot, y |-> ltop}$, variable $x$ has no possible
value, so the state describes no store. If the analyzer only recognizes the
bottom element as unreachable, such a state looks reachable, and after the next
assignment or join the information that the point is dead is gone (@sec:lift).
This chapter derives the laws a domain must satisfy so that the solver's
inequalities discharge the obligations, stated so that they mention neither
contexts nor the solver, and names the laws it omits on purpose.

#let _snode(pos, name, body) = node(pos, text(size: 8pt, body), name: name, inset: 3pt)
#let _order = 0.7pt + vb.neutral
#let _hit = 1.1pt + vb.accent
#figure(
  diagram(
    spacing: (13mm, 11mm),
    _snode((1, 0), <s-top>, signval($top$)),
    _snode((0.5, 1), <s-le>, signval("≤0")),
    _snode((1.5, 1), <s-ge>, signval("≥0")),
    _snode((0, 2), <s-neg>, signval("−")),
    _snode((1, 2), <s-zero>, signval("0")),
    _snode((2, 2), <s-pos>, signval("+")),
    _snode((1, 3), <s-bot>, signval($bot$)),
    _snode((5.5, 0), <c-top>, $ZZ$),
    _snode((6.2, 1), <c-le>, $setcomp(n, n <= 0)$),
    _snode((4.8, 1), <c-ge>, $setcomp(n, n >= 0)$),
    _snode((6.7, 2), <c-neg>, $setcomp(n, n < 0)$),
    _snode((5.5, 2), <c-zero>, ${0}$),
    _snode((4.3, 2), <c-pos>, $setcomp(n, n > 0)$),
    _snode((5.5, 3), <c-bot>, $emptyset$),
    ..(
      ("top", "le"),
      ("top", "ge"),
      ("le", "neg"),
      ("le", "zero"),
      ("ge", "zero"),
      ("neg", "bot"),
      ("zero", "bot"),
      ("pos", "bot"),
    )
      .map(((hi, lo)) => (
        edge(label("s-" + hi), label("s-" + lo), "-", stroke: _order),
        edge(label("c-" + hi), label("c-" + lo), "-", stroke: _order),
      ))
      .flatten(),
    edge(<s-ge>, <s-pos>, "-", stroke: _hit, label: $lle$, label-side: left),
    edge(<c-ge>, <c-pos>, "-", stroke: _hit, label: $subset.eq$, label-side: right),
    edge(<s-top>, <c-top>, "|-->", stroke: 0.7pt + vb.muted, label: $conc$),
    edge(<s-ge>, <c-ge>, "|-->", stroke: 0.7pt + vb.accent),
    edge(<s-pos>, <c-pos>, "|-->", stroke: 0.7pt + vb.accent),
    edge(<s-bot>, <c-bot>, "|-->", stroke: 0.7pt + vb.muted),
  ),
  kind: image,
  placement: none,
  caption: [The Sign domain (left) and the sets of integers its values denote
    (right, drawn mirrored), each ordered bottom to top. The solid lines are
    the orders $lle$ and $subset.eq$. The dashed arrows show four instances of
    $conc$, which maps every value to the set at the mirrored position.
    Since $conc$ is monotone, the blue step
    $signval("+") lle signval("≥0")$ becomes the inclusion
    $conc(signval("+")) subset.eq conc(signval("≥0"))$. Adapted from the
    parity figure of @nipkow14[Fig. 13.5].],
) <fig:sign-conc>

== The domain interface <sec:domain-contract>

A domain must supply the operations the analysis computes with and the laws
that connect them to $conc$. Voblint states them in three layers. The carrier
type of abstract values instantiates a hierarchy of type classes: order classes
from Isabelle's HOL library, two classes of Voblint's own
(@fig:domain-contract) and the update classes of the vendored solver. Over that
carrier, a forward interface evaluates expressions and tests truth
(@fig:forward-contract), and a backward domain refines values at guards
(@fig:backward-contract). Every expression-level use of a domain builds on the
same forward interface, so a domain proves its laws once and the transfer
functions, the guard filters and the check layer reuse them.
@fig:domain-carrier shows every operation and law of the three layers in the class or locale that declares it.

#block(breakable: false)[
  #definition(name: [Numeric domain], isa: "numeric_domain", cmd: "class")[
    A numeric domain is an executable join semilattice of abstract integers
    with a concretization into sets of integers that respects its order, its
    bottom, its top and its emptiness test.
  ]

  #figure(
    {
      show raw.where(block: true): set text(size: 6.2pt)
      thy("executable_domain")
      thy("numeric_domain")
    },
    kind: image,
    placement: none,
    caption: [The declarations of #isalocale("executable_domain") and
      #isalocale("numeric_domain"), lifted from the theory. The lattice classes
      appear as the sort of #raw("'a") because the solver's #isalocale("widening") and
      #isalocale("narrowing") constrain their type variable to #isalocale("order")
      instead of extending it, and a class built on them must do the same to use
      $lbot$ and $ltop$. The sort still makes them superclasses.],
  ) <fig:domain-contract>
]

#definition(name: [Forward interface], isa: "sound_evaluator", cmd: "locale")[
  A sound evaluator maps an expression and an abstract state to an abstract
  value that contains the expression's value in every store the state
  describes. A sound truth test may answer that every value an abstract value
  denotes is non-zero, or that every one is zero.
]

#figure(
  {
    show raw.where(block: true): set text(size: 6.2pt)
    thy("sound_evaluator")
    thy("sound_truth_test")
  },
  kind: image,
  placement: none,
  caption: [The declarations of the forward evaluator
    #isalocale("sound_evaluator") and the truth test #isalocale("sound_truth_test"),
    lifted from the theory.],
) <fig:forward-contract>

The evaluator is stated over any state type $d$ together with a parameter
#isai("\<gamma>\<^sub>S") that gives the set of stores #isai("\<gamma>\<^sub>S d") a
state describes. The numeric domains instantiate it with their pointwise
abstract states and their state concretization, which @sec:domain-states
defines. The check layer states its evaluator requirement over an arbitrary
state type through the same locale, and every shipped domain instantiates it at
the pointwise states. The numeric queries that decide checks (@sec:queries)
are a further forward operation outside this definition.

#block(breakable: false)[
  #definition(name: [Backward domain], isa: "backward_domain", cmd: "locale")[
    A backward domain extends the forward interface with an intersection that
    keeps every value both operands admit and with inverse operators that refine
    the operands of a comparison or an arithmetic operation to values that still
    contain every concrete pair producing the required result.
  ]
]

#figure(
  {
    show raw.where(block: true): set text(size: 6.2pt)
    thy("semantic_intersection")
    thy("backward_domain")
  },
  kind: image,
  placement: none,
  caption: [The declarations of #isalocale("semantic_intersection") and
    #isalocale("backward_domain"), which combines the intersection and the
    forward interface with the inverse operators, lifted from the theory.],
) <fig:backward-contract>

The inverse operators form a locale, while $conc$ is a class operation, because
Int has one sound backward interpretation per reduction policy
#isatype("refine_mode") (@ch:instances). A class would allow only one
instance per type. The intersection need not be the lattice meet, and the
carrier need not have a meet at all (@sec:branches).

// Everything a domain supplies, as a UML inheritance tree. Each node is a
// class or locale read from its lifted declaration and lists only the members
// it declares; the edges are its declared parents, followed from the
// declarations a domain instantiates, so the figure cannot drift from the
// sources. Only the roots and node positions are chosen, in
// shared/domain-tree.toml.
#let _decl(src) = {
  // The first line names the source file, and with it the origin.
  let (path, ..rest) = src.split("\n")
  let origin = if path.contains("~~/src/HOL/") { "hol" } else if path.contains(
    "vendor/td-verification/",
  ) { "solver" } else { "voblint" }
  let src = rest.join("\n")
  let head = src.match(regex("^(class|locale)\s+(\S+)\s*="))
  let body = src.slice(head.end)
  // The parent expression ends at the `for` clause or the first member; the
  // `for` clause only renames inherited parameters, so members start after it.
  let stop = body.match(regex("\b(for|fixes|assumes)\b"))
  let parent-text = if stop == none { body } else { body.slice(0, stop.start) }
  let first = body.match(regex("\b(fixes|assumes)\b"))
  let members = if first == none { "" } else { body.slice(first.start) }
  let (fixes, laws, mode) = ((), (), none)
  let member = regex(
    "\b(fixes|assumes|and)\s+((?:[A-Za-z_]|\\\\<[A-Za-z]+>)(?:[A-Za-z0-9_']|\\\\<\^?[A-Za-z]+>)*)(?:\s*\[[^\]]*\])?\s*(::|:)\s*(\"[^\"]*\"|'[a-z]+)"
      + "(?:\s*\((?:infix[lr]?\s+)?(?:\\\\<open>(.*?)\\\\<close>|\"([^\"]*)\")[^)]*\))?",
  )
  for m in members.matches(member) {
    let (kw, name, _, rhs, n1, n2) = m.captures
    if kw != "and" { mode = kw }
    let entry = (
      name: name,
      rhs: rhs.trim("\"").replace(regex("\s+"), " "),
      notation: if n1 != none { n1 } else { n2 },
    )
    if mode == "fixes" { fixes.push(entry) } else { laws.push(entry) }
  }
  let kind = head.captures.at(0)
  let parents = parent-text
    .split("+")
    .map(p => p.trim().split(regex("\s+")).at(0))
    .filter(p => p != "")
  // The sort a parameter's type variable is constrained to
  // (`'a::numeric_domain`, `'a::{order_bot, order_top}`).
  let sorts = fixes
    .map(f => f
      .rhs
      .matches(regex("'[a-z]+\s*::\s*(\{[^}]*\}|[A-Za-z_]+)"))
      .map(m => m.captures.at(0)))
    .flatten()
    .map(s => s.trim("{").trim("}").split(",").map(c => c.trim()))
    .flatten()
    .dedup()
  (
    name: head.captures.at(1),
    kind: kind,
    origin: origin,
    // In a class the sort of its own type variable becomes a superclass, as
    // for the solver's `widening`; in a locale it is a dependency.
    parents: if kind == "class" { (parents + sorts).dedup() } else { parents },
    fixes: fixes,
    laws: laws,
    bounds: if kind == "class" { () } else { sorts },
  )
}
#let _snip(n) = read("/shared/generated/snippets/" + n + ".thy")
#let _visit(d, acc) = {
  if acc.any(e => e.name == d.name) { return acc }
  for q in d.parents { acc = _visit(_decl(_snip(q)), acc) }
  acc + (d,)
}
#let _tree = toml("/shared/domain-tree.toml")
#let _hierarchy = _tree.roots.fold((), (acc, n) => _visit(_decl(_snip(n)), acc))
#let _rows = _tree.rows
#let _ancestors(n) = {
  let d = _hierarchy.find(e => e.name == n)
  if d == none { () } else { d.parents + d.parents.map(_ancestors).flatten() }
}
#{
  let names = _hierarchy.map(d => d.name)
  let placed = _rows.map(r => r.keys()).flatten()
  let unplaced = names.filter(n => n not in placed)
  let stale = placed.filter(n => n not in names)
  assert(
    unplaced == () and stale == (),
    message: "domain tree positions: unplaced " + repr(unplaced) + ", stale " + repr(stale),
  )
}

#let swatch(c) = box(
  width: 0.8em,
  height: 0.8em,
  baseline: 0.1em,
  radius: 1pt,
  fill: c.lighten(82%),
  stroke: 0.7pt + c,
)

#figure(
  layout(size => context {
    let code(s, fill: vb.plain) = text(fill: fill, raw(decode-isabelle(s)))
    let box-of(d) = {
      let rows = (
        table.cell(colspan: 2, fill: vb.at(d.origin).lighten(82%), align: center, text(
          size: 6.4pt,
          isalocale(d.name),
        )),
      )
      for (items, fill) in ((d.fixes, vb.const), (d.laws, vb.thm)) {
        if items == () { continue }
        rows.push(table.hline(stroke: 0.4pt + vb.at(d.origin)))
        for it in items {
          let head = code(it.name, fill: fill)
          if it.notation != none { head += [ (#code(it.notation))] }
          rows.push(head)
          // A class draws its type variable's sort as arrows, so the
          // signature omits it.
          let rhs = if d.kind == "class" {
            it.rhs.replace(regex("('[a-z]+)\s*::\s*(\{[^}]*\}|[A-Za-z_]+)"), m => m.captures.at(0))
          } else { it.rhs }
          rows.push(code(if fill == vb.const { ":: " + rhs } else { rhs }))
        }
      }
      // Styled inside, so that `measure` sees the size the node is drawn at.
      let t = {
        set text(size: 5.6pt)
        set par(justify: false, leading: 0.4em)
        show: isabelle-scripts
        table(columns: 2, stroke: none, inset: (x: 2.5pt, y: 1.2pt), align: left + top, ..rows)
      }
      // A node that shares its row wraps its statements beyond this width.
      let alone = _rows.any(r => r.len() == 1 and d.name in r)
      let cap = if alone { size.width } else { 0.46 * size.width }
      block(
        width: calc.min(measure(t).width, cap),
        stroke: (
          paint: vb.at(d.origin),
          thickness: 0.7pt,
          dash: if d.kind == "locale" { "dashed" } else { none },
        ),
        radius: 2pt,
        clip: true,
        fill: white,
        t,
      )
    }
    let boxes = (:)
    for d in _hierarchy { boxes.insert(d.name, box-of(d)) }
    let (at, y) = ((:), 0pt)
    for row in _rows {
      let h = calc.max(..row.keys().map(n => measure(boxes.at(n)).height))
      // Physical coordinates grow upwards.
      for (n, x) in row { at.insert(n, (x * size.width, -(y + h / 2))) }
      y += h + 13pt
    }
    let hollow = (inherit: "stealth", stealth: 0, fill: white, size: 7)
    diagram(
      node-inset: 0pt,
      ..for d in _hierarchy {
        (node(at.at(d.name), boxes.at(d.name), name: label(d.name)),)
      },
      ..for d in _hierarchy {
        // An arrow implied by a longer path is left out.
        for p in d.parents.filter(p => not d.parents.any(q => q != p and p in _ancestors(q))) {
          (edge(label(d.name), label(p), marks: (none, hollow), stroke: 0.5pt + vb.neutral),)
        }
        for b in d.bounds.filter(b => b in at) {
          (
            edge(label(d.name), label(b), "-straight", stroke: (
              paint: vb.muted,
              thickness: 0.5pt,
              dash: "dashed",
            )),
          )
        }
      },
    )
  }),
  kind: image,
  placement: auto,
  caption: [Everything a domain supplies over its carrier type #raw("'a"), as a
    UML inheritance tree. Each class (solid) or locale (dashed) lists the
    operations and laws it declares, not the theorems it derives; a solid arrow
    points to a declaration it extends, a dashed one to the class its type
    variable is constrained to. The colour gives where each node is declared:
    #swatch(vb.hol) Isabelle's HOL library, #swatch(vb.solver) the
    vendored solver, #swatch(vb.voblint) Voblint. Nodes and arrows are read from
    the declarations.],
) <fig:domain-carrier>


The HOL classes fix the order structure (@fig:domain-carrier). #isalocale("ord") fixes $lle$ and $<$,
and #isalocale("preorder") and #isalocale("order") make $lle$ a partial order.
In a #isalocale("semilattice_sup") the join $a ljoin b$ lies above both operands
(#isathm("sup_ge1"), #isathm("sup_ge2")) and below every other upper bound
(#isathm("sup_least")). #isalocale("order_bot") and #isalocale("order_top") add
a least element $lbot$ and a greatest element $ltop$. On top of this,
#isalocale("executable_domain") extends the solver's class
#isalocale("warrowing"), which brings the widening $widen$ and the narrowing
$narrow$, and adds the emptiness test #isaconst("is_empty") and the printer
#isaconst("to_string"). This completes what the solver and the generated code
compute with. #isalocale("numeric_domain") adds $conc$ and its
laws (@fig:domain-contract). Generated code never needs $conc$
(@sec:engineering).


The law #isathm("gamma_mono") is the one that turns each certified inequality
$d lle sol(x)$ into the inclusion $conc(d) subset.eq conc(sol(x))$
(@sec:abs-int). With $a lle a ljoin b$ it also gives
$conc(a) union conc(b) subset.eq conc(a ljoin b)$ (#isathm("gamma_sup_ub1")), so
a merge keeps the stores of both predecessors and no separate join law is
needed. The law $conc(lbot) = emptyset$ lets a contradictory guard answer "no
value", and $conc(ltop) = ZZ$ makes "unknown" a sound answer, for instance for
a nondeterministic input or for the locals of a callee at its entry.

The law #isathm("is_empty_correct") makes emptiness a semantic test. A
structural test $a = lbot$ would miss empty values, because a carrier may
represent the empty set in several ways. Voblint's interval type
#isatype("ivl") stores raw bound pairs and never normalizes them. Its bottom
#isaconst("bot_ivl") is the pair $[infinity, -infinity]$, but under
#isaconst("gamma_ivl") every pair with a lower bound above its upper bound also
denotes $emptyset$, and so do $[-infinity, -infinity]$ and
$[infinity, infinity]$, which contain no integer. Goblint's lattice signature
`Lattice.Bot` likewise declares its bottom test per domain. Discarding a state
is sound as soon as the test implies emptiness. The converse makes the test
exact. Voblint uses this exactness to derive that emptiness is downward closed
(#isathm("is_empty_antimono")), which normalization needs (@sec:lift), and in
the correspondence between the executable carrier's canonicalization and
semantic readback (@sec:readback).

Two stronger algebraic requirements come from the solver interface. The
vendored solver is stated over #isalocale("bounded_semilattice_sup_bot"), so
the join must be the least upper bound. It also needs $widen$ and $narrow$ with
the laws of #isalocale("warrowing") (@sec:widening). Because
#isalocale("executable_domain") extends both classes, a domain meets these
requirements by instantiating it, after proving its widening and narrowing
laws. At the semantic-domain layer, the join is used only through the fact
that it lies above both operands. Leastness and the laws of
#isalocale("warrowing") are structural requirements of the solver.

The least-upper-bound requirement excludes some carriers. Consider a simplified
form of Goblint's exclusion-set domain `DefExc`, which describes an integer
either by its exact value, a singleton ${n}$, or by a finite set $F$ of values
it cannot have, the set $ZZ without F$. The singletons ${1}$ and ${2}$ have
many upper bounds in this carrier, among them $ZZ without {3}$ and
$ZZ without {4}$. A least upper bound would have to lie below all of them, and
the only set with this property that still contains $1$ and $2$ is ${1, 2}$.
This set is neither a singleton nor of the form $ZZ without F$, so ${1}$ and
${2}$ have no least upper bound in the carrier. This rules out a direct
singleton/cofinite `DefExc`-style component over Voblint's unbounded
mathematical integers under the current
#isalocale("bounded_semilattice_sup_bot") requirement. Goblint's `DefExc` is
bounded by the range of the integer kind; @app:goblint-alignment discusses this
difference.

The interface has no abstraction function, because Voblint makes no claim of
optimal precision (@sec:abs-int). Termination is a premise of the main theorem
(@sec:termination), so widening need not stabilize. Monotonicity is a separate
layer of every interface: #isalocale("mono_evaluator"),
#isalocale("mono_truth_test") and #isalocale("mono_intersection") add it to the
sound versions. The analysis soundness contract (@sec:sound-core) and
the solver's partial-correctness theorem (@sec:td) use none of these layers.
The refined backward domain #isalocale("backward_domain_refined") and the
transfer interface of @ch:instances impose them, and therefore prove more than
soundness alone requires.

The interface is executable and it can be reasoned about. Sign instantiates the
classes with its seven values and the locale with #isaconst("meet_sign") as
intersection and #isaconst("inv_less_sign") as the inverse of $<$
(@fig:interface-at-work). The first lemma is proved by evaluation: Isabelle
generates code for the Sign operations and runs it. The meet of #signval("≥0")
and #signval("≤0") is #signval("0"), the meet of #signval("+") and
#signval("−") is empty, and when $x < 0$ holds for an unknown $x$, the inverse
refines $x$ to #signval("−"). Such proofs rest on the code generator's
evaluation oracle (@tab:oracles-audit). The second lemma holds for every
domain and follows from the laws alone: a value both operands admit keeps
their intersection non-empty, by #isathm("intersect_sound") and
#isathm("is_empty_correct"). The third lemma obtains the same fact for Sign
without evaluation, by instantiating the second through Sign's interpretation
of the locale. The layers pay off in that interpretation too: Sign's expression
domain already establishes the forward laws, so its backward interpretation
proves only the laws of the intersection and the inverse operators.

#figure(
  {
    show raw.where(block: true): set text(size: 6.2pt)
    thy("sign_interface_regression")
    thy("intersect_shared_not_empty")
    thy("sign_meet_zero_not_empty")
  },
  kind: image,
  placement: auto,
  caption: [Three lemmas about the interface, lifted with their proofs from an
    example theory: concrete Sign operations evaluated by generated code, a
    fact derived from the laws of #isalocale("semantic_intersection") for every
    domain, and its instance for Sign.],
) <fig:interface-at-work>

== From values to stores <sec:domain-states>

The simplest description of a set of stores assigns one abstract value to each
variable. The type #isatype("abs_state") is such a function: an abstract state
$sigma$ maps every variable name $x$ to an abstract value $sigma(x)$. The
function #isaconst("gamma_state") gives it a meaning, the set of stores whose
every variable lies in the concretization of its abstract value:
$ sem(sigma) = setcomp(s, forall x. s(x) in conc(sigma(x))). $
Order and join work variable by variable, so the construction forgets every
relation between variables. Take intervals and a program that sets both
$x$ and $y$ to $1$ on one branch and both to $5$ on the other. After the join,
$sigma(x) = sigma(y) = [1, 5]$, which also admits the store with $x = 1$ and
$y = 5$, so the check `x == y` cannot be proved. @sec:relational shows that the
framework does not require this form.

The set $sem(sigma)$ is empty exactly when one variable has an empty
concretization (#isathm("is_empty_state_iff_gamma_state_empty")): a store needs
a value for every variable. This test quantifies over all variable names;
@ch:solving supplies a finite equivalent.

== Unreachable program points <sec:lift>

A `DEAD` verdict is meant to certify that no execution reaches a check, so the
analyzer should recognize unreachability reliably. The pointwise form offers
two encodings of unreachability. The all-bottom state is too narrow: backward
filtering (@sec:branches) typically empties one variable, and
${x |-> signval(bot), y |-> signval(top)}$ is empty without being all-bottom. Any empty state
is too fragile: the assignment `x = 1` turns that state into
${x |-> signval("+"), y |-> signval(top)}$ and makes dead code live again, and a
pointwise join of two differently empty arms restores both variables
(@fig:domain-reachability). Both failures are sound but lose the reachability
fact.

#let _r = claim-row("dom-disjunct-sign", "13:5")
#let _disjunct-program = ```
fun main() {
  x = __voblint_nondet_int();
  y = __voblint_nondet_int();
  if ((x == 0 && x == 1) || (y == 0 && y == 1)) {
    __voblint_check(x == 5);
  }
}
```
#figure(
  {
    align(center, block(width: 72%, {
      show raw: set text(size: 6.5pt)
      listing(lang: "c", claim: "dom-disjunct-sign", _disjunct-program.text)
    }))
    v(0.4em)
    table(
      columns: (auto, 1fr, 1fr),
      align: (left, left, left),
      stroke: none,
      table.hline(),
      [*after*], [*pointwise states only*], [*lifted and normalized*],
      table.hline(stroke: 0.5pt),
      [`x == 0 && x == 1`], [${x |-> signval(bot), y |-> signval(top)}$], [#ctor("Bot")],
      [`y == 0 && y == 1`], [${x |-> signval(top), y |-> signval(bot)}$], [#ctor("Bot")],
      [join of both arms], [${x |-> signval(top), y |-> signval(top)}$], [#ctor("Bot")],
      [check in the branch], [`UNKNOWN`], [#raw(_r.verdict)],
      table.hline(),
    )
  },
  kind: table,
  placement: auto,
  caption: [Sign states in the branch of the program above, whose guard
    no execution satisfies. The check in the branch only probes reachability:
    its verdict shows whether the analyzer recognizes the branch as dead. The
    middle column is a hand calculation; the last verdict is the analyzer's
    output (claim `dom-disjunct-sign`).],
) <fig:domain-reachability>

The fix keeps reachability apart from the store description. The datatype
#isatype("lifted") adds an outer constructor #ctor("Bot"), meaning
"unreachable", below every #ctor("Lifted") payload, with
$conc(ctor("Bot")) = emptyset$. #ctor("Bot") is the identity of the lifted
join, and #isaconst("transfer_lift") passes it through without running the
payload transfer. On a #ctor("Lifted") payload it runs the transfer and then
#isaconst("normalize_lift"), which replaces a result the emptiness test
classifies as empty by #ctor("Bot") (@fig:lifted-hasse). #ctor("Bot") plays the role that Goblint's
`Deadcode` exception plays operationally: it stops an unreachable path from
contributing further states. Joins preserve normalization
(#isathm("normalized_lift_sup")), and for a normalized value the emptiness test
holds exactly when the value is #ctor("Bot")
(#isathm("normalized_state_lift_bot_iff")). With the exact test, denoting no
store is then the same as being #ctor("Bot"), so dead code stays dead.
Normalization is not required for soundness. Its role is to preserve explicit
reachability information. It never changes the denoted set
(#isathm("gamma_state_normalize_lift")), so soundness does not need every solved
value to be normalized, and the published result canonicalizes each value it
reads back (#isaconst("canonicalize_lift")).

#let _lnode(pos, name, body, empty: false) = node(
  pos,
  text(size: 7pt, body),
  name: name,
  stroke: if empty { (paint: vb.muted, dash: "dashed", thickness: 0.7pt) } else {
    0.7pt + vb.neutral
  },
  fill: if empty { vb.bg } else { white },
  corner-radius: 3pt,
  inset: 3.5pt,
)
#figure(
  diagram(
    spacing: (14mm, 7mm),
    _lnode((1, 0), <l-top>, [#ctor("Lifted") ${x |-> signval(top), y |-> signval(top)}$]),
    _lnode((0, 1), <l-xp>, [#ctor("Lifted") ${x |-> signval("+"), y |-> signval(top)}$]),
    _lnode((2, 1), <l-yp>, [#ctor("Lifted") ${x |-> signval(top), y |-> signval("+")}$]),
    _lnode(
      (0, 2),
      <l-xb>,
      [#ctor("Lifted") ${x |-> signval(bot), y |-> signval(top)}$],
      empty: true,
    ),
    _lnode(
      (2, 2),
      <l-yb>,
      [#ctor("Lifted") ${x |-> signval(top), y |-> signval(bot)}$],
      empty: true,
    ),
    _lnode(
      (1, 3),
      <l-bb>,
      [#ctor("Lifted") ${x |-> signval(bot), y |-> signval(bot)}$],
      empty: true,
    ),
    _lnode((1, 4.6), <l-bot>, [#ctor("Bot")]),
    edge(<l-top>, <l-xp>, "-", stroke: 0.8pt + vb.neutral),
    edge(<l-top>, <l-yp>, "-", stroke: 0.8pt + vb.neutral),
    edge(<l-xp>, <l-xb>, "-", stroke: 0.8pt + vb.neutral),
    edge(<l-yp>, <l-yb>, "-", stroke: 0.8pt + vb.neutral),
    edge(<l-xb>, <l-bb>, "-", stroke: 0.8pt + vb.neutral),
    edge(<l-yb>, <l-bb>, "-", stroke: 0.8pt + vb.neutral),
    edge(<l-bb>, <l-bot>, "-", stroke: 0.8pt + vb.neutral),
    edge(<l-xb>, <l-bot>, "..|>", stroke: 0.7pt + vb.accent, bend: -35deg),
    edge(<l-yb>, <l-bot>, "..|>", stroke: 0.7pt + vb.accent, bend: 35deg),
    edge(<l-bb>, <l-bot>, "..|>", stroke: 0.7pt + vb.accent, bend: 70deg),
  ),
  kind: image,
  placement: none,
  caption: [Part of the lifted Sign states over two variables $x$ and $y$,
    ordered bottom to top. #ctor("Bot") lies below every #ctor("Lifted")
    payload, including the all-bottom one. The dashed payloads describe no
    store; #isaconst("normalize_lift") maps them to #ctor("Bot") (blue
    arrows). Illustrative.],
) <fig:lifted-hasse>

== Learning from a guard <sec:branches>

A guard changes no variable, yet the stores that pass it satisfy it. In

#align(center, block(width: 80%, listing(
  "x = __voblint_nondet_int();\nif (0 < x) { y = x; } else { y = 0 - x; }\n__voblint_check(y >= 0);",
  lang: "c",
  claim: "dom-guard-sign",
)))

$y$ is always $|x|$. A branch transfer that only evaluates the guard keeps
$x = signval(top)$ in both arms, and the check is `UNKNOWN`. The inverse
operators of #isalocale("backward_domain") (@fig:backward-contract) use the
guard instead: given abstract operands and the required result, they return
refined operands. Sign refines $x$ to
#signval("+") on the true arm and #signval("≤0") on the false arm, $y$ joins to
#signval("≥0"),
#let _g = claim-row("dom-guard-sign", "18:3")
and the analyzer reports #raw(_g.verdict) with #raw(_g.state).

The intersection only has to keep every value both operands share, so it need
not be the lattice meet, and the carrier need not have a meet at all. For
intervals, #isaconst("intersect_ivl") maps $[1, 2]$ and $[5, 6]$ to the
canonical bottom (#isathm("interval_intersect_of_witness_bot")), while the
greatest lower bound in the raw bound order is the inverted pair $[5, 2]$.

The generic filters #isaconst("afilter") and #isaconst("bfilter") push these
requirements through an expression once for every domain. A filter may keep
stores that fail the guard, but it drops none that pass it.

#block(breakable: false)[
  #theorem(name: [Sound guard filter], isa: "bfilter_sound")[
    If a store $s$ lies in $sem(sigma)$ and the guard $e$ has truth value
    #isai("res") at $s$, then $s$ lies in the meaning of the filtered state.
  ]

  #proved("bfilter_sound")
]

For a true disjunction, #isaconst("bfilter") filters each alternative
separately, drops one that the forward test #isaconst("feasible") rejects, and
joins the rest. An arm can still become empty by backward refinement, so
#isaconst("bfilter_lifted") normalizes each arm to #ctor("Bot") before the join
and avoids the leak of @fig:domain-reachability. In the example of
@sec:constraints, the guard refinement of $h$ by $[-infinity, 4]$, written
there with the interval meet, stands for this filter.

== Asking instead of assuming <sec:queries>

A branch assumes its condition. A check must decide whether the current
description already implies it. The backward domain alone cannot decide
this: a sound filter may keep stores that fail the condition, so filtering does
not show that the original state implied it. A domain therefore also answers
comparison queries with definitely true, definitely false or unknown
(@fig:numeric-queries). The unknown answer #isai("None") carries no
obligation, so a domain may give it whenever it cannot decide, and queries may
be incomplete. Congruence
#let _c = claim-row("dom-even-odd-congruence", "20:3")
stores the disjoint classes #raw(_c.state) for `x = 2 * n; y = 2 * n + 1`, yet
its equality query decides only between single integers, so #box[`x != y`]
stays #raw(_c.verdict).

#block(breakable: false)[
  #definition(name: [Numeric queries], isa: "abstract_numeric_queries", cmd: "locale")[
    A definite answer must hold for every pair of integers the operands denote.
  ]

  #figure(
    {
      show raw.where(block: true): set text(size: 6.2pt)
      thy("abstract_numeric_queries")
    },
    kind: image,
    placement: none,
    caption: [The declaration of #isalocale("abstract_numeric_queries"), lifted
      from the theory.],
  ) <fig:numeric-queries>
]

#figure(
  table(
    columns: (auto, auto),
    align: (left, center),
    stroke: none,
    inset: (x: 4pt, y: 3pt),
    table.hline(),
    [*requirement*], [*what the proofs use it for*],
    table.hline(stroke: 0.5pt),
    [#isaconst("is_empty") $a ==> conc(a) = emptyset$], [discarding an empty state (@sec:lift)],
    [$conc(a) = emptyset ==>$ #isaconst("is_empty") $a$], [normalization, readback (@sec:readback)],
    [least upper bounds], [the solver's order class],
    [#isalocale("warrowing")], [the solver's update rule],
    [sound inverse operators, if any], [#isathm("bfilter_sound") (@sec:branches)],
    [sound comparison queries], [check verdicts (@sec:verdicts)],
    table.hline(stroke: 0.5pt),
    [_not required:_ abstraction function], [no optimality claim],
    [_not required:_ lattice meet], [#isalocale("semantic_intersection") suffices],
    [_not required by core soundness:_ monotone transfers], [some instance interfaces impose it],
    [_not required:_ stabilizing widening], [termination is a premise],
    table.hline(),
  ),
  placement: auto,
  caption: [The requirements this chapter adds to the laws of $conc$ from
    @sec:abs-int, each with the proof step that uses it. The last rows name
    what a domain does not need to provide.],
) <tab:domain-contract>

A domain contributes to the composition by proving the laws of
#isalocale("numeric_domain") and the requirements of @tab:domain-contract. None
of them mentions a context, an equation or a solver, so a domain proves them
once per domain instance (and, where applicable, refinement mode) and reuses them across context policies
and solver configurations. @ch:analysis-interface turns these per-value laws
into the per-edge form of #oblig("INTRA") and asks what else an analysis must
supply at calls.
