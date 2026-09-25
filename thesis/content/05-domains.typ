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
that connect them to $conc$. @fig:domain-carrier draws them as one inheritance
tree with three parts.

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
          size: 5.8pt,
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
        set text(size: 5pt)
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
      y += h + 6pt
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
  placement: top,
  caption: [What a domain supplies over its carrier type #raw("'a"). Each
    class (solid) or locale (dashed) lists the operations and laws it declares.
    Solid arrows point to what a declaration extends, dashed ones to the class
    its type variable is constrained to. Colour gives where a node is declared:
    #swatch(vb.hol) HOL, #swatch(vb.solver) the vendored solver,
    #swatch(vb.voblint) Voblint. Read from the declarations.],
) <fig:domain-carrier>

- *Carrier classes.* The solver compares, joins, widens and narrows abstract
  values, and the proof must read each solved value as a set of integers. Isabelle's HOL library supplies the order in
  which the solver's inequalities are stated, the join that merges control
  flow, and the bounds $lbot$ and $ltop$. The solver's own classes supply the
  widening $widen$ and the narrowing $narrow$ it applies at loop heads.
  #isalocale("executable_domain") adds an emptiness test, so that the analysis
  can discard a state no store reaches, and a printer for reporting results.
  #isalocale("numeric_domain") adds $conc$ with the laws that turn the solver's
  inequalities into inclusions. A _numeric domain_ is a type of this class.
- *Forward interface.* Assignments, branches and checks evaluate expressions
  over abstract states, as in the generic abstract interpreter of Nipkow and
  Klein @nipkow14[Sect. 13.5.2]. Their soundness reduces to one statement per
  expression: the abstract result contains every concrete result, which
  #isalocale("sound_evaluator") requires. #isalocale("sound_truth_test") rules out a branch whose condition is certainly zero or certainly non-zero.
- *Backward domain.* A guard such as $x < 10$ tells the analysis more about $x$
  on each branch, but forward evaluation only yields the guard's truth value.
  Inverse operators @nipkow14[Sect. 13.7.1] run the other way: they refine the operands of a
  comparison or an arithmetic operation to values that still contain every
  concrete pair producing the required result.
  #isalocale("semantic_intersection") combines the result with what was known,
  and #isalocale("backward_domain") adds both to the forward interface.

The interface asks for less than Nipkow and Klein's backward analysis, whose
carrier must be a lattice with a precise meet,
$conc(a_1 lmeet a_2) = conc(a_1) inter conc(a_2)$ @nipkow14[Sect. 13.7].
#isalocale("semantic_intersection") asks only for the inclusion
$conc(a_1) inter conc(a_2) subset.eq conc("intersect"(a_1, a_2))$ that the
analysis uses, so the carrier need not have a meet at all. The interface also
has no abstraction function, since Voblint claims no optimal precision.
Monotonicity is a separate layer, #isalocale("mono_evaluator") and its
siblings, which soundness does not need.

=== A carrier the interface excludes <sec:no-defexc>

The domain laws use the join only through the fact that it lies above both
operands. The carrier classes demand more: #isalocale("semilattice_sup")
requires the join to be the _least_ upper bound, and the solver and the
generic framework are stated over this class. Leastness rules out a domain
that Goblint uses. Its exclusion-set domain
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/cdomain/value/cdomains/int/defExcDomain.ml")[`DefExc`] describes an integer
either by its exact value, a singleton ${n}$, or by a finite set $F$ of values
it cannot have, the cofinite set $ZZ without F$.

#figure(
  diagram(
    spacing: (9mm, 8mm),
    _snode((1.5, 0), <x-top>, $ZZ$),
    _snode((0.8, 1), <x-3>, $ZZ without {3}$),
    _snode((2.2, 1), <x-4>, $ZZ without {4}$),
    _snode((3.1, 1), <x-more>, $dots.c$),
    _snode((1.5, 2), <x-34>, $ZZ without {3, 4}$),
    _snode((1.5, 3), <x-345>, $ZZ without {3, 4, 5}$),
    _snode((1.5, 3.9), <x-down>, $dots.v$),
    node(
      (1.5, 4.9),
      text(size: 8pt, fill: vb.muted, ${1, 2}$),
      name: <x-12>,
      inset: 3pt,
      stroke: stroke(paint: vb.muted, thickness: 0.6pt, dash: "dashed"),
      shape: rect,
      corner-radius: 2pt,
    ),
    _snode((-0.7, 5.8), <x-s0>, ${0}$),
    _snode((0.3, 5.8), <x-s1>, ${1}$),
    _snode((2.7, 5.8), <x-s2>, ${2}$),
    _snode((3.7, 5.8), <x-s3>, ${3}$),
    _snode((4.4, 5.8), <x-smore>, $dots.c$),
    _snode((1.5, 6.9), <x-bot>, $emptyset$),
    edge(<x-top>, <x-3>, "-", stroke: _order),
    edge(<x-top>, <x-4>, "-", stroke: _order),
    edge(<x-3>, <x-34>, "-", stroke: _hit),
    edge(<x-4>, <x-34>, "-", stroke: _hit),
    edge(<x-34>, <x-345>, "-", stroke: _hit),
    edge(<x-345>, <x-down>, "-", stroke: _hit),
    edge(<x-345>, <x-s1>, "-", stroke: (paint: vb.neutral, thickness: 0.7pt, dash: "dotted")),
    edge(<x-345>, <x-s2>, "-", stroke: (paint: vb.neutral, thickness: 0.7pt, dash: "dotted")),
    edge(<x-12>, <x-s1>, "-", stroke: (paint: vb.muted, thickness: 0.6pt, dash: "dashed")),
    edge(<x-12>, <x-s2>, "-", stroke: (paint: vb.muted, thickness: 0.6pt, dash: "dashed")),
    ..("s0", "s1", "s2", "s3").map(n => edge(label("x-" + n), <x-bot>, "-", stroke: _order)),
  ),
  kind: image,
  placement: auto,
  caption: [A sketch of the simplified exclusion-set carrier, each value drawn as
    the set of integers it denotes and ordered bottom to top. Every
    $ZZ without F$ with $1, 2 in.not F$ lies above ${1}$ and ${2}$. The blue
    chain of such upper bounds descends forever, and every element of it lies
    above both singletons (dotted). A least upper bound would denote ${1, 2}$ (dashed),
    which the carrier does not contain. Illustrative, not machine-checked.],
) <fig:defexc>

Over unbounded integers (@fig:defexc), the singletons ${1}$ and ${2}$ have no least upper
bound in this carrier. Every $ZZ without {p}$ with $p in.not {1, 2}$ is an
upper bound, and no two of them are comparable, so no single value lies below
all of them. A least upper bound would have to denote exactly ${1, 2}$, which
is neither a singleton nor cofinite. Goblint avoids the problem in two ways. Its exclusion sets carry the bit
range of the integer kind, so the upper bounds of ${1}$ and ${2}$ are
finitely many. Its join is also not least: joining two different values
excludes only $0$. Voblint could keep this carrier only by bounding its
integers, or by weakening #isalocale("semilattice_sup") to an upper-bound
law, which the vendored solver's own definitions rule out. A carrier that also
holds finite sets has no such problem. Finite and cofinite sets are closed
under union, so the join of ${1}$ and ${2}$ is ${1, 2}$. Goblint's enumeration
domain #link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/cdomain/value/cdomains/int/enumsDomain.ml")[`Enums`] has this shape, and Voblint
has no such component. This argument is not machine-checked.

== From values to stores <sec:domain-states>

The simplest description of a set of stores assigns one abstract value to each
variable. A store, of type #isatype("store") $=$ #isatype("vname") $=>$
`int`, maps every variable name to an integer. An abstract state replaces the
integer by an abstract value: #isatype("abs_state") $=$ #isatype("vname")
$=>$ `'a`, so a state $sigma$ maps every variable name $x$ to $sigma(x)$. The
function #isaconst("gamma_state") gives it a meaning, the set of stores whose
every variable lies in the concretization of its abstract value:
$ sem(sigma) = setcomp(s, forall x. s(x) in conc(sigma(x))). $
Order and join work variable by variable (@fig:pointwise), so the
construction forgets every relation between variables.

#let _pw-vals = ($bot$, "0", $top$)
#figure(
  diagram(
    spacing: (10mm, 7mm),
    ..for i in range(3) {
      for j in range(3) {
        let empty = i == 0 or j == 0
        let body = $(signval(#_pw-vals.at(i)), signval(#_pw-vals.at(j)))$
        (
          node(
            (j - i, 4 - i - j),
            text(size: 8pt, fill: if empty { vb.muted } else { vb.plain }, body),
            name: label("pw-" + str(i) + str(j)),
            inset: 3pt,
            stroke: if empty { stroke(paint: vb.muted, thickness: 0.5pt, dash: "dashed") } else {
              none
            },
            shape: rect,
            corner-radius: 2pt,
          ),
        )
      }
    },
    ..for i in range(3) {
      for j in range(3) {
        let here = label("pw-" + str(i) + str(j))
        if i < 2 { (edge(here, label("pw-" + str(i + 1) + str(j)), "-", stroke: _order),) }
        if j < 2 { (edge(here, label("pw-" + str(i) + str(j + 1)), "-", stroke: _order),) }
      }
    },
  ),
  kind: image,
  placement: none,
  caption: [Pointwise states over two variables, each pair giving
    $(sigma(x), sigma(y))$ with values from the fragment
    $signval(bot) lle signval("0") lle signval(top)$ of Sign, ordered
    variable by variable. The dashed states have a #signval($bot$) component and
    denote no store, although only the lowest one is the bottom state.],
) <fig:pointwise>

== Unreachable program points <sec:lift>

A `DEAD` verdict is meant to certify that no execution reaches a check, so the
analyzer should recognize unreachability reliably. The pointwise form offers
two encodings of unreachability. The all-bottom state is too narrow: backward
filtering (@sec:branches) typically empties one variable, and
${x |-> signval(bot), y |-> signval(top)}$ is empty without being all-bottom
(@fig:pointwise). Any empty state
is too fragile: the assignment `x = 1` turns that state into
${x |-> signval("+"), y |-> signval(top)}$ and makes dead code live again, and a
pointwise join of two differently empty arms restores both variables
(@fig:domain-reachability). Both failures are sound but lose the reachability
fact.

#let _r = claim-row("dom-disjunct-sign", "13:5")
#figure(
  align(center, block(width: 72%, {
    show raw: set text(size: 6.5pt)
    listing(
      lang: "c",
      claim: "dom-disjunct-sign",
      ```
      fun main() {
        x = __voblint_nondet_int();
        y = __voblint_nondet_int();
        if ((x == 0 && x == 1) || (y == 0 && y == 1)) {
          __voblint_check(x == 5);
        }
      }
      ```.text,
    )
  })),
  kind: image,
  placement: auto,
  caption: [A guard no execution satisfies. Its two disjuncts empty different
    variables, so a pointwise join of the arms restores both. With the lifted
    states of this section, the analyzer reports the check in the branch as
    #raw(_r.verdict) (claim `dom-disjunct-sign`).],
) <fig:domain-reachability>

Goblint tracks reachability separately from the store description: a transfer
function that finds its path unreachable raises the `Deadcode` exception, and
the path contributes no further states. Voblint keeps the same separation, but
inside the lattice. The datatype
#isatype("lifted") adds an outer constructor #ctor("Bot"), meaning
"unreachable", below every #ctor("Lifted") payload, with
$conc(ctor("Bot")) = emptyset$. #ctor("Bot") is the identity of the lifted
join, and #isaconst("transfer_lift") passes it through without running the
payload transfer. On a #ctor("Lifted") payload it runs the transfer and then
#isaconst("normalize_lift"), which replaces a result the emptiness test
classifies as empty by #ctor("Bot") (@fig:lifted-hasse). Joins preserve normalization
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
operators of #isalocale("backward_domain") (@fig:domain-carrier) use the
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
