#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "../lib/math.typ": *
#import "../lib/code.typ": (
  decode-isabelle, isabelle-scripts, isaconst, isai, isalocale, isathm, isatype, listing, oblig,
  thy-badge,
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
assignment or join the information that the point is dead is gone (@sec:nonrel-state).
This chapter separates the semantic laws that connect abstract operations to
their concrete meaning from the additional algebraic structure the solver
requires. It also names the laws it omits on purpose.

#let _snode(pos, name, body) = node(pos, text(size: 8pt, body), name: name, inset: 3pt)
#let _order = 0.7pt + vb.neutral
#let _hit = 1.1pt + vb.accent
#figure(
  diagram(
    spacing: (0mm, 9mm),
    cell-size: (22mm, 5mm),
    _snode((1, 0), <s-top>, signval($top$)),
    _snode((0.5, 1), <s-le>, signval("≤0")),
    _snode((1.5, 1), <s-ge>, signval("≥0")),
    _snode((0, 2), <s-neg>, signval("−")),
    _snode((1, 2), <s-zero>, signval("0")),
    _snode((2, 2), <s-pos>, signval("+")),
    _snode((1, 3), <s-bot>, signval($bot$)),
    _snode((4.5, 0), <c-top>, $ZZ$),
    _snode((5, 1), <c-le>, $setcomp(n, n <= 0)$),
    _snode((4, 1), <c-ge>, $setcomp(n, n >= 0)$),
    _snode((5.5, 2), <c-neg>, $setcomp(n, n < 0)$),
    _snode((4.5, 2), <c-zero>, ${0}$),
    _snode((3.5, 2), <c-pos>, $setcomp(n, n > 0)$),
    _snode((4.5, 3), <c-bot>, $emptyset$),
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
    edge(<s-top>, <c-top>, "|-->", stroke: 0.7pt + vb.muted, label: $conc$, bend: 12deg),
    edge(<s-ge>, <c-ge>, "|-->", stroke: 0.7pt + vb.accent, bend: 12deg),
    edge(<s-pos>, <c-pos>, "|-->", stroke: 0.7pt + vb.accent, bend: -12deg),
    edge(<s-bot>, <c-bot>, "|-->", stroke: 0.7pt + vb.muted, bend: -12deg),
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

A domain is a type $A$ of abstract values, operations on $A$, and laws that
relate these operations to $conc$. @fig:domain-carrier shows all of them, read
from the declarations. They fall into three groups: what the solver needs,
forward evaluation, and backward refinement.

// What a domain supplies, as UML inheritance trees. Each node is a class or
// locale read from its lifted declaration and lists only the members it
// declares; the edges are its declared parents, followed from the declarations
// a domain instantiates, so a figure cannot drift from the sources. Only the
// roots, the nodes another figure introduces and the node positions are
// chosen, in shared/domain-tree.toml.
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
// A node another figure introduces keeps its name and constraining class but
// neither its members nor its parents.
#let _visit(d, acc, refs) = {
  if acc.any(e => e.name == d.name) { return acc }
  if d.name in refs { return acc + ((..d, parents: (), fixes: (), laws: (), ref: true),) }
  for q in d.parents { acc = _visit(_decl(_snip(q)), acc, refs) }
  acc + ((..d, ref: false),)
}
#let _trees = toml("/shared/domain-tree.toml")
#let _tree(key) = {
  let cfg = _trees.at(key)
  let hierarchy = cfg.roots.fold((), (acc, n) => _visit(_decl(_snip(n)), acc, cfg.refs))
  let names = hierarchy.map(d => d.name)
  let placed = cfg.rows.map(r => r.keys()).flatten()
  let unplaced = names.filter(n => n not in placed)
  let stale = placed.filter(n => n not in names)
  assert(
    unplaced == () and stale == (),
    message: "domain tree "
      + key
      + " positions: unplaced "
      + repr(unplaced)
      + ", stale "
      + repr(stale),
  )
  // Each instance is listed at the most derived node it reaches: a type at the
  // class it instantiates, a lemma proving a final locale, one nothing else
  // extends. The lemma may prove a strengthening the figure leaves out
  // (`backward_domain_mono`).
  let interpreted = (:)
  for (n, instances) in cfg.at("interpreted", default: (:)) {
    assert(n in names, message: "domain tree " + key + ": interpreted " + n + " is not drawn")
    interpreted.insert(n, instances.map(i => {
      let src = _snip(i)
      let inst = src.match(
        regex("(?m)^instantiation\\s+(\\S+)\\s*::\\s*(?:\\([^)]*\\)\\s*)?(\\S+)"),
      )
      if inst != none {
        assert(
          inst.captures.at(1) == n,
          message: i + " instantiates " + inst.captures.at(1) + ", not " + n,
        )
        return (name: inst.captures.at(0), locale: n, kind: "class")
      }
      let m = src.match(regex("(?m)^lemma\\s+(\\S+):\\s+\"(\\S+)"))
      assert(m != none and m.captures.at(0) == i, message: "no lemma " + i)
      assert(
        not hierarchy.any(d => n in d.parents),
        message: "domain tree " + key + ": " + n + " is extended, so it is not final",
      )
      let locale = m.captures.at(1)
      assert(
        locale == n or locale.starts-with(n + "_"),
        message: i + " proves " + locale + ", not " + n,
      )
      (name: i, locale: locale, kind: "locale")
    }))
  }
  (
    hierarchy: hierarchy,
    rows: cfg.rows,
    bends: cfg.bends,
    parent-bends: cfg.parent-bends,
    widths: cfg.at("widths", default: (:)),
    row-gap: cfg.at("row-gap", default: 6.0) * 1pt,
    interpreted: interpreted,
  )
}
#let _ancestors(hierarchy, n) = {
  let d = hierarchy.find(e => e.name == n)
  if d == none { () } else { d.parents + d.parents.map(p => _ancestors(hierarchy, p)).flatten() }
}

#let swatch(c) = box(
  width: 0.8em,
  height: 0.8em,
  baseline: 0.1em,
  radius: 1pt,
  fill: c.lighten(82%),
  stroke: 0.7pt + c,
)

#let domain-tree(key) = {
  let tree = _tree(key)
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
      // A pure combination such as `backward_domain` or `warrowing` declares
      // nothing itself; an empty box would read as a rendering fault.
      let instances = tree.interpreted.at(d.name, default: ())
      if d.fixes == () and d.laws == () and not d.ref and instances == () {
        rows.push(table.hline(stroke: 0.4pt + vb.at(d.origin)))
        rows.push(table.cell(colspan: 2, align: center, text(
          fill: vb.muted,
          style: "italic",
        )[combines its parents]))
      }
      if instances != () {
        rows.push(table.hline(stroke: 0.4pt + vb.at(d.origin)))
        rows.push(table.cell(colspan: 2, align: center, text(
          fill: vb.muted,
          style: "italic",
        )[#if instances.all(it => it.kind == "class") [instantiated by] else [proved by]]))
        // Types need no second column, so they share one wrapped line.
        let types = instances.filter(it => it.kind == "class")
        if types != () {
          rows.push(table.cell(colspan: 2, types.map(it => code(it.name)).join[, ]))
        }
        // The strengthening a lemma proves is named in the caption, not per row.
        for it in instances.filter(it => it.kind == "locale") {
          rows.push(table.cell(colspan: 2, code(it.name)))
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
      let alone = tree.rows.any(r => r.len() == 1 and d.name in r)
      let cap = if alone { size.width } else {
        tree.widths.at(d.name, default: 0.3) * size.width
      }
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
    for d in tree.hierarchy { boxes.insert(d.name, box-of(d)) }
    let (at, y) = ((:), 0pt)
    for row in tree.rows {
      let h = calc.max(..row.keys().map(n => measure(boxes.at(n)).height))
      // Physical coordinates grow upwards.
      for (n, x) in row { at.insert(n, (x * size.width, -(y + h / 2))) }
      y += h + tree.row-gap
    }
    let hollow = (inherit: "stealth", stealth: 0, fill: white, size: 7)
    diagram(
      node-inset: 0pt,
      ..for d in tree.hierarchy {
        // Fletcher draws near-square nodes as circles unless told otherwise.
        (node(at.at(d.name), boxes.at(d.name), name: label(d.name), shape: fletcher.shapes.rect),)
      },
      ..for d in tree.hierarchy {
        // An arrow implied by a longer path is left out.
        for p in d.parents.filter(p => {
          not d.parents.any(q => q != p and p in _ancestors(tree.hierarchy, q))
        }) {
          (
            edge(
              label(d.name),
              label(p),
              marks: (none, hollow),
              stroke: 0.5pt + vb.neutral,
              bend: tree.parent-bends.at(d.name, default: (:)).at(p, default: 0) * 1deg,
            ),
          )
        }
        for b in d.bounds.filter(b => b in at) {
          (
            edge(
              label(d.name),
              label(b),
              "-straight",
              stroke: (paint: vb.muted, thickness: 0.5pt, dash: "dashed"),
              bend: tree.bends.at(d.name, default: 0) * 1deg,
            ),
          )
        }
      },
    )
  })
}

#figure(
  domain-tree("carrier"),
  kind: image,
  placement: top,
  caption: [What a domain supplies over its carrier type #raw("'a") for
    sound evaluation, refinement and checks; the reductive and monotone strengthenings
    are not drawn. Each
    class (solid) or locale (dashed) lists the operations and laws it declares.
    Solid arrows point to what a declaration extends, dashed ones to the class
    its type variable is constrained to. An interface an analysis implements
    lists the instances or lemmas establishing it. The backward lemmas prove the monotone strengthening
    #isalocale("backward_domain_mono"), except Int's, which proves the
    reductive one. Colour gives where a node is
    declared:
    #swatch(vb.hol) HOL, #swatch(vb.solver) the vendored solver,
    #swatch(vb.voblint) Voblint. Read from the declarations.],
) <fig:domain-carrier>

The solver compares abstract values, joins them where control flow merges, and
uses a least value $lbot$ and a greatest value $ltop$. It also applies a
widening $widen$ and a narrowing $narrow$, whose laws only bound their results:
$
  a lle a widen b, quad b lle a widen b, quad
  b lle a ==> b lle a narrow b lle a.
$
The laws do not force an iteration with these operators to stop. A domain
further supplies an emptiness test, a printer, and the concretization
$conc : A -> cal(P)(ZZ)$ with four laws:
$
  conc(lbot) = emptyset, quad conc(ltop) = ZZ, quad
  a lle b ==> conc(a) subset.eq conc(b), quad
  #isaconst("is_empty") (a) <==> conc(a) = emptyset.
$
The third law turns the solver's inequalities into inclusions; the fourth
decides emptiness for every value, not only for $lbot$. Such a type is a
_numeric domain_ (#isalocale("numeric_domain")).

Forward evaluation computes an abstract value for an expression $e$ from an
abstract description $d$ of a set of stores $sem(d)$, as in the generic
abstract interpreter of Nipkow and Klein @nipkow14[Sect. 13.5.2]. The abstract
result must contain every concrete result:
$ s in sem(d) ==> sem(e)_e thin s in conc(sh("eval")(e, d)). $
A domain may also decide the truth of a value. Its truth test
$"tobool"(a)$ returns $"Some"(b)$ if it can decide that every integer in
$conc(a)$ has truth value $b$, where non-zero counts as true, and
$"None"$ otherwise:
$ "tobool"(a) = "Some"(b) and i in conc(a) ==> (i != 0) = b. $

To answer the checks of @sec:queries, a domain also supplies two queries on
abstract values, $"less"(a, b)$ for $a < b$ and $"eq"(a, b)$ for $a = b$
(#isalocale("sound_numeric_queries")). A definite answer must hold for every
pair of integers the two values denote, and $"None"$ is always allowed:
$ "less"(a, b) = "Some"(r) and i in conc(a) and j in conc(b) ==> (i < j) = r, $
and likewise for $"eq"$. #isalocale("abstract_check_domain") combines the
queries with forward evaluation.

Backward refinement runs evaluation in reverse @nipkow14[Sect. 13.7.1]. Given
abstract operands $a_1, a_2$ and the result an operation must produce, an
inverse operator returns refined operands $a'_1, a'_2$ that keep every
concrete pair producing that result. For a comparison that must yield $r$:
$
  n_1 in conc(a_1) and n_2 in conc(a_2) and (n_1 < n_2) = r
  ==> n_1 in conc(a'_1) and n_2 in conc(a'_2),
$
and likewise for equality, addition, subtraction and multiplication. An
intersection combines a refined value with the value known before. Nipkow and
Klein use a lattice meet and require $conc(a_1 lmeet a_2) = conc(a_1) inter
conc(a_2)$; one inclusion holds in every lattice, and the other is all that
soundness needs @nipkow14[Sect. 13.7]. The interface keeps that inclusion and
drops the lattice. The intersection is any operation with
$ conc(a_1) inter conc(a_2) subset.eq conc("intersect"(a_1, a_2)), $
not necessarily a meet of the order, and the carrier classes require a join
but no meet.

The interface also asks for no monotone operations. Nipkow and Klein need them
because their narrowing keeps a post-fixpoint only for a monotone step function
@nipkow14[Lemma 13.39]. Voblint's solver stops only when every unknown it reached
is stable, so a terminated solve satisfies each inequality whatever the
operations are (#isathm("partial_post_solution")). Monotonicity would help precision and termination, which
Voblint does not prove: precision is not a theorem, termination a premise.

== Intervals as a numeric domain #thy-badge("Voblint_Domain", "Interval_Lattice") <sec:interval-domain>

The interval domain of @sec:abs-int shows how a concrete type meets these laws.
@sec:abs-int described it on non-empty intervals. The formal type must also
represent unbounded ends and empty intervals, and most design decisions
concern the latter. The paragraphs below follow @fig:domain-carrier from top
to bottom.

*Carrier.* Bounds are extended integers #isatype("eint"): $-infinity$, an
integer, or $+infinity$, linearly ordered. Addition and subtraction extend the
integer operations. HOL functions are total, so the mixed cases such as
$+infinity + (-infinity)$ return a fixed bound instead of being undefined. An
interval is a raw pair of bounds, #isatype("ivl"), with
$ conc(ivl(l, u)) = setcomp(n in ZZ, l <= n and n <= u). $
The empty set has many representations. Any pair with $l > u$ is empty, and
so are $ivl(+infinity, +infinity)$ and $ivl(-infinity, -infinity)$, since no
integer equals an infinite bound.

*Order, bottom and top* (#isalocale("order"), #isalocale("order_bot"),
#isalocale("order_top")). The order compares bounds:
$ivl(l_1, u_1) lle ivl(l_2, u_2)$ if $l_2 <= l_1$ and $u_1 <= u_2$. The bottom
value is one of the empty pairs, $lbot = ivl(+infinity, -infinity)$, and the
top value is $ltop = ivl(-infinity, +infinity)$, the only pair denoting $ZZ$.
An empty pair such as $ivl(5, 3)$ denotes the same set as $lbot$, yet it is
neither $lbot$ nor below it.

*Join* (#isalocale("semilattice_sup")). The join takes the outer bounds,
$ivl(l_1, u_1) ljoin ivl(l_2, u_2) = ivl(min(l_1, l_2), max(u_1, u_2))$, which
is the least upper bound in the bound order. Joined with an empty pair it can
add integers: $ivl(1, 0) ljoin ivl(5, 5) = ivl(1, 5)$, although only $5$ is
denoted by either operand. The result is sound but imprecise.
#isaconst("normalize_ivl") replaces every empty pair by $lbot$ and leaves
non-empty pairs unchanged. The arithmetic operations normalize their operands
and results, so they never produce a second empty pair. One representative
per value also keeps the solver's stability test meaningful, since two
different empty pairs compare as different values.

*Widening and narrowing* (#isalocale("widening"), #isalocale("narrowing")).
The widening #isaconst("widen_ivl_core") keeps a bound that did not move
outward and sends one that did to infinity,
$ivl(0, 1) widen ivl(0, 2) = ivl(0, +infinity)$. Because
$lbot = ivl(+infinity, -infinity)$, this rule would send
$lbot widen ivl(0, 0)$ to $ltop$, so widening from $lbot$ returns the other
operand. The narrowing #isaconst("narrow_ivl_td") fills only infinite bounds,
$ivl(0, +infinity) narrow ivl(0, 10) = ivl(0, 10)$. Each law of the two
classes follows by comparing bounds.

*Emptiness test and printer* (#isalocale("executable_domain")). Since an
empty pair need not be $lbot$, the emptiness test inspects the bounds instead
of comparing with $lbot$ (#isaconst("is_bottom_ivl")). The
printer shows $ivl(l, u)$ with $plus.minus infinity$ for infinite ends, every
empty pair as $lbot$, and a standalone $ltop$ as $ltop$. No law constrains it.
Isabelle checks it only on a few fixed values
(#isathm("string_of_ivl_regression")). A printer that swapped the bounds
would leave every theorem intact and still mislead every reader of the output. It lies outside the verified boundary.

*Concretization laws* (#isalocale("numeric_domain")). $conc(lbot) = emptyset$
and $conc(ltop) = ZZ$ hold by definition. Monotonicity follows from
transitivity of $<=$ on bounds. The emptiness law is the bound test above
(#isathm("is_bottom_ivl_correct")). Intervals are the case this law exists
for.

*Forward evaluation* (#isalocale("sound_evaluator"),
#isalocale("sound_truth_test")). Expressions evaluate by interval arithmetic
on the bounds (#isaconst("aval_ivl")). If $x = ivl(0, 9)$, then $x + 1$
evaluates to $ivl(1, 10)$. The truth test #isaconst("interval_tobool") returns $"Some"("true")$ for
$ivl(l, u)$ if the interval excludes $0$, that is $u < 0$ or $l > 0$, and
$"Some"("false")$ if $l = u = 0$. Otherwise it returns $"None"$. So $ivl(1, 5)$
is true, $ivl(0, 0)$ is false, and $ivl(0, 5)$ is undecided. An empty pair also
counts as true. The law holds for it vacuously, since it denotes no integer.

*Intersection and inverse operators* (#isalocale("sound_intersection"),
#isalocale("backward_ops")). The meet intersects the bounds and is exact on
the denoted sets, $conc(a lmeet b) = conc(a) inter conc(b)$. It cannot
normalize its result: $ivl(5, 3)$ lies below both $ivl(0, 3)$ and
$ivl(5, 9)$, but not below the normalized meet $lbot$, so a normalizing meet
would not be a greatest lower bound
(#isathm("meet_ivl_normalized_breaks_greatest")). The intersection of the
interface is therefore a separate operation, the normalized meet
#isaconst("intersect_ivl"). It preserves the denoted set exactly, and it is
reductive and monotone. The inverse of $<$ refines $x = ivl(0, +infinity)$
against $ivl(10, 10)$, with $x < 10$ required true, to $x = ivl(0, 9)$
(#isaconst("inv_less_ivl")). Only comparisons refine. The inverses of
addition, subtraction and multiplication return their operands unchanged,
which the law allows.

Every operation above is proved to satisfy its law, so the interval domain is
sound. It is however not as precise as it could be. The inverse of addition, for
example, could refine $x_1$ in $x_1 + x_2 = r$ to $x_1 lmeet (r - x_2)$, as
the interval analysis of Nipkow and Klein does @nipkow14[Sect. 13.8.3]. Such
refinements would only add precision, which this thesis does not pursue.

=== A carrier without least upper bounds <sec:no-defexc>

Soundness uses the join only as an upper bound of its operands. The carrier
classes demand more: #isalocale("semilattice_sup") requires the _least_ upper
bound, because the solver and the generic framework are stated over this
class. This excludes every carrier in which two values have upper bounds but
no least one.

Goblint's exclusion-set domain
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/cdomain/value/cdomains/int/defExcDomain.ml",
)[`DefExc`]
is such a carrier once its bit range is removed. A value is `Definite n`,
denoting ${n}$, or `Excluded (S, r)`, denoting the integers in the bit range
$r$ outside the finite set $S$. Mathematical integers have no bit range, so
`Excluded S` denotes $ZZ without S$ (@fig:defexc). Then `Definite 1` and
`Definite 2` have no least upper bound. Every `Excluded {p}` with
$p in.not {1, 2}$ lies above both. A least upper bound $u$ would lie below
each of them, so by monotonicity of $conc$
$ {1, 2} subset.eq conc(u) subset.eq inter.big_(p in.not {1, 2}) (ZZ without {p}) = {1, 2}, $
but no value denotes exactly ${1, 2}$: `Definite n` denotes a single
integer, and `Excluded S` all but finitely many.

#let _gnode(pos, name, body) = node(pos, text(size: 7pt, raw(body)), name: name, inset: 3pt)
#figure(
  diagram(
    spacing: (4.5mm, 6mm),
    _gnode((1.5, 0), <x-top>, "Excluded {}"),
    _gnode((0.6, 1), <x-3>, "Excluded {3}"),
    _gnode((2.4, 1), <x-4>, "Excluded {4}"),
    _snode((3.4, 1), <x-more>, $dots.c$),
    _gnode((1.5, 2), <x-34>, "Excluded {3,4}"),
    _gnode((1.5, 3), <x-345>, "Excluded {3,4,5}"),
    _snode((1.5, 3.6), <x-down>, $dots.v$),
    node(
      (1.5, 4.4),
      text(size: 8pt, fill: vb.muted, ${1, 2}$),
      name: <x-12>,
      inset: 3pt,
      stroke: stroke(paint: vb.muted, thickness: 0.6pt, dash: "dashed"),
      shape: rect,
      corner-radius: 2pt,
    ),
    _gnode((-0.9, 5.3), <x-s0>, "Definite 0"),
    _gnode((0.4, 5.3), <x-s1>, "Definite 1"),
    _gnode((2.6, 5.3), <x-s2>, "Definite 2"),
    _gnode((3.9, 5.3), <x-s3>, "Definite 3"),
    _snode((4.9, 5.3), <x-smore>, $dots.c$),
    _gnode((1.5, 6.4), <x-bot>, "Bot"),
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
  caption: [Goblint's exclusion sets without a bit range, ordered bottom to
    top: `Definite n` denotes ${n}$ and `Excluded S` denotes $ZZ without S$.
    Every `Excluded S` with $1, 2 in.not S$ lies above `Definite 1` and
    `Definite 2`. The blue chain of such upper bounds descends forever, and
    each of its elements lies above both values (dotted). A least upper bound
    would denote ${1, 2}$ (dashed), which no value does. Illustrative, not
    machine-checked.],
) <fig:defexc>

Goblint's domain escapes in two ways. The bit range leaves only finitely many
upper bounds of the two values. Its join does not compute the least one
anyway: joining two distinct `Definite` values yields `Excluded ({0}, r)`,
or excludes nothing if one of them is $0$. Voblint could admit this carrier
only by bounding its integers, or by weakening #isalocale("semilattice_sup")
to an upper-bound law throughout the solver and the framework. This argument
is not machine-checked.

== From values to stores <sec:domain-states>

A numeric domain describes the possible values of one variable. At a program
point, the analysis must describe whole stores, since the obligations of
@ch:traces are stated over sets of stores. A store, of type #isatype("store")
$=$ #isatype("vname") $=>$ `int`, maps every variable name to an integer. An _abstract state_ describes a set of stores. It is a
type $D$ with the order and join the solver needs and a monotone concretization
that maps each state $d$ to the set $sem(d)$ of stores it describes. One
symbol serves every kind of state, and the type of $d$ selects its definition
(#isaconst("gamma_S")). Nothing else about $D$ is fixed.
@ch:analysis-interface states the analysis for an arbitrary abstract state
and makes these requirements formal. Two kinds of abstract state are common, and this thesis uses both.

A _non-relational_, or pointwise, state gives each variable its own
abstract value and reuses a numeric domain unchanged. A _relational_ state records how variables relate to each other. They differ in what
they can state. Take the stores with $0 <= x <= y <= 5$. The best pointwise
state over intervals is ${x |-> ivl(0, 5), y |-> ivl(0, 5)}$. It shows
$x >= 0$ and $y <= 5$, but not $x <= y$, since it also admits $x = 5, y = 0$.
A relational state that records $x <= y$ shows exactly that fact, but
bounds neither variable, so it also admits $x = y = -7$. Neither state is stronger than the other. Together they describe exactly the given set. The numeric analyses of this
thesis use pointwise states, the order analysis uses a relational state, and
@ch:cooperation shows how Voblint combines them.


=== A non-relational state #thy-badge("Voblint_Domain", "Nonrelational_State") <sec:nonrel-state>

A pointwise state replaces the integer of a store by an abstract value:
#isatype("abs_state") $=$ #isatype("vname") $=>$ `'a`, so a state $sigma$ maps
every variable name $x$ to $sigma(x)$. When the state is clear, we write
$x = a$ for $sigma(x) = a$, as in $x = signval(top)$. Its concretization is
#isaconst("gamma_state"), the set of stores whose every variable lies in the
concretization of its abstract value,
$ sem(sigma) = setcomp(s, forall x. s(x) in conc(sigma(x))). $
Order and join work variable by variable (@fig:pointwise). A
pointwise state denotes no store exactly when one of its variables has an
empty value:
$ sem(sigma) = emptyset <==> exists x. isai("is_empty") (sigma(x)), $
which #isathm("is_empty_state_iff_gamma_state_empty") proves for the predicate
#isaconst("is_empty_state").

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

Some program points are reached by no execution, for example code behind a
condition that never holds. The analysis should recognize them from their
state. A pointwise state makes this hard, because it can say "unreachable" in
many ways: every state with one empty variable describes no store, and only
one of them is the bottom state (@fig:pointwise).

Neither simple test works. Treating only the all-bottom state as unreachable
misses most cases: refining a branch condition (@sec:branches) usually empties
a single variable, as in ${x |-> signval(bot), y |-> signval(top)}$. Treating
every empty state as unreachable is correct at the moment of the test, but the
information does not survive the next step: joining two differently empty
states can give a non-empty one (@fig:domain-reachability). This is sound,
since it only adds stores, but it loses the fact that the point is
unreachable.

#let _r = claim-row("dom-disjunct-sign", "13:5")
#assert(_r.verdict == "DEAD", message: "dom-disjunct-sign: the caption says unreachable")
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
          __voblint_check(false);
        }
      }
      ```.text,
    )
  })),
  kind: image,
  placement: none,
  caption: [A branch no execution enters: no integer equals both $0$ and $1$.
    Sign refines the left disjunct to
    ${x |-> signval(bot), y |-> signval(top)}$ and the right one to
    ${x |-> signval(top), y |-> signval(bot)}$. Both are empty, but their
    pointwise join is ${x |-> signval(top), y |-> signval(top)}$. With the
    lifted states below, both arms become #ctor("Bot"), and the
    analyzer reports the check in the branch as unreachable (claim
    `dom-disjunct-sign`).],
) <fig:domain-reachability>

Voblint therefore makes unreachability a value of its own. A lifted state
(#isatype("lifted")) is either #ctor("Bot"), meaning unreachable, or
$ctor("Lifted")(sigma)$ for an ordinary state $sigma$, with #ctor("Bot") below
every other value and $sem(ctor("Bot")) = emptyset$.
After every transfer, the analysis tests whether the result is empty and, if
so, replaces it by #ctor("Bot") (#isaconst("normalize_lift")). From then on
#ctor("Bot") stays #ctor("Bot"). Like `None` in an option type, it
short-circuits: a transfer applied to #ctor("Bot") is skipped and returns
#ctor("Bot"), and a join with #ctor("Bot") returns the other operand. An unreachable program point thus keeps the value #ctor("Bot"), and the
analysis can report it as unreachable. In the program of
@fig:domain-reachability, the two arms of the disjunction join as follows,
written as pairs $(sigma(x), sigma(y))$ as in @fig:pointwise, first without
and then with lifting:
$ (signval(bot), signval(top)) ljoin (signval(top), signval(bot)) & = (signval(top), signval(top)), \
                                  ctor("Bot") ljoin ctor("Bot") & = ctor("Bot"). $ Goblint separates reachability in the same way, but outside the
lattice: a transfer function that finds its path unreachable raises the
`Deadcode` exception, and the path contributes no further states.

Replacing an empty state by #ctor("Bot") does not change the stores it
describes (#isathm("gamma_state_normalize_lift")), so it cannot make the
analysis unsound. The construction needs only an emptiness test on whole
states. For a pointwise state, the test asks whether some variable is empty. A
pointwise state is a function on all variable names, an infinite set, so this
test cannot be computed by checking every name. The executable analyzer
therefore stores a state as finitely many explicit entries plus default values
for all other names, and tests only those. @sec:readback proves that this
finite test agrees with the original one.

=== A relational state #thy-badge("Voblint_Domain", "Order_Lattice") <sec:rel-state>

A relational state keeps what the pointwise form forgets. The type
#isatype("relc") records a finite set $P$ of variable pairs, where $(x, y)$
asserts $x <= y$. Its concretization is #isaconst("gamma_rel"):
$
  sem(ctor("RelC")(P)) = setcomp(s, forall (x, y) in P. s(x) <= s(y)),
  quad sem(ctor("RelBot")) = emptyset.
$
Below, the pair $(x, y)$ is written $x <= y$. More pairs describe fewer stores, so the order is reverse inclusion:
$ctor("RelC")(P) lle ctor("RelC")(Q)$ if $Q subset.eq P$, with #ctor("RelBot")
below every value and $ltop = ctor("RelC")(emptyset)$, which constrains
nothing. The join keeps the pairs both operands share,
$ctor("RelC")(P) ljoin ctor("RelC")(Q) = ctor("RelC")(P inter Q)$. The
widening is the join, and the narrowing returns its second operand. Both
satisfy the laws of the solver's classes.

#let _rnode(pos, name, body) = node(pos, text(size: 7pt, body), name: name, inset: 3pt)
#figure(
  diagram(
    spacing: (5mm, 6mm),
    _rnode((1.5, 0), <r-top>, $ltop = ctor("RelC")(emptyset)$),
    _rnode((0, 1), <r-xy>, ${x <= y}$),
    _rnode((1.5, 1), <r-yz>, ${y <= z}$),
    _rnode((3, 1), <r-xz>, ${x <= z}$),
    _rnode((0, 2), <r-xy-yz>, ${x <= y, y <= z}$),
    _rnode((1.5, 2), <r-xy-xz>, ${x <= y, x <= z}$),
    _rnode((3, 2), <r-yz-xz>, ${y <= z, x <= z}$),
    _rnode((1.5, 3), <r-all>, ${x <= y, y <= z, x <= z}$),
    _rnode((0.5, 4), <r-all-yx>, ${x <= y, y <= z, x <= z, y <= x}$),
    _rnode((2.5, 4), <r-all-zy>, ${x <= y, y <= z, x <= z, z <= y}$),
    _rnode((3.6, 4), <r-all-more>, $dots.c$),
    _rnode((0.5, 4.8), <r-down1>, $dots.v$),
    _rnode((2.5, 4.8), <r-down2>, $dots.v$),
    _rnode((1.5, 5.6), <r-nine>, [all nine pairs, $x = y = z$]),
    _rnode((1.5, 6.4), <r-bot>, ctor("RelBot")),
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
  placement: none,
  caption: [The relational states over the variables $x$, $y$ and $z$,
    ordered bottom to top by reverse inclusion. Each #ctor("RelC") value is
    drawn as its set of pairs. The upper part shows all values built from
    $x <= y$, $y <= z$ and $x <= z$. Values with other pairs, such as $y <= x$, are
    drawn only below the lowest of these, and the dots stand for the rest.
    Nine pairs exist, including $x <= x$, so the values are finitely many, and
    the lowest #ctor("RelC") value holds all nine and denotes the stores with
    $x = y = z$. For example, ${x <= y, y <= z}$ and
    ${x <= y, y <= z, x <= z}$ denote the same stores, since the first two
    pairs imply the third, yet they are different values, because the carrier
    does not close its pairs under transitivity. The join of ${x <= y, y <= z}$
    and ${x <= y, x <= z}$ keeps only their common pair and is ${x <= y}$,
    although both operands imply $x <= z$.],
) <fig:rel-state>

Emptiness is exact by construction. Every $ctor("RelC")(P)$ contains the store
that maps every variable to $0$, so only #ctor("RelBot") denotes no store, and
the emptiness test compares with it (#isathm("is_empty_relc_gamma")). Unlike
the pointwise form, the carrier has a single representation of
unreachability, so it needs no lifting.

The carrier does not close its pairs under transitivity (@fig:rel-state).
The join inherits this: joining
$ctor("RelC"){x <= y, y <= z}$ with $ctor("RelC"){x <= y, x <= z}$ yields
$ctor("RelC"){x <= y}$, although both operands imply $x <= z$.

The type instantiates the solver's classes and
#isalocale("executable_domain"). It is not a numeric domain, since its
concretization yields sets of stores rather than sets of integers, and a
relational transfer acts on the whole state, so its laws are stated per
transfer in the analysis interface. @fig:contract-routes in @ch:analysis-interface shows how
both kinds of state reach that interface, and @sec:relational turns #isatype("relc")
into an analysis.

== Learning from a guard <sec:branches>

When the analysis enters a branch, it knows whether the condition held. On the
true arm of `if (0 < x)`, for example, $x$ is positive, even though the
condition assigns no variable. Evaluating the condition forward cannot use
this: it only tells the analysis whether the condition may hold, not which
values of $x$ make it hold.

#let _g = claim-row("dom-guard-sign", "18:3")
#align(center, block(width: 60%, {
  show raw: set text(size: 6.5pt)
  listing(
    lang: "c",
    claim: "dom-guard-sign",
    ```
    x = __voblint_nondet_int();
    if (0 < x) {
      y = x;
    } else {
      y = - x;
    }
    __voblint_check(y >= 0);
    ```.text,
  )
}))

In this program $y$ ends up as $|x|$, so the check always holds. With forward
evaluation only, `0 < x` is unknown for $x = signval(top)$, both arms keep
$x = signval(top)$, $y$ becomes #signval($top$), and the state cannot show that
the check holds.
Backward refinement instead runs the condition in reverse, as in the backward
analysis of Nipkow and Klein @nipkow14[Sect. 13.7.2]. Given the truth value the
branch requires, the inverse operators of #isalocale("backward_domain") refine
the operands so that they retain every concrete pair that can produce it. The refined value is the
meet of the old value with what the guard implies. Sign refines $x$ to
$signval(top) lmeet signval("+") = signval("+")$ on the true arm and to
$signval(top) lmeet signval("≤0") = signval("≤0")$ on the false arm
(@fig:guard-meet). Both arms
then give $y$ a non-negative value, and the join yields $y = signval("≥0")$
(#raw(_g.state)). @sec:queries answers the check from this state.

The function #isaconst("bfilter") performs this refinement. It takes a
condition, the required truth value and a state, and returns the refined state.
It follows the structure of the condition, as the backward analysis of boolean
expressions of Nipkow and Klein does @nipkow14[Sect. 13.7.2], and hands
arithmetic operands to #isaconst("afilter"), which refines a state so that an
expression evaluates within a required abstract value
@nipkow14[Sect. 13.7.1]. Both are defined once, generically for every
backward domain.

A relational state learns from a guard in the same way, but what it learns is
a relation. On the true arm of `if (x < y)`, the relational state of
@sec:rel-state adds the pair $x <= y$ (#isaconst("assume_step")), which is
again the meet of its current value with $ctor("RelC"){x <= y}$. The carrier
stores only weak orders, so the strictness of $x < y$ is lost, which is sound
but less precise. A pointwise
state learns nothing there when $x$ and $y$ are unbounded, since $x < y$ bounds
neither variable on its own. For Interval and the relational state this is
proved by evaluating the analyzer on such a branch
(#isathm("demo_ivl_x_at_branch"), #isathm("demo_rel_learns_xy")).

#let _mnode(pos, name, body, kind: none) = node(
  pos,
  text(size: 8pt, body),
  name: name,
  inset: 3pt,
  stroke: if kind == "old" { stroke(paint: vb.neutral, thickness: 0.6pt, dash: "dashed") } else if (
    kind != none
  ) { 0.8pt + vb.accent } else { none },
  fill: if kind == "meet" { vb.accent.lighten(80%) } else { none },
  shape: rect,
  corner-radius: 2pt,
)
#figure(
  diagram(
    spacing: (10mm, 8mm),
    _mnode((1, 0), <m-top>, signval($top$)),
    _mnode((0.5, 1), <m-le>, signval("≤0"), kind: "guard"),
    _mnode((1.5, 1), <m-ge>, signval("≥0"), kind: "old"),
    _mnode((0, 2), <m-neg>, signval("−")),
    _mnode((1, 2), <m-zero>, signval("0"), kind: "meet"),
    _mnode((2, 2), <m-pos>, signval("+")),
    _mnode((1, 3), <m-bot>, signval($bot$)),
    ..(
      (<m-top>, <m-le>),
      (<m-top>, <m-ge>),
      (<m-le>, <m-neg>),
      (<m-ge>, <m-pos>),
      (<m-neg>, <m-bot>),
      (<m-zero>, <m-bot>),
      (<m-pos>, <m-bot>),
    ).map(((a, b)) => edge(a, b, "-", stroke: _order)),
    edge(<m-le>, <m-zero>, "-", stroke: _hit),
    edge(<m-ge>, <m-zero>, "-", stroke: _hit),
  ),
  kind: image,
  placement: none,
  caption: [Refinement as a meet in Sign, for $x$ on the false arm of
    `if (0 < x)` when $x = signval("≥0")$ held before the branch (dashed). The
    guard implies $x in conc(signval("≤0"))$ (blue outline), and the refined value is
    the meet, the greatest value below both (filled):
    $signval("≥0") lmeet signval("≤0") = signval("0")$. Illustrative.],
) <fig:guard-meet>

Refinement is a matter of precision, not soundness. A branch that ignores its
condition keeps every incoming store, and that is already sound. What the
filter must guarantee is that it never removes a store that satisfies the
condition. It may keep stores that fail it.

#block(breakable: false)[
  #theorem(name: [Sound guard filter], isa: "bfilter_sound")[
    If a store $s$ lies in $sem(sigma)$ and the guard $e$ has truth value
    #isai("res") at $s$, then $s$ lies in the meaning of the filtered state.
  ]

  #proved("bfilter_sound")
]

The relational state satisfies the same statement for its own refinement
#isaconst("branch_step_rel"), with the polarity `pol` selecting the arm:

#proved("branch_step_rel_sound")

The counting loop of @sec:constraints already used this refinement: its
inequality $b gt.eq h lmeet [-infinity, 4]$ is the refinement of the loop-head
interval $h$ at the guard `i < 5`.

== Answering queries <sec:queries>

An assertion `__voblint_check(c)` asks whether $c$ holds in every store that
reaches its program point, and the analysis must answer from the abstract state
there. Filtering by $c$ does not answer this, since a filter may keep stores that
violate $c$. Voblint therefore asks the domain, as Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/assert.ml",
)[`assert`]
analysis asks its query system.

#definition(name: [Query], isa: "check_query", cmd: "fun")[
  A query asks whether a condition $c$ holds in the stores an abstract state
  $d$ describes. The answer _true_ certifies that $c$ holds in every such
  store, _false_ that it holds in none, and _unknown_ makes no claim.
]

A domain answers only two queries on abstract values, $"less"$ and $"eq"$
(@sec:domain-contract). #isaconst("check_query") answers every condition from
these two, by recursion on the condition. A comparison first evaluates its
operands forward to abstract values $hat(a)$ and $hat(b)$ (@sec:domain-contract)
and then asks one of the two queries, with the operands swapped or the answer
negated where needed:
$
  a < b & ~> "less"(hat(a), hat(b)), & quad a > b & ~> "less"(hat(b), hat(a)), & quad
  a == b & ~> "eq"(hat(a), hat(b)), \
  a <= b & ~> not "less"(hat(b), hat(a)), & quad a >= b & ~> not "less"(hat(a), hat(b)), & quad
  a != b & ~> not "eq"(hat(a), hat(b)).
$
Negation keeps _unknown_. The connectives `!`, `&&` and `||` combine the answers
of their operands in three-valued logic: a definite _false_ decides `&&` and a
definite _true_ decides `||`, whatever the other operand answers. Any other
expression $e$ is read as $e != 0$, its truth value in VIMP. So
`x <= y && y != 0` is answered from $"less"(hat(y), hat(x))$ and
$"eq"(hat(y), hat(0))$ alone, and a new domain gets checks on arbitrary
conditions by providing these two queries.

In the program of @sec:branches, the state at the check has
$y = signval("≥0")$, and `y >= 0` becomes
$not "less"(signval("≥0"), signval("0"))$. No non-negative integer is below $0$,
so Sign's $"less"$ answers a definite _false_, and the check is answered _true_.
Without the refinement of @sec:branches, $y = signval(top)$, and
$"less"(signval(top), signval("0"))$ is _unknown_.

One proof covers every domain: a definite answer holds in every store the state
describes (#isathm("check_query_sound")), and @sec:verdicts turns the answers into
the analyzer's verdicts.
