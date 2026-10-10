#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "../lib/math.typ": *
#import "../lib/code.typ": (
  decode-isabelle, isabelle-scripts, isaconst, isai, isalocale, isathm, isatype, listing, oblig,
  thy-badge,
)
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": definition, lemma, theorem
#import "../lib/theme.typ": vb
#import "@preview/cetz:0.5.2"
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

= Abstract Domains <ch:domains>

@ch:traces reduced soundness to five obligations on a claim. A claim assigns
each node and context a set of stores. The obligations are local conditions,
and together they guarantee that the claim contains every store an execution
in that context brings there (#isathm("activation_collect_sound")). These sets
are arbitrary and usually infinite. An analyzer, however, computes with finite
abstract values, and its solver (@sec:td) compares, joins, widens and narrows them without
knowing what they mean. Recall from @sec:abs-int that an abstract value $a$
denotes a set $conc(a)$ of concrete values. A value of a numeric domain such
as Sign or Interval denotes a set of integers, $conc(a) subset.eq ZZ$. An
abstract state $d$, in contrast, denotes a set of stores,
$conc(d) subset.eq (#isatype("vname") -> ZZ)$ (@sec:domain-states). We write
$conc$ for both, as the theories do; the type of the argument determines
which concretization is meant. An
arbitrary lattice of abstract values is not enough, for two reasons. First,
the order must agree with the meaning. The solver only proves inequalities
$a lle b$ in the abstract order, while the obligations of @ch:traces are
inclusions between sets. The law
$ a lle b ==> conc(a) subset.eq conc(b) $
turns each such inequality into an inclusion (#isathm("gamma_mono"),
@fig:sign-conc). Second, a value can denote no integer without being the
lattice's bottom element. The interval pair $ivl(5, 3)$, whose lower bound
exceeds its upper bound, is such a value. An analyzer that recognizes only the
bottom element as empty misses it. This is still sound, since the analyzer
then assumes more stores than exist, but it costs precision. After the next
join, the information that a program point is dead is gone
(@sec:nonrel-state).

This chapter therefore asks what an abstract domain must provide so that the
analyzer can compute with it, every result still contains the stores it stands
for, and no precision is lost merely through the abstract representation, such
as the fact that a program point is unreachable.

#let _snode(pos, name, body) = node(pos, text(size: 8pt, body), name: name, inset: 3pt)
#let _order = 0.7pt + vb.neutral
#let _hit = 1.1pt + vb.accent
#figure(
  diagram(
    spacing: (0mm, 7.2mm),
    cell-size: (17.6mm, 4mm),
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
    (right, mirrored), both ordered bottom to top. The dashed arrows show four
    instances of $conc$. Since $conc$ is monotone, the blue step
    $signval("+") lle signval("≥0")$ becomes the inclusion
    $conc(signval("+")) subset.eq conc(signval("≥0"))$. Adapted from
    @nipkow14[Fig. 13.5].],
) <fig:sign-conc>

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
  // A parent may carry a qualifier (`backward: sound_refinement`).
  let parents = parent-text
    .split("+")
    .map(p => p.trim().split(regex("\s+")))
    .map(ws => if ws.len() > 1 and ws.at(0).ends-with(":") { ws.at(1) } else { ws.at(0) })
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
  // (mono_refinement).
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
      assert(
        not hierarchy.any(d => n in d.parents),
        message: "domain tree " + key + ": " + n + " is extended, so it is not final",
      )
      // An interpretation proves the node or a strengthening declared on top of
      // it, which the figure marks as monotone.
      let gi = src.match(regex("(?m)^global_interpretation\\s+(\\S+?):\\s+(\\S+)"))
      if gi != none {
        let (name, locale) = gi.captures
        let mono = locale != n
        assert(
          not mono or n in _decl(_snip(locale)).parents,
          message: i + " interprets " + locale + ", which does not extend " + n,
        )
        return (name: name, locale: locale, kind: "interp", mono: mono)
      }
      let m = src.match(regex("(?m)^lemma\\s+(\\S+):\\s+\"(\\S+)"))
      assert(m != none and m.captures.at(0) == i, message: "no lemma " + i)
      let locale = m.captures.at(1)
      assert(
        locale == n or locale.starts-with(n + "_"),
        message: i + " proves " + locale + ", not " + n,
      )
      (name: i, locale: locale, kind: "locale", mono: false)
    }))
  }
  // Nodes whose operations have a monotone strengthening; `domain_tree.py`
  // checks each named strengthening against the theories.
  let mono = cfg.at("mono", default: (:))
  for n in mono.keys() {
    assert(n in names, message: "domain tree " + key + ": mono " + n + " is not drawn")
  }
  (
    mono: mono,
    // Whether to draw the dashed edges to a locale's constraining class.
    bounds: cfg.at("bounds", default: true),
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

// Marks an interface whose operations have a monotone strengthening, and an
// instance that proves it.
#let mono-mark = super(text(fill: vb.accent)[M])

#let domain-tree(key) = {
  let tree = _tree(key)
  layout(size => context {
    let code(s, fill: vb.plain) = text(fill: fill, raw(decode-isabelle(s)))
    let box-of(d) = {
      let head = isalocale(d.name)
      if d.name in tree.mono { head += mono-mark }
      let rows = (
        table.cell(colspan: 2, fill: vb.at(d.origin).lighten(82%), align: center, text(
          size: 5.8pt,
          head,
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
      // A pure combination such as sound_refinement or warrowing declares
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
        )[#if instances.all(it => it.kind == "class") [instantiated by] else if instances.all(
          it => (
            it.kind == "interp"
          ),
        ) [interpreted by] else [proved by]]))
        // Types and interpretations need no second column, so they share one
        // wrapped line.
        for kind in ("class", "interp") {
          let these = instances.filter(it => it.kind == kind)
          if these != () {
            rows.push(table.cell(
              colspan: 2,
              these
                .map(it => if it.at("mono", default: false) { code(it.name) + mono-mark } else {
                  code(it.name)
                })
                .join[, ],
            ))
          }
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
      // A node wraps its statements beyond its configured width; one alone in
      // its row may otherwise take the whole line.
      let alone = tree.rows.any(r => r.len() == 1 and d.name in r)
      let cap = if d.name in tree.widths { tree.widths.at(d.name) * size.width } else if alone {
        size.width
      } else { 0.3 * size.width }
      block(
        width: calc.min(measure(t).width, cap),
        stroke: (
          paint: vb.at(d.origin),
          // An interface something implements is drawn heavier.
          thickness: if instances == () { 0.7pt } else { 1.3pt },
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
    // A straight edge must not pass behind a box it does not connect, where
    // it would read as ending there. Bent edges are left to the eye.
    let rect(n) = {
      let (width: w, height: h) = measure(boxes.at(n))
      let (x, y) = at.at(n)
      ((x - w / 2).pt() + 1, (y - h / 2).pt() + 1, (x + w / 2).pt() - 1, (y + h / 2).pt() - 1)
    }
    let hits(a, b, r) = {
      let (t0, t1) = (0.0, 1.0)
      let (ok, lo, hi) = (true, (r.at(0), r.at(1)), (r.at(2), r.at(3)))
      for i in range(2) {
        let (p, d) = (a.at(i), b.at(i) - a.at(i))
        if d == 0 {
          if p < lo.at(i) or p > hi.at(i) { ok = false }
        } else {
          let (ta, tb) = ((lo.at(i) - p) / d, (hi.at(i) - p) / d)
          t0 = calc.max(t0, calc.min(ta, tb))
          t1 = calc.min(t1, calc.max(ta, tb))
        }
      }
      ok and t0 <= t1
    }
    let centre(n) = at.at(n).map(c => c.pt())
    // An arrow implied by a longer path is left out.
    let drawn(d) = d.parents.filter(p => {
      not d.parents.any(q => q != p and p in _ancestors(tree.hierarchy, q))
    })
    let crossings = ()
    for d in tree.hierarchy {
      let ends = drawn(d).filter(p => (
        tree.parent-bends.at(d.name, default: (:)).at(p, default: 0) == 0
      ))
      if tree.bounds and tree.bends.at(d.name, default: 0) == 0 {
        ends += d.bounds.filter(b => b in at)
      }
      for p in ends {
        for n in at.keys().filter(n => n != d.name and n != p) {
          if hits(centre(d.name), centre(p), rect(n)) {
            crossings.push(d.name + " -> " + p + " behind " + n)
          }
        }
      }
    }
    assert(crossings == (), message: "domain tree " + key + ": " + crossings.join("; "))
    let hollow = (inherit: "stealth", stealth: 0, fill: white, size: 7)
    diagram(
      node-inset: 0pt,
      ..for d in tree.hierarchy {
        // Fletcher draws near-square nodes as circles unless told otherwise.
        (node(at.at(d.name), boxes.at(d.name), name: label(d.name), shape: fletcher.shapes.rect),)
      },
      ..for d in tree.hierarchy {
        for p in drawn(d) {
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
        for b in d.bounds.filter(b => tree.bounds and b in at) {
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

== What an abstract value means #thy-badge("Voblint_Domain", "Abstract_Domain") <sec:domain-carrier-laws>

The two requirements of the chapter opening become laws on the domain's
carrier. A domain is a type $A$ of abstract values, its _carrier_. The solver compares
its values, joins them where control flow merges, starts from a least value
$lbot$, and extrapolates with the widening $widen$ and the narrowing $narrow$
of @sec:widening. The analysis also needs a greatest value $ltop$ for unknown
values. A domain further supplies an emptiness test, a printer, and a
concretization $conc : A -> cal(P)(ZZ)$ with four laws. Such a type is a
_numeric domain_:

#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("numeric_domain")
}

The third and fourth laws, #isathm("gamma_mono") and
#isathm("is_empty_correct"), are the two requirements of the chapter opening.
The class extends #isalocale("executable_domain"), the part the analyzer runs, by
the concretization and its laws.

Intervals (@sec:abs-int) are this chapter's running example
#thy-badge("Voblint_Domain", "Interval_Lattice"). As in Nipkow and Klein
@nipkow14[§13.8.1], bounds are extended integers #isatype("eint"), and an
interval is a pair of bounds with
$conc(ivl(l, u)) = setcomp(n in ZZ, l <= n and n <= u)$. On non-empty pairs,
the order and join (#isaconst("less_eq_ivl"), #isaconst("sup_ivl")) are those
of @sec:abs-int. Nipkow and Klein identify all empty pairs by a quotient type.
Voblint's #isatype("ivl") is a plain datatype of bound pairs, so it must
handle them itself. Every pair with $l > u$ is
empty, and so are $ivl(+infinity, +infinity)$ and $ivl(-infinity, -infinity)$,
since no integer equals an infinite bound. The bottom value
$lbot = ivl(+infinity, -infinity)$ is only one of these empty pairs. An empty
pair such as $ivl(5, 3)$ denotes the same set as $lbot$, yet it is neither
$lbot$ nor below it.

The arithmetic operations build their results through
#isaconst("normalize_ivl"), which replaces every empty pair by
$lbot = ivl(+infinity, -infinity)$ and leaves non-empty pairs unchanged.
Otherwise $ivl(1, 0) + ivl(1, 1) = ivl(2, 1)$ would create ever new empty
values, and the solver, which tests whether a value changed (@sec:td), could
fail to stabilize. Normalizing never changes the denoted set
(#isathm("normalize_ivl_gamma")), so it is sound wherever it is applied.

The meet intersects the bounds, so
$ivl(0, 3) lmeet ivl(5, 9) = ivl(5, 3)$, an empty pair. In the order on pairs,
$ivl(5, 3)$ is the greatest lower bound of the two operands, as a meet must
be. A normalizing meet would return $lbot$ instead. However, $ivl(5, 3)$ lies
below both operands but not below $lbot$, since its lower bound $5$ is smaller
than the lower bound $+infinity$ of $lbot$. So $lbot$ would not be the greatest
lower bound (#isathm("meet_ivl_normalized_breaks_greatest")). Because an empty
pair need not be $lbot$, the emptiness test inspects the bounds
(#isaconst("is_bottom_ivl")). A pair is empty if $l > u$, if its lower bound
is $+infinity$, or if its upper bound is $-infinity$. The printer uses the same
test and shows every empty pair as $lbot$. It lies outside the verified
boundary (@sec:trust-boundary).

The widening is the standard one of @sec:widening
(#isaconst("widen_ivl_core")), with one exception: widening with $lbot$
returns the other operand. The standard rule pushes a bound to infinity
whenever the new value reaches beyond it. Both bounds of
$lbot = ivl(+infinity, -infinity)$ are exceeded by every non-empty interval, so
the rule would widen $lbot widen ivl(0, 0)$ all the way to $ltop$.
The narrowing #isaconst("narrow_ivl_td") refines only infinite bounds and
keeps finite ones, so $ivl(0, +infinity) narrow ivl(0, 10) = ivl(0, 10)$. Each
bound leaves infinity at most once, so a narrowing sequence is finite.

== From values to stores <sec:domain-states>

A numeric domain describes the possible values of one variable. The
obligations of @ch:traces, however, are stated over sets of stores. A store
maps every variable name to an integer,
$#isatype("store") = #isatype("vname") -> ZZ$, so at a program point the
analysis must describe whole stores. This thesis uses the two forms
introduced in @sec:constraints, non-relational and relational states. A non-relational description gives each
variable its own abstract value, and a relational one records how variables
relate to each other. The two differ in what they can state. Take the stores with
$0 <= x <= y <= 5$ (@fig:rel-vs-nonrel). The best non-relational description
over intervals is ${x |-> ivl(0, 5), y |-> ivl(0, 5)}$. It shows $x >= 0$ and
$y <= 5$, but not $x <= y$, since it also admits $x = 5, y = 0$. A relational
description that records $x <= y$ shows exactly that fact, but it bounds
neither variable, so it also admits $x = y = -7$. Neither description is
therefore stronger than the other. Together, however, they describe exactly
the given set.

#figure(
  cetz.canvas(length: 0.5cm, {
    import cetz.draw: *
    let lbl(pos, body, anchor: "west", fill: vb.plain) = content(
      pos,
      text(size: 7.5pt, fill: fill, body),
      anchor: anchor,
    )
    // The half-plane x <= y, clipped to the drawn window.
    line((-1, -1), (-1, 7), (7, 7), close: true, fill: vb.muted.lighten(82%), stroke: none)
    line((-1, -1), (7, 7), stroke: (paint: vb.muted, thickness: 0.6pt))
    // The best non-relational state: the box [0, 5] x [0, 5].
    rect((0, 0), (5, 5), stroke: (paint: vb.neutral, thickness: 0.8pt, dash: "dashed"))
    line((-1, 0), (7.3, 0), stroke: 0.5pt + vb.neutral, mark: (end: ">", fill: vb.neutral))
    line((0, -1), (0, 7.3), stroke: 0.5pt + vb.neutral, mark: (end: ">", fill: vb.neutral))
    lbl((7.4, 0), $x$)
    lbl((0, 7.4), $y$, anchor: "south")
    for x in range(6) {
      for y in range(x, 6) { circle((x, y), radius: 0.12, fill: vb.accent, stroke: none) }
    }
    circle((5, 0), radius: 0.14, fill: none, stroke: 0.8pt + vb.neutral)
    lbl((5.25, 0.35), $(5, 0)$, fill: vb.neutral)
    lbl((5.3, 5.4), [$ivl(0, 5) times ivl(0, 5)$], fill: vb.neutral)
    lbl((1.2, 6.4), [$x <= y$], fill: vb.muted)
  }),
  kind: image,
  placement: none,
  caption: [Stores over two variables as points $(x, y)$. The stores with
    $0 <= x <= y <= 5$ are the dots. The best non-relational state denotes the
    square (dashed), which also admits $(5, 0)$. The relational state
    ${x <= y}$ denotes the half-plane above the diagonal (shaded), which is
    unbounded. Their intersection is exactly the dots. Illustrative.],
) <fig:rel-vs-nonrel>

An _abstract state_ describes a set of stores. It is a type $D$ with
the order and join the solver needs and a monotone concretization that maps
each state $d$ to the set $conc(d)$ of stores it describes. Each kind of state
defines its own concretization, and Isabelle overloads one constant,
#isaconst("gamma_S"), written $conc(d)$, for all of them. The numeric analyses use non-relational states. An analysis that records
relations $x <= y$ between variables uses a relational state.

=== A non-relational state #thy-badge("Voblint_Domain", "Nonrelational_State") <sec:nonrel-state>

A non-relational state is represented pointwise. It replaces the integer of a
store by an abstract value:
#isatype("abs_state") $=$ #isatype("vname") $=>$ `'a`, so a state $d$ maps
every variable name $x$ to $d(x)$. Its concretization admits a store if every
variable's value lies in the concretization of its abstract value:

#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("gamma_state")
}

Order and join work variable by variable, as for any function type in HOL.
A state $d_1$ lies below $d_2$ if $d_1(x) lle d_2(x)$ for every variable $x$,
and the join is $(d_1 ljoin d_2)(x) = d_1(x) ljoin d_2(x)$
(@fig:pointwise). Because $conc$ is monotone, so is this concretization, and a
larger state describes more stores.

#let _pw-vals = ($bot$, "0", $top$)
#figure(
  diagram(
    spacing: (7mm, 4.9mm),
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
  placement: auto,
  caption: [Pointwise states $(d(x), d(y))$ over two variables, with values
    from the fragment $signval(bot) lle signval("0") lle signval(top)$ of Sign,
    ordered variable by variable. The dashed states have a #signval($bot$)
    component and denote no store, although only the lowest one is the bottom
    state.],
) <fig:pointwise>

Some program points are reached by no execution, for example code behind a
condition that never holds. The analysis should recognize them from their
state. A pointwise state makes this hard, because it can say "unreachable" in
many ways. Every state with one empty variable describes no store, and only
one of them is the bottom state (@fig:pointwise).

Neither simple test works. Treating only the all-bottom state as unreachable
misses most cases, because refining a branch condition (@sec:branches) usually
empties a single variable, as in ${x |-> signval(bot), y |-> signval(top)}$. Treating
every empty state as unreachable is correct at the moment of the test, but the
information does not survive the next step. Joining two differently empty
states can give a non-empty one (@fig:domain-reachability). This is sound,
since it only adds stores, but it loses the fact that the point is unreachable
and is thus imprecise.

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
  caption: [A branch no execution enters, since no integer equals both $0$
    and $1$.
    Sign refines the left disjunct to
    ${x |-> signval(bot), y |-> signval(top)}$ and the right one to
    ${x |-> signval(top), y |-> signval(bot)}$. Both are empty, but their
    pointwise join is ${x |-> signval(top), y |-> signval(top)}$. The branch
    turns each empty arm into #ctor("Bot") before the join, and the
    analyzer reports the check in the branch as unreachable (claim
    #claim-ref("dom-disjunct-sign")).],
) <fig:domain-reachability>

Voblint therefore makes unreachability a value of its own, as Nipkow and
Klein do with an option type @nipkow14[§13.7] and as Goblint does. Goblint's
framework lifts the local state by an outer bottom element for dead code
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L120-L135")[`Analyses.Dom`]), and a transfer function that finds its path unreachable
raises the `Deadcode` exception instead of returning a state. In Voblint, a
lifted state (#isatype("lifted")) is either #ctor("Bot"), meaning unreachable,
or $ctor("Lifted")(d)$ for an ordinary state $d$, with #ctor("Bot") below every
other value and $conc(ctor("Bot")) = emptyset$.

After every transfer, the analysis tests whether the result is empty and, if
so, replaces it by #ctor("Bot") (#isaconst("normalize_lift")). Comparing with
the bottom state cannot implement this test, for the reason above. The test
instead asks the domain's emptiness test, which #isathm("is_empty_correct")
makes exact for every value. A pointwise state is empty exactly when some
variable's value is (#isaconst("is_empty_state"),
#isathm("is_empty_state_iff_gamma_state_empty")). The variable names form an
infinite set, so the executable analyzer decides this on a finite
representation of the state (@sec:represented-function). Replacing an empty
state by #ctor("Bot") only exchanges one abstract representation of the empty
set for another, equivalent one (#isathm("gamma_state_normalize_lift")), so it
cannot make the analysis unsound.

From then on #ctor("Bot") stays #ctor("Bot"). A transfer applied to
#ctor("Bot") is skipped and returns #ctor("Bot"), and a join with #ctor("Bot") returns the other operand. An
unreachable program point thus keeps the value #ctor("Bot"), and the analysis
can report it as unreachable. In the program of @fig:domain-reachability, both
arms are joined inside one branch transfer, so the test after the transfer
would come too late. The branch refinement of @sec:branches therefore also
replaces each empty arm of a disjunction by #ctor("Bot") before the join, and
the two arms join to #ctor("Bot").

=== A relational state #thy-badge("Voblint_Domain", "Order_Lattice") <sec:rel-state>

A relational state keeps what the pointwise form forgets. Its concretization
therefore maps a whole state to a set of stores directly, instead of a value
to a set of integers. The type #isatype("relc") records a set $P$ of variable
pairs, where the pair $(x, y)$ stands for the constraint $x <= y$. Its
concretization is #isaconst("gamma_relc"):
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
(#isaconst("sup_relc")). The widening is simply the join. The solver's
widening contract (#isalocale("widening")) only asks for a value above both
operands, and the join is one, although the contract alone does not force the
iteration to terminate. Here an ascending chain can only drop pairs
from a finite set, since every constructed $P$ is finite (below), so it is
finite anyway. The narrowing returns its second
operand, the newly computed value. This is sound for the same reason, since
the narrowing law only asks for a value between the two operands.

The carrier does not close its pairs under transitivity (@fig:rel-state). The
values ${x <= y, y <= z}$ and ${x <= y, y <= z, x <= z}$ therefore denote the
same stores but are different values. The join can also forget an implied
relation. The join of ${x <= y, y <= z}$ and ${x <= y, x <= z}$ keeps only
their common pair and is ${x <= y}$, although both operands imply $x <= z$.

Pairs enter only at guards, and an assignment to $x$ removes every pair that
mentions $x$, so $P$ is finite in every value the analysis constructs. This matters for the
executable analyzer. Generated code stores a finite set as the list of its
elements, while an infinite set, such as the set of all pairs, needs a
complement representation for which not every set operation has executable
code.

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
  placement: auto,
  caption: [The relational states over the variables $x$, $y$ and $z$,
    ordered bottom to top by reverse inclusion. Each #ctor("RelC") value is
    drawn as its set of pairs. The upper part shows all values built from
    $x <= y$, $y <= z$ and $x <= z$. Values with other pairs, such as $y <= x$, are
    drawn only below the lowest of these, and the dots stand for the rest.
    Nine pairs exist, including $x <= x$, so the values are finitely many, and
    the lowest #ctor("RelC") value holds all nine and denotes the stores with
    $x = y = z$.],
) <fig:rel-state>

All constraints in $P$ can be satisfied simultaneously by assigning the same
value to every variable. In particular, the store that maps every variable to $0$ satisfies every pair
in $P$. Therefore every $ctor("RelC")(P)$ denotes at least one store,
regardless of which constraints $P$ contains. Only #ctor("RelBot") denotes the
empty set of stores. The emptiness
test only compares with #ctor("RelBot") (#isathm("is_empty_relc_gamma")).
Unlike the pointwise form, the carrier has a single representation of
unreachability, so it needs no lifting.

A relational state stores no value per variable, so it cannot evaluate an
expression to an abstract value. Its transfers update the constraints
directly instead. An assignment to $x$ forgets every pair that mentions $x$,
and a comparison between two variables adds the pairs it implies
(@sec:branches). The type instantiates
the solver's classes and #isalocale("executable_domain"), but it is not a
numeric domain. The next three sections introduce operations on single
numeric values. They serve non-relational states, and @sec:branches returns to
the relational state at its end.

== Evaluating expressions #thy-badge("Voblint_Domain", "Forward_Domain") <sec:domain-forward>

The carrier operations serve the solver. The analysis additionally needs
operations that mirror the program's own arithmetic, comparisons and branch
conditions. We call them the domain's _primitives_. This section
and the next two introduce them, one use at a time.

An assignment `x = e` needs the abstract value of $e$. Forward evaluation
computes it from an abstract state $d$, as in the generic abstract interpreter
of Nipkow and Klein @nipkow14[§13.5.3]. The abstract result $asem(e) thin d$ must contain
every concrete result (#isalocale("sound_evaluator")):
$ s in conc(d) ==> sem(e)_e thin s in conc(asem(e) thin d). $
Interval evaluates by interval arithmetic on the bounds (#isaconst("aval_ivl")).
For example, if $d(x) = ivl(0, 9)$, Interval evaluates `x + 1` to
$ivl(1, 10)$.

A condition is an expression too, and VIMP reads its value as a truth value,
with non-zero meaning true. If the abstract value of a condition admits only
one truth value, a branch can drop the arm that needs the other. A domain
therefore also supplies a truth test (#isalocale("sound_truth_test")). The
test $"tobool"(a)$ answers in three values. It returns $"Some"(b)$ if every
integer in $conc(a)$ has truth value $b$, and $"None"$ otherwise:
$ "tobool"(a) = "Some"(b) and i in conc(a) ==> (i != 0) = b. $
Interval's test #isaconst("interval_tobool") returns $"Some"("true")$ for
$ivl(l, u)$ if the interval excludes $0$, that is $u < 0$ or $l > 0$, and
$"Some"("false")$ if $l = u = 0$. Otherwise it returns $"None"$. So
$ivl(1, 5)$ is true, $ivl(0, 0)$ is false, and $ivl(0, 5)$ is undecided.

== Answering queries <sec:queries>

An assertion `__voblint_check(c)` asks whether $c$ holds in every store that
reaches its program point. The analysis must answer this from the abstract
state there alone. Voblint answers it through queries, as does Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/assert.ml",
)[`assert`]
analysis.

A domain answers two comparisons on abstract values, $"less"(a, b)$ for
$a < b$ and $"eq"(a, b)$ for $a = b$. Like the truth test, each answers in
three values. A definite answer must hold for every pair of integers the two
values denote, and $"None"$, meaning unknown, is always allowed:

#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("sound_numeric_queries")
}

Domains differ in which comparisons they can decide. Interval decides $a < b$
when one interval lies entirely below the other, where a shared endpoint
suffices for the answer false, and $a = b$ when the intervals are disjoint or
the same single integer. Sign decides $a < b$ whenever the signs separate the
values, for example for zero and a positive value. Parity and Congruence, the
domains of @ch:instances, are weaker here. Parity can only refute equality
between an even and an odd value and never decides $<$. Congruence answers
only when both values are single integers.

#definition(name: [Query], isa: "check_query", cmd: "fun")[
  A query evaluates a condition $c$ on an abstract state $d$ to one of three
  answers, _true_, _false_ or _unknown_, by recursion on $c$, using only the
  domain's two comparisons.
]

In #isaconst("check_query"), a comparison first evaluates its operands forward to abstract values $hat(a)$ and $hat(b)$
(@sec:domain-forward) and then asks one of the two comparisons, with the operands
swapped or the answer negated where needed:
$
  a < b & ~> "less"(hat(a), hat(b)), & quad a > b & ~> "less"(hat(b), hat(a)), & quad
  a == b & ~> "eq"(hat(a), hat(b)), \
  a <= b & ~> not "less"(hat(b), hat(a)), & quad a >= b & ~> not "less"(hat(a), hat(b)), & quad
  a != b & ~> not "eq"(hat(a), hat(b)).
$

Negation keeps _unknown_. The connectives `!`, `&&` and `||` combine the answers
of their operands in three-valued logic. A definite _false_ decides `&&`, and a
definite _true_ decides `||`, whatever the other operand answers. Both
operands are judged in the same state, so for $x$ in $ivl(1, 2)$,
`x == 1 || x == 2` stays unknown although every store satisfies it (claim
#claim-ref("dom-disjunction-one-state")). Goblint is more precise here. CIL
compiles `&&` and `||` into branches
(#link("https://github.com/goblint/cil/blob/003821f1d4a95c758bb255080e9b91a22ea5df31/src/frontc/cabs2cil.ml#L5264-L5299")[`cabs2cil.ml`]),
and where `x == 1` fails, Goblint's interval refinement narrows $ivl(1, 2)$ to
$ivl(2, 2)$
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/baseInvariant.ml#L395-L410")[`baseInvariant.ml`],
@saan26phd[§4.5.1, Rem. 8]). Voblint's interval inverse of a failed equality
changes nothing (#isaconst("inv_eq_ivl")). Any other
expression $e$ is read as $e != 0$, its truth value in VIMP. A new domain
therefore gets checks on arbitrary conditions by providing these two
comparisons.
One proof covers every domain. The answer _true_ certifies that $c$ holds in
every store the state describes, _false_ that it holds in none, and _unknown_
makes no claim (#isathm("check_query_sound")). #isalocale("sound_check_query")
combines the queries with forward evaluation, and @sec:verdicts turns the
answers into the analyzer's verdicts.

The condition `x <= y && y != 0` is answered from $"less"(hat(y), hat(x))$ and
$"eq"(hat(y), hat(0))$ alone. In Sign, with $x$ non-positive and $y$ positive,
both comparisons give a definite _false_, both negations give _true_, and so does
the conjunction (@fig:query-tree).

#let _q = claim-row("dom-query-tree-sign", "11:7")
#assert(_q.verdict == "PROVED", message: "dom-query-tree-sign: the figure says proved")
#let _qn(pos, name, body, query: false) = node(
  pos,
  text(size: 8.5pt, body),
  name: name,
  inset: 4pt,
  stroke: if query { 0.8pt + vb.accent } else { 0.6pt + vb.neutral },
  fill: if query { vb.accent.lighten(88%) } else { none },
  shape: rect,
  corner-radius: 2pt,
)
#figure(
  diagram(
    spacing: (8mm, 11mm),
    _qn((1, 0), <q-and>, [`x <= y && y != 0`: _true_]),
    _qn((0, 1), <q-le>, [`x <= y` #h(0.3em) $~> not "less"(hat(y), hat(x))$: _true_]),
    _qn((2, 1), <q-ne>, [`y != 0` #h(0.3em) $~> not "eq"(hat(y), hat(0))$: _true_]),
    _qn((0, 2), <q-less>, [$"less"(signval(+), signval("≤0"))$: _false_], query: true),
    _qn((2, 2), <q-eq>, [$"eq"(signval(+), signval("0"))$: _false_], query: true),
    edge(<q-and>, <q-le>, "-", stroke: _order),
    edge(<q-and>, <q-ne>, "-", stroke: _order),
    edge(<q-le>, <q-less>, "-", stroke: 1.1pt + vb.accent),
    edge(<q-ne>, <q-eq>, "-", stroke: 1.1pt + vb.accent),
  ),
  kind: image,
  placement: none,
  caption: [How #isaconst("check_query") answers a compound condition, in Sign
    with #raw(_q.state) (claim #claim-ref("dom-query-tree-sign")). Each comparison becomes
    one of the domain's two comparisons (blue), as $~>$ marks; the answer follows
    the colon. Negation flips a definite answer,
    and `&&` is true because both operands are, so the check is
    #_q.verdict.],
) <fig:query-tree>

== Learning from a guard #thy-badge("Voblint_Domain", "Backward_Domain") <sec:branches>

When the analysis enters a branch, it knows whether the condition held. On the
true arm of `if (0 < x)`, for example, $x$ is positive. Ignoring this knowledge is sound, since the
state before the branch already contains every store that takes either arm.
It costs precision, however, as the following program shows.

#let _g = claim-row("dom-guard-interval", "18:3")
#align(center, block(width: 60%, {
  show raw: set text(size: 6.5pt)
  listing(
    lang: "c",
    claim: "dom-guard-interval",
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

In this program $y$ ends up as $|x|$, so the check always holds. Without
refinement, both arms keep $x |-> ltop$, $y$ becomes $ltop$, and the state
cannot show that the check holds. Backward refinement runs the condition in
reverse, as in the backward abstract interpretation of tests by Cousot
@cousot99[§§8.5, 10.1] and the backward analysis of Nipkow and Klein
@nipkow14[§13.7].
Given abstract operands $a_1, a_2$ and the result an operation must produce,
an inverse operator returns refined operands $a'_1, a'_2$ that keep every
concrete pair producing that result. For a comparison that must yield $r$:
$
  n_1 in conc(a_1) and n_2 in conc(a_2) and (n_1 < n_2) = r
  ==> n_1 in conc(a'_1) and n_2 in conc(a'_2),
$
and likewise for equality, addition, subtraction and multiplication
(#isalocale("sound_inverse_ops")).

The refined operand is then combined with the value known before. Nipkow and
Klein use the lattice meet for this and require it to be exact on the denoted
sets. Voblint asks for less, namely an intersection that keeps every integer
both operands share and lies below both (#isalocale("sound_intersection"), shown in
@sec:isabelle). For Interval it is the normalized meet
#isaconst("intersect_ivl"), which agrees with the meet on the operands below. In the program above, Interval
refines $x$ to $ltop lmeet ivl(1, +infinity) = ivl(1, +infinity)$ on the true
arm and to
$ivl(-infinity, 0)$ on the false arm. Both arms then give $y$ a non-negative
value, and the join yields #raw(_g.state).

The guard filter #isaconst("bfilter") takes a condition, the required truth
value and a state, and applies the inverse operators along the structure of
the condition. For the arithmetic operands of a comparison it calls
#isaconst("afilter"), which refines a state so that an expression evaluates
within a required value @nipkow14[§13.7.1]. Its soundness is exactly what
the branch needs, since it never removes a store that satisfies the guard.
The filter refines a conjunction from right to left. Each conjunct is applied
once, to the state the conjuncts on its right have refined, and the filter does
not iterate to a local fixpoint. Which bound reaches which variable can therefore
depend on the order of the conjuncts. With Interval, `0 < i && i < j && j < 10`
bounds $i$ to $ivl(1, 8)$ but not $j$ from below, and the reversed order bounds
$j$ to $ivl(2, 9)$ but not $i$ from above (claim
#claim-ref("dom-conjunct-order")).

#block(breakable: false)[
  #lemma(name: [Sound guard filter], isa: "bfilter_sound")[
    If a store $s$ lies in $conc(d)$ and the guard $e$ has truth value
    #isai("res") at $s$, then $s$ lies in the meaning of the filtered state.
  ]

  #proved("bfilter_sound")
]

The shipped inverse operators are sound but not the most precise possible.
Interval and Sign, for
instance, do not invert arithmetic and cannot learn $x < 4$ from `x + 1 < 5`,
as the interval analysis of Nipkow and Klein does @nipkow14[§13.8.3].

The branch transfer #isaconst("sound_refinement.branch") first drops an arm
that the truth test rules out, and otherwise applies the filter. Where it joins
the arms of a disjunction, it uses #isaconst("bfilter_lifted"), which turns
each empty arm into #ctor("Bot") first (@sec:nonrel-state). The branch inherits the filter's
soundness (#isathm("sound_refinement.branch_sound")).

A relational state learns from a guard in the same way, but what it learns is
a relation. On the true arm of `if (x < y)`, the relational
state of @sec:rel-state adds the pair $x <= y$ (#isaconst("assume_step")), the
meet of its current value with $ctor("RelC"){x <= y}$. The carrier
stores only weak orders, so the strictness of $x < y$ is lost, which is sound
but less precise. The relational refinement #isaconst("relc_branch_step")
satisfies the same statement as the filter
(#isathm("relc_branch_step_sound")).

== The complete domain interface #thy-badge("Voblint_Nonrelational", "Nonrelational_Transfer") <sec:domain-contract>

The operations of this chapter fall into two groups. The _carrier operations_
serve the solver: the order, the join, bottom and top, widening and narrowing,
the emptiness test and the printer (@sec:domain-carrier-laws). The
_primitives_ mirror the program's operations: evaluation and the truth test
(@sec:domain-forward), the two comparisons (@sec:queries), and the inverse
operators and the intersection (@sec:branches). Every non-relational domain
hands its primitives over as one record of type #isatype("nonrelational_ops"),
for Interval #isaconst("ivl_ops"), and proves them sound once by interpreting
#isalocale("sound_nonrelational_ops") (@fig:domain-carrier).

The record contains no transfer function, because the primitives determine
every edge. An assignment `x = e` overwrites $x$ with the abstract value of $e$,
and a skip leaves the state unchanged. A branch is the backward refinement of
@sec:branches, built from the evaluator, the truth test and the inverse
operators. Procedure entry evaluates the arguments in the caller's state, sets
every variable of the callee to $ltop$, and binds the formal parameters. A new
non-relational domain therefore supplies values and primitives only, and its
interpretation of #isalocale("sound_nonrelational_ops") proves all of these
transfers sound at once.

#figure(
  domain-tree("carrier"),
  kind: image,
  placement: top,
  caption: [What a non-relational domain supplies over its carrier type
    #raw("'a"), down to the soundness locale #isalocale("sound_nonrelational_ops")
    an analysis interprets. Each class (solid) or locale (dashed) lists the
    operations and laws it declares, which the declarations below it inherit.
    Solid arrows point to what a declaration extends, dashed ones to the class
    its type variable is constrained to. An interface an analysis implements
    has a heavier border and lists its instances. A superscript #mono-mark
    marks an interface with a monotone strengthening, and an interpretation
    that proves it (#isalocale("mono_nonrelational_ops")). Colour gives where a
    node is declared: #swatch(vb.hol) HOL, #swatch(vb.solver) the vendored
    solver, #swatch(vb.voblint) Voblint.],
) <fig:domain-carrier>

== A carrier the interface excludes <sec:no-defexc>

Voblint cannot host every domain Goblint offers. The verified solver requires
its values to form a #isalocale("bounded_semilattice_sup_bot")
(#isalocale("TD_side_upd_rule")), and the generic framework inherits the
requirement. That class asks for the _least_ upper bound
(#isalocale("semilattice_sup")), and the proofs use it. Reductive refinement
bounds the join of two disjunction arms by the state it started from
(#isathm("sound_refinement.bfilter_reductive")). This requirement excludes every
carrier in which two values have upper bounds but no least one.

Goblint's exclusion-set domain
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/cdomain/value/cdomains/int/defExcDomain.ml",
)[`DefExc`]
is such a carrier once its bit range is removed. A non-bottom value is
`Definite n`,
denoting ${n}$, or `Excluded (S, r)`, denoting the integers in the bit range
$r$ outside the finite set $S$. Mathematical integers have no bit range, so
`Excluded S` denotes $ZZ without S$ (@fig:defexc). Then `Definite 1` and
`Definite 2` have no least upper bound. Every `Excluded {p}` with
$p in.not {1, 2}$ lies above both. A least upper bound $u$ would lie below
each of them, so by monotonicity of $conc$
$ {1, 2} subset.eq conc(u) subset.eq inter.big_(p in.not {1, 2}) (ZZ without {p}) = {1, 2}, $
but no value denotes exactly ${1, 2}$, since `Definite n` denotes a single
integer and `Excluded S` all but finitely many.

#let _gnode(pos, name, body) = node(pos, text(size: 7pt, raw(body)), name: name, inset: 3pt)
#figure(
  diagram(
    spacing: (4.5mm, 4.5mm),
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
  placement: none,
  caption: [Goblint's exclusion sets without a bit range, ordered bottom to
    top: `Definite n` denotes ${n}$ and `Excluded S` denotes $ZZ without S$.
    Every `Excluded S` with $1, 2 in.not S$ lies above `Definite 1` and
    `Definite 2`. The blue chain of such upper bounds descends forever, and
    each of its elements lies above both values (dotted). A least upper bound
    would denote ${1, 2}$ (dashed), which no value does. Illustrative, not
    machine-checked.],
) <fig:defexc>

Goblint's domain escapes this argument through its bit range. With a range $r$,
the value `Excluded (`$r without {1, 2}$`, r)` denotes exactly ${1, 2}$. Its
join does not return this value anyway. Joining two distinct `Definite`
values yields `Excluded ({0}, r)`, or excludes nothing if one of them is $0$. Voblint could admit this carrier
only by bounding its integers, or by weakening #isalocale("semilattice_sup")
to an upper-bound law throughout the solver and the framework.

The domain interface is now complete. Its laws make every operation keep the
stores its inputs admit, but each law speaks only about one value or one state.
A program moves its state along edges and through calls, and
@ch:analysis-interface states what an analysis must prove there.
