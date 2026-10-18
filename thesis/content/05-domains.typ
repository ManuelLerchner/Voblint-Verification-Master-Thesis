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
and together they guarantee that the claim contains every store that an execution in that context reaches at the node (#isathm("activation_collect_sound")). These sets
are arbitrary and usually infinite. An analyzer, however, computes with finite
abstract values, and its solver (@sec:td) compares, joins, widens, and narrows them without
knowing what they mean. Recall from @sec:abs-int that an abstract value $a$
denotes a set $conc(a)$ of concrete values. A value of a numeric domain such
as Sign or Interval denotes a set of integers, $conc(a) subset.eq ZZ$. An
abstract state $d$, in contrast, denotes a set of stores,
$conc(d) subset.eq (#isatype("vname") -> ZZ)$ (@sec:domain-states). We write
$conc$ for both, as the theories do. The type of the argument determines
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
$conc(ivl(l, u)) = setcomp(n in ZZ, l <= n and n <= u)$. On nonempty pairs,
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
$lbot = ivl(+infinity, -infinity)$ and leaves nonempty pairs unchanged.
Otherwise $ivl(1, 0) + ivl(1, 1) = ivl(2, 1)$ would keep creating new empty values, and the solver, which tests whether a value changed (@sec:td), could
fail to stabilize. Normalizing never changes the denoted set
(#isathm("normalize_ivl_gamma")), so it is sound wherever it is applied.

The meet intersects the bounds and does not normalize, since $lbot$ would not
be the greatest lower bound of, say, $ivl(0, 3)$ and $ivl(5, 9)$ in the order
on pairs (#isathm("meet_ivl_normalized_breaks_greatest")). An empty pair is
therefore not necessarily $lbot$, and the emptiness test inspects the bounds
(#isaconst("is_bottom_ivl")): a pair is empty if $l > u$, if its lower bound is
$+infinity$, or if its upper bound is $-infinity$. The widening is the
standard one of @sec:widening, except that widening with $lbot$ returns the
other operand (#isaconst("widen_ivl_core")), and the narrowing refines only
infinite bounds (#isaconst("narrow_ivl_td")).

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
neither variable, so it also admits $x = y = -7$. Therefore neither description is stronger than the other. Together, however, they describe exactly
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
the order and join the solver needs, and a monotone concretization that maps
each state $d$ to the set $conc(d)$ of stores it describes. Each kind of state
defines its own concretization, and Isabelle overloads one constant,
#isaconst("gamma_S"), written $conc(d)$, for all of them. The numeric
analyses use non-relational states. An analysis that records relations
$x <= y$ between variables uses a relational state, whose concretization maps
a whole state to a set of stores instead of each variable to a set of
integers. The interface of this chapter admits such a state, because the
solver and the framework ask only for order, join, and a monotone
concretization, never for a map from variables to abstract values. The
relational state of the order analysis instantiates the solver's classes and
#isalocale("executable_domain") without being a numeric domain
(@sec:rel-state). The remaining sections of this chapter develop the
non-relational case.

== A non-relational state #thy-badge("Voblint_Domain", "Nonrelational_State") <sec:nonrel-state>

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
states can give a nonempty one (@fig:domain-reachability). This is sound,
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
so, replaces it with #ctor("Bot") (#isaconst("normalize_lift")). Comparing with
the bottom state cannot implement this test, for the reason above. Instead, the test relies on the domain's emptiness test, which #isathm("is_empty_correct")
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
replaces each empty arm of a disjunction with #ctor("Bot") before the join, and
the two arms join to #ctor("Bot").

== Evaluating expressions #thy-badge("Voblint_Domain", "Forward_Domain") <sec:domain-forward>

The carrier operations serve the solver. The analysis additionally needs
operations that mirror the program's own arithmetic, comparisons, and branch conditions. We call them the domain's _primitives_. This section
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
with nonzero meaning true. If the abstract value of a condition admits only
one truth value, a branch can drop the arm that needs the other. A domain
therefore also supplies a truth test (#isalocale("sound_truth_test")). The
test $"tobool"(a)$ has three possible answers. It returns $"Some"(b)$ if every
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
$a < b$ and $"eq"(a, b)$ for $a = b$. Like the truth test, each has three possible answers. A definite answer must hold for every pair of integers the two
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
  answers, _true_, _false_, or _unknown_, by recursion on $c$, using only the
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
definite _true_ decides `||`, regardless of the other operand's answer. Both
operands are evaluated in the same state, so for $x$ in $ivl(1, 2)$,
`x == 1 || x == 2` stays unknown, although every store satisfies it (claim
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
combines the queries with forward evaluation. An analysis passes these answers
to its partners and to the verdicts as answers to the query
#isaconst("EvalInt") of @sec:coop-queries (@sec:coop-mcp, @sec:verdicts).

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
Given abstract operands $a_1, a_2$, and the result an operation must produce,
an inverse operator returns refined operands $a'_1, a'_2$ that keep every
concrete pair producing that result. For a comparison that must yield $r$:
$
  n_1 in conc(a_1) and n_2 in conc(a_2) and (n_1 < n_2) = r
  ==> n_1 in conc(a'_1) and n_2 in conc(a'_2),
$
and likewise for equality, addition, subtraction, and multiplication
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
not iterate to a local fixpoint. The bounds that reach each variable can therefore depend on the order of the conjuncts. With Interval, `0 < i && i < j && j < 10`
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

== The complete domain interface #thy-badge("Voblint_Nonrelational", "Nonrelational_Transfer") <sec:domain-contract>

The operations of this chapter fall into two groups. The _carrier operations_
serve the solver: the order, the join, bottom and top, widening and narrowing,
the emptiness test, and the printer (@sec:domain-carrier-laws). The
_primitives_ mirror the program's operations: evaluation and the truth test
(@sec:domain-forward), the two comparisons (@sec:queries), and the inverse
operators and the intersection (@sec:branches). Every non-relational domain
hands its primitives over as one record of type #isatype("nonrelational_ops"),
for Interval #isaconst("ivl_ops"), and proves them sound once by interpreting
#isalocale("sound_nonrelational_ops") (@fig:domain-carrier).

The record contains no transfer function, because the primitives determine
every edge. An assignment `x = e` overwrites $x$ with the abstract value of $e$,
and a skip leaves the state unchanged. A branch is the backward refinement of
@sec:branches, built from the evaluator, the truth test, and the inverse
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
    that proves it (#isalocale("mono_nonrelational_ops")). Color gives where a
    node is declared: #swatch(vb.hol) HOL, #swatch(vb.solver) the vendored
    solver, #swatch(vb.voblint) Voblint.],
) <fig:domain-carrier>

The interface also excludes some carriers. The verified solver requires a
#isalocale("bounded_semilattice_sup_bot") (#isalocale("TD_side_upd_rule")),
whose join is the _least_ upper bound, and the framework's proofs use
leastness (#isathm("sound_refinement.bfilter_reductive")). Goblint's
exclusion-set domain
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/cdomain/value/cdomains/int/defExcDomain.ml")[`DefExc`],
stripped of its bit range so that it describes mathematical integers, has no
least upper bound of `Definite 1` and `Definite 2`. Every `Excluded {p}` with
$p in.not {1, 2}$ lies above both, so a least upper bound would have to denote
exactly ${1, 2}$, which no value does. Voblint could admit such a carrier only
by bounding its integers or by weakening the join to an upper bound throughout
the solver and the framework.

== Executable states <sec:exec-states>

The non-relational state of @sec:nonrel-state is a total function on
infinitely many variable names. The solver cannot compute with it, because it
compares states after every evaluation, so the analyzer runs on a finite
representation, and the soundness proved for function states must carry over
to it. The obligation is a commutation law. Each executable operation, read
back as the function it represents, must equal the abstract operation on that
function (#isathm("sound_nonrelational_ops.tf_st_for_commute")). Abstract and
executable steps are built from the same primitives, so the law holds for
every domain without a proof of its own, and the executable local
specification inherits the soundness of the abstract one:

#proved("exec_local_spec_sound")

The analysis contract of @ch:analysis-interface therefore holds for the code
that is exported, not only for its specification. @sec:represented-function
describes the representation itself, a pair of finite default dictionaries
with an exact emptiness test.

The domain interface is now complete. Its laws make every operation keep the
stores its inputs admit, but each law speaks only about one value or one state.
A program moves its state along edges and through calls, and
@ch:analysis-interface states what an analysis must prove there.
