#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "../lib/math.typ": *
#import "../lib/code.typ": (
  decode-isabelle, fixture, isabelle-scripts, isaconst, isalocale, isathm, isatype, listing,
  thy-badge,
)
#import "../lib/figures.typ": check-row, verdict
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

@ch:traces reduced soundness to five local obligations on a claim, which
assigns each node and context a set of stores. Together they guarantee that the
claim contains every store an execution in that context reaches at the node
(#isathm("activation_collect_sound")). These sets are usually infinite. An
analyzer, however, computes with finite abstract values, and its solver
(@sec:td) compares, joins, widens, and narrows them without knowing what they
mean. Recall from @sec:abs-int that an abstract value $a$ denotes a set
$conc(a)$. A value of a numeric domain such as Sign or Interval denotes a set
of integers, and an abstract state $d$ denotes a set of stores,
$conc(d) subset.eq (#isatype("var_id") -> ZZ)$. We write $conc$ for both, as
the theories do.

An arbitrary lattice of abstract values is not enough. First, the order must
agree with the meaning. The solver proves only inequalities $a lle b$, while
the obligations of @ch:traces are inclusions between sets. The law
$ a lle b ==> conc(a) subset.eq conc(b) $
turns each such inequality into an inclusion (#isathm("gamma_mono"),
@fig:sign-conc). Second, a value can denote no integer without being the
bottom element, as the interval $ivl(5, 3)$ does. An analyzer that recognizes
only the bottom element as empty stays sound, but it loses precision, because
after the next join the result no longer records that the program point is
dead.

This chapter therefore asks what an abstract domain must provide so that the
analyzer can compute with it, every result contains the stores it stands for,
and the representation itself loses no precision, such as the fact that a
program point is unreachable.

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
  // A parent may carry a qualifier (`name: parent`).
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
      // A pure combination such as warrowing declares
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

A domain is a type $A$ of abstract values, its _carrier_. The solver compares
values, joins them where control flow merges, starts from a least value
$lbot$, and extrapolates with the widening $widen$ and the narrowing $narrow$
of @sec:widening. The analysis also needs a greatest value $ltop$ for unknown
values, an emptiness test, and a concretization $conc : A -> cal(P)(ZZ)$ with
$conc(lbot) = emptyset$ and $conc(ltop) = ZZ$. A _numeric domain_
(#isalocale("numeric_domain")) adds the two requirements of the chapter
opening as laws. The concretization is monotone (#isathm("gamma_mono")), and
the emptiness test holds of a value exactly when its concretization is empty
(#isathm("is_empty_correct")). Isabelle states such an interface as a _type
class_, which collects operations and laws that an instance proves once for a
carrier @haftmann07. Unlike a locale (@sec:contract), a class has at most one
instance for each type.

Intervals (@sec:abs-int) are this chapter's running example
#thy-badge("Voblint_Domain", "Interval_Lattice"). As in Nipkow and Klein
@nipkow14[§13.8.1], bounds are extended integers #isatype("eint"), and
$conc(ivl(l, u)) = setcomp(n in ZZ, l <= n and n <= u)$. On nonempty pairs the
order and join are those of @sec:abs-int. Nipkow and Klein identify all empty
pairs by a quotient type. Voblint's #isatype("ivl") is a plain datatype of
bound pairs, so it must handle them itself. Every pair with $l > u$ is empty,
and so are $ivl(+infinity, +infinity)$ and $ivl(-infinity, -infinity)$. The
bottom value $lbot = ivl(+infinity, -infinity)$ is only one of these, and an
empty pair such as $ivl(5, 3)$ is neither $lbot$ nor below it.

Arithmetic therefore replaces every empty result by $lbot$
(#isaconst("normalize_ivl")). Otherwise $ivl(1, 0) + ivl(1, 1) = ivl(2, 1)$
would keep creating new empty values, and the solver, which tests whether a
value changed (@sec:td), could fail to stabilize. Normalizing never changes the
denoted set (#isathm("normalize_ivl_gamma")). The meet, however, must not
normalize. It intersects the bounds, so $ivl(0, 3) lmeet ivl(5, 9) = ivl(5, 3)$,
the greatest lower bound in the order on pairs. Returning $lbot$ would break
this property, since $ivl(5, 3)$ lies below both operands but not below $lbot$
(#isathm("meet_ivl_normalized_breaks_greatest")). The emptiness test therefore
inspects the bounds (#isaconst("is_bottom_ivl")) instead of comparing with
$lbot$.

The widening is the standard one of @sec:widening
(#isaconst("widen_ivl_core")), except that widening with $lbot$ returns the
other operand. Every nonempty interval exceeds both bounds of
$ivl(+infinity, -infinity)$, so the standard rule would widen
$lbot widen ivl(0, 0)$ to $ltop$. The narrowing (#isaconst("narrow_ivl_td"))
refines only infinite bounds, so $ivl(0, +infinity) narrow ivl(0, 10) = ivl(0, 10)$,
and since each bound leaves infinity at most once, a narrowing sequence is
finite.

== Values at a machine kind #thy-badge("Voblint_Domain", "Kind_Lifted") <sec:domain-kinds>

The domains of @sec:domain-carrier-laws denote sets of mathematical integers
and compute with the arithmetic of $ZZ$. A VIMP variable, however, holds a
value of its machine kind $k$, and every arithmetic node wraps its result into
the kind's range with #isaconst("ik_norm") (@sec:elaboration). The classical
operations are therefore unsound. In the program of @fig:domain-kinds,
interval arithmetic over $ZZ$ bounds $x$ by $ivl(0, +infinity)$ after the
guard, hence $y$ by $ivl(1, +infinity)$, and would prove `y > 0`. At `i32` the
check fails for $x = 2^31 - 1$, where `x + 1` wraps to $-2^31$.

Some facts, however, survive wrapping, and which of them an analysis keeps
depends on the domain. Besides Sign and Interval, two classical domains
express such facts. Parity records whether a value is even or odd, and
Congruence records a residue class $c + m ZZ$, the integers congruent to $c$
modulo $m$ @granger89. For a 32-bit unsigned `n`, the program computes
$a = 4n mod 2^32$ and $b = 3n mod 2^32$. Wrapping subtracts a multiple of
$2^32$. Since $4$ divides $2^32$, $a$ stays a multiple of $4$, and `a != 1`
holds in every run. Since $3$ does not divide $2^32$, $b$ loses its
divisibility by $3$, and $n = 2863311531$ gives $b = 1$. This section asks how
a classical domain is used at machine kinds so that its results describe the
wrapped values and keep the facts that wrapping preserves.

#let _ki(loc) = check-row("dom-kinds-interval", loc: loc)
#let _kc(loc) = check-row("dom-kinds-congruence", loc: loc)
#figure(
  align(center, block(width: 60%, {
    show raw: set text(size: 6.5pt)
    listing(
      lang: "c",
      claim: "dom-kinds-interval",
      ```
      fun main() {
        i32 x;
        u32 n;
        if (x >= 0) {
          i32 y = x + 1;
          __voblint_check(y > 0);
        }
        u32 a = 4 * n;
        u32 b = 3 * n;
        __voblint_check(a != 1);
        __voblint_check(b != 1);
      }
      ```.text,
    )
  })),
  kind: image,
  placement: none,
  caption: [Arithmetic at machine kinds. The first and last checks fail in some
    run, and `a != 1` holds in every run. Interval reports `y > 0`
    #verdict(_ki("6:5").verdict) with #raw(_ki("6:5").state) (claim
    #claim-ref("dom-kinds-interval")). Congruence reports `a != 1`
    #verdict(_kc("10:3").verdict) with #raw(_kc("10:3").state) and `b != 1`
    #verdict(_kc("11:3").verdict) with #raw(_kc("11:3").state) (claim
    #claim-ref("dom-kinds-congruence")).],
) <fig:domain-kinds>

Voblint keeps the classical carriers and attaches the kind outside them. A
value of type #isatype("kd") is #ctor("KBot"), #ctor("KTop"), or a carrier
value $a$ tagged with a kind $k$, and it denotes the integers of $conc(a)$
that $k$ represents:
$
  conc(ctor("KD")(k, a)) = conc(a) inter #isaconst("ik_range") med k, quad
  conc(ctor("KBot")) = emptyset, quad conc(ctor("KTop")) = ZZ.
$
Values of different kinds join to #ctor("KTop"). Goblint likewise
parameterizes every operation of its integer domains by the kind it computes
at.
// TODO: the register records only this; the attribution of the tag itself to
// Goblint's IntDomLifter comes from the Kind_Lifted theory text and needs a
// register row before it is printed.

An operation at kind $k$ computes the classical result and then _normalizes_
it to $k$, the abstract counterpart of wrapping. If $n in conc(a)$, the
wrapped integer $#isaconst("ik_norm") med k med n$ must lie in the
concretization of the normalized value. Wrapping is the identity inside the
range, so only a result that may leave the range needs work.

For an unsigned kind, C prescribes wrapping. For a signed kind, C leaves
overflow undefined, and VIMP wraps (@sec:vimp-vs-c). The signed-overflow
policy (#isatype("signed_overflow_policy")), after Goblint's option
`sem.int.signed_overflow`, chooses how an analysis treats a signed result that
may leave its range. Under the default #ctor("Assume_Top") the result becomes
the kind's top, and under #ctor("Assume_Wraparound") it wraps as an unsigned
result does.
// TODO: cite Goblint's default (assume_top) from src/config/options.schema.json
// at the pinned revision; the register records should_wrap but not the default.
Both choices are sound, because the semantics wraps under either policy and
the kind's top contains the wrapped value. Every soundness theorem therefore
holds for either policy. Goblint's third setting, which assumes that no signed
overflow occurs, has no counterpart, since it would drop values the semantics
produces.

Each domain normalizes according to what its values can express. Interval
keeps a result inside the range. Otherwise, if the kind wraps under the
policy, it wraps a finite interval that is narrower than the modulus $2^w$ and
whose wrapped endpoints stay ordered. Wrapping shifts such an interval as a
whole by one multiple of $2^w$ (#isathm("ik_norm_interval_shift")), so
converting $ivl(260, 265)$ to `u8` gives $ivl(4, 9)$. Every other overflow
gives the kind's whole range. In @fig:domain-kinds, `x + 1` yields
$ivl(1, 2^31)$. Its endpoints wrap to $1$ and $-2^31$, which are out of order,
so the shift rule does not apply and $y$ gets the whole range under both
policies.

Congruence relies on the same shift. Wrapping changes a value by a multiple of
$2^w$, so a class $c + m ZZ$ is preserved modulo $gcd(m, 2^w)$, and a constant
($m = 0$) stays a constant. In @fig:domain-kinds, $4n$ keeps the class $4 ZZ$
since $gcd(4, 2^32) = 4$, while the class $3 ZZ$ of $3n$ becomes $ZZ$ since
$gcd(3, 2^32) = 1$. Under #ctor("Assume_Top") at a signed kind, Congruence
cannot tell whether a sum or product wraps and returns its top. For example,
`a + 1` with $a = 2^31 - 1$ is $-2^31$ under #ctor("Assume_Wraparound") and
$top$ under #ctor("Assume_Top")
(#fixture("27-signed-overflow/precision/02-congruence_wraparound.vimp", label: "02-congruence_wraparound")
and its #fixture("27-signed-overflow/known-imprecision/02-congruence_assume_top.vimp", label: "assume_top twin")).

Sign carries no magnitude, so it rules out a wrap only where the operand signs
do, as described below. Every other nonzero sign normalizes to the kind's top,
#signval($top$) at a signed kind and #signval("≥0") at an unsigned one, and
zero keeps its sign. Parity, in contrast, computes classically at every kind
and under both policies, because wrapping subtracts a multiple of an even modulus, which preserves parity
(#isathm("even_ik_norm_iff")).

The domain interface states these requirements as one law per primitive,
quantified over the policy $p$. For arithmetic it reads
(#isathm("arith_ik_sound"))
$
  m in conc(a) and n in conc(b) ==>
  #isaconst("ik_norm") med k med (#isaconst("aop_eval") med italic("op") med m med n)
  in conc(#isaconst("arith_ik") med p med k med italic("op") med a med b),
$
where the theory passes one more argument, a flag stating that both operands
lie in $k$'s range. A carrier value denotes mathematical integers, so the law
alone admits operands beyond the range, such as $2^40$ at `i32`. The evaluator
sets the flag when both operand expressions have kind $k$, since every value of
kind $k$ lies in its range. Under the flag, some operations cannot leave the
range. At a signed kind, a sum of operands with opposite signs lies between
them, a product with a zero operand is zero, and a remainder is no larger in
magnitude than its operands, so Sign keeps the classical sign of these
operations. Congruence keeps the classical class of a remainder and of a
quotient whose divisor excludes $-1$ at every kind. The law does not require a result to lie
in the range, since the tag adds that restriction.

Two carrier operations also depend on the kind. The emptiness test must
recognize a value whose integers all lie outside the kind, such as the sign
#signval("−") at `u8`, and the interval widening needs the kind's limits. The
class #isalocale("ik_domain") therefore asks each carrier for a widening, a
narrowing and an emptiness test at a kind, with the laws of their kind-free
counterparts, and the tagged value applies them at the kind of its operands.
The interval widening at a kind moves a growing bound to the kind's limit
instead of to infinity, or to the new bound if that already lies beyond the
limit, and the narrowing replaces only a bound that sits at that limit. In a
loop that starts at $v = 1$ and adds $2$ while $v < 51$, the loop head widens
the upper bound of $v$ to the limit of `i32`, and narrowing then lowers it to
$52$, as the state at the check `v <= 52` in the loop body shows (claim
#claim-ref("dom-stride2-interval")). The kind-free narrowing refines only
infinite bounds and would keep the limit. On intervals inside the range, each
bound grows at most once under widening and leaves the limit at most once
under narrowing. This argument bounds the widening and narrowing sequences of
one value. It is not a lemma of the theories, and it does not make the solver
terminate. Sign, Parity and Congruence widen by the join and narrow by the
meet at every kind.

Wrapping loses precision that the classical domains would keep. In
@fig:domain-kinds no domain avoids the loss, because $b$ takes every `u32`
value, since $3$ is invertible modulo $2^32$, and $y$ takes both $1$ and
$-2^31$, so only the top describes these values. Elsewhere the loss comes from
the domain or the policy. Sign loses the sign of a sum whenever both operands
may be positive, even where the program keeps its values small
(#fixture("07-sign-precision/known-imprecision/01-sign_cannot_bound_magnitude.vimp", label: "01-sign_cannot_bound_magnitude")).
Under #ctor("Assume_Top"), Congruence alone loses the class of every signed sum
and product, including those that cannot wrap, because its values do not bound
magnitudes. Domains can, however, be combined so that they refine each other,
and then the bounds of one component tell another that no value wraps.

== From values to stores <sec:domain-states>

A numeric domain describes the possible values of one variable. The
obligations of @ch:traces, however, concern sets of stores
$#isatype("store") = #isatype("var_id") -> ZZ$. This thesis uses two forms of
abstract state. A _non-relational_ state gives each variable its own abstract
value and admits a store if each variable's value lies in its own abstract
value. A _relational_ state records constraints between variables, such as
$x <= y$, and admits a store if the store satisfies them. Neither is stronger than the other. For the stores with
$0 <= x <= y <= 5$ (@fig:rel-vs-nonrel), the best non-relational state over
intervals, ${x |-> ivl(0, 5), y |-> ivl(0, 5)}$, misses $x <= y$ and admits
$x = 5, y = 0$. The relational fact $x <= y$ bounds neither variable and admits
$x = y = -7$. Together they describe the set exactly.

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

An _abstract state_ is a type $D$ with the order and join the solver needs
and a monotone concretization that maps each state $d$ to the set $conc(d)$ of
stores it describes. Isabelle overloads one constant, #isaconst("gamma_S"),
written $conc(d)$, for every kind of state.

=== A non-relational state #thy-badge("Voblint_Domain", "Nonrelational_State") <sec:nonrel-state>

A non-relational state (#isatype("gabs_state")) maps every variable $x$ to an
abstract value $d(x)$. It admits a store if every variable's value lies in the
concretization of its abstract value,
$conc(d) = setcomp(s, forall x. s(x) in conc(d(x)))$ (#isaconst("gamma_state")).
Order and join work variable by variable, as for any function type in HOL
(@fig:pointwise), so this concretization is monotone too. The non-relational
analyses use kind-tagged values (@sec:domain-kinds), and their concretization
also requires every variable to hold a value of its own kind
(#isaconst("in_kinds")).

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

Some program points are reached by no execution, and the analysis should
recognize them from their state. Each layer has its own least element. A
domain has $lbot$, which for intervals is one empty value among several
(@sec:domain-carrier-laws), the tagged values have #ctor("KBot"), and the
pointwise order has the _bottom state_, which maps every variable to the least
value. For pointwise states, recognizing unreachability is difficult,
because every state with one empty variable describes no store, and only one
of them is the bottom state (@fig:pointwise). Treating only the bottom state
as unreachable misses most cases, since a branch condition usually empties a
single variable, as in ${x |-> signval(bot), y |-> signval(top)}$. Treating
every empty state as unreachable is correct at the moment of the test, but a
later join of two differently empty states can give a nonempty one
(@fig:domain-reachability). This is sound, since it only adds stores, but it
loses the fact that the point is unreachable.

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
        i32 x = __voblint_nondet_int();
        i32 y = __voblint_nondet_int();
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
    turns each empty arm into the bottom state before the join, and the
    analyzer reports the check in the branch as unreachable (claim
    #claim-ref("dom-disjunct-sign")).],
) <fig:domain-reachability>

Voblint therefore makes unreachability a value of its own, as Nipkow and
Klein do with an option type @nipkow14[§13.7]. Goblint likewise lifts the local
state by an outer bottom element for dead code
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L120-L135")[`Analyses.Dom`]),
and a transfer that finds its path unreachable raises the `Deadcode` exception.
A lifted state (#isatype("lifted")) is either #ctor("Bot"), meaning
unreachable, with $conc(ctor("Bot")) = emptyset$, or $ctor("Lifted")(d)$ for
an ordinary state $d$. After every transfer, the analysis replaces an empty
result by #ctor("Bot") (#isaconst("normalize_lift")). The test relies on the
exact emptiness test of the domain, since a pointwise state is empty exactly
when some variable's value is (#isathm("is_empty_state_iff_gamma_state_empty")).
The replacement only exchanges one representation of the empty set for another
(#isathm("gamma_exec_normalize_lift")), so it cannot make the analysis
unsound.

Once a state is #ctor("Bot"), it stays #ctor("Bot"), because transfers skip it
and a join with #ctor("Bot") returns the other operand. The bottom state and
#ctor("Bot") differ in role. The bottom state is one ordinary pointwise
state among the empty ones, while #ctor("Bot") is the single value that marks
a point as unreachable. In @fig:domain-reachability, both arms are joined
inside one branch transfer, so the test after the transfer comes too late, and
@sec:branches shows how the branch avoids this.

=== A relational state #thy-badge("Voblint_Analysis_Order", "Order_Analysis") <sec:rel-state>

A relational state records relations that the pointwise form cannot
express, so its concretization maps a whole state to a set of stores. The type
#isatype("order_rel") records a set $P$ of variable pairs, where $(x, y)$
stands for the constraint $x <= y$, and a flag $t$ stating that the store lies
in the set $K$ of stores in which every variable holds a value of its kind
(#isaconst("in_kinds")). The concretization is #isaconst("gamma_ord"):
$
  conc(ctor("OFacts")(t, P)) = setcomp(s, (t --> s in K) and forall (x, y) in P. s(x) <= s(y)),
  quad conc(ctor("OBot")) = emptyset.
$
The flag lets assignments record more pairs. If every variable holds a value of
its kind, a copy `x = y` between two variables of one kind stores the value
unchanged, so the analysis may record both $x <= y$ and $y <= x$. The initial state sets the
flag, since every initial store lies in $K$. The top value leaves it unset,
because it must describe every store. Below, the pair $(x, y)$ is written
$x <= y$, and a value is written as its set of pairs when the flag does not
matter.

More pairs describe fewer stores, so the order is reverse inclusion
(#isaconst("less_eq_order_rel")), with #ctor("OBot") at the bottom and
$ltop = ctor("OFacts")("False", emptyset)$, which constrains nothing. The join
keeps the pairs both operands share,
$ctor("OFacts")(t, P) ljoin ctor("OFacts")(u, Q) = ctor("OFacts")(t and u, P inter Q)$
(#isaconst("sup_order_rel")). The widening is the join. The solver's widening
contract (#isalocale("widening")) asks only for a value above both operands,
which alone does not force termination, but here an ascending chain can only
drop pairs from a finite set. The narrowing returns the newly computed value,
which the narrowing law accepts since it lies between the two operands.

The carrier does not close its pairs under transitivity (@fig:rel-state). The
values ${x <= y, y <= z}$ and ${x <= y, y <= z, x <= z}$ therefore denote the
same stores but are different values, and the join of ${x <= y, y <= z}$ and
${x <= y, x <= z}$ is ${x <= y}$, although both operands imply $x <= z$. Pairs
enter only at guards and assignments and relate two of the program's
variables, so $P$ is finite in every value the analysis constructs. The
executable analyzer relies on this to store $P$ as a list.

#let _rnode(pos, name, body) = node(pos, text(size: 7pt, body), name: name, inset: 3pt)
#figure(
  diagram(
    spacing: (5mm, 6mm),
    _rnode((1.5, 0), <r-top>, $ltop = emptyset$),
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
    _rnode((1.5, 6.4), <r-bot>, ctor("OBot")),
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
  caption: [The relational states over the variables $x$, $y$, and $z$ with the
    flag unset, ordered bottom to top by reverse inclusion. Each
    #ctor("OFacts") value is drawn as its set of pairs. The upper part shows all values built from
    $x <= y$, $y <= z$ and $x <= z$. Values with other pairs, such as $y <= x$, are
    drawn only below the lowest of these, and the dots stand for the rest.
    Nine pairs exist, including $x <= x$, so the values are finitely many, and
    the lowest #ctor("OFacts") value holds all nine and denotes the stores with
    $x = y = z$.],
) <fig:rel-state>

The store that maps every variable to $0$ satisfies every pair, and $0$ lies
in the range of every kind. Every $ctor("OFacts")(t, P)$ therefore denotes at
least one store, and only #ctor("OBot") denotes the empty set. Unlike the
pointwise form, the carrier has a single representation of unreachability.

A relational state stores no value per variable, so it cannot evaluate an
expression to an abstract value. Its transfers update the constraints
directly. An assignment `x = e` first forgets every pair that mentions $x$ and
then adds the pairs the new value implies. A copy `x = y` within one kind adds
$x <= y$ and $y <= x$ when the flag is set, and $x$ inherits the pairs of $y$.
Further pairs $x <= y$ or $y <= x$ come from asking other analyses how the new
value compares with $y$ (@sec:coop-mcp). A guard
comparing two variables adds the pairs its outcome implies (@sec:branches). The type
instantiates the solver's classes, but it is not a numeric domain, so the
operations on single values that follow serve only non-relational states.

== Evaluating expressions #thy-badge("Voblint_Nonrelational", "Nonrelational_Domain") <sec:domain-forward>

The carrier operations serve the solver. The analysis also needs operations
that mirror the program's arithmetic, comparisons, and branch conditions. We
call them the domain's _primitives_.

An assignment `x = e` needs the abstract value of $e$. Forward evaluation
computes it from an abstract state $d$, as in the generic abstract interpreter
of Nipkow and Klein @nipkow14[§13.5.3], and its result must contain every
concrete result:
$ s in conc(d) ==> #isaconst("eval", thy: "Core_Exp") med e med s in conc(asem(e) med d). $
Voblint defines this evaluation once for every domain, using each operation at
its machine kind (@sec:domain-kinds), and proves the law once
(#isathm("aeval_sound")). The evaluation may also ask other analyses for the
value of a subexpression, and the law then assumes that their answers are true.
@sec:coop-channels makes this premise precise. If $d(x) = ivl(0, 9)$ at a 32-bit kind, for example, Interval
evaluates `x + 1` to $ivl(1, 10)$.

A condition is an expression too, and VIMP reads a nonzero value as true. If
the abstract value of a condition admits only one truth value, a branch can
drop the arm that needs the other. Voblint therefore derives a truth test from
the domain's comparison with zero. It answers $"Some"(b)$ if every integer in
$conc(a)$ has truth value $b$, and $"None"$ otherwise
(#isathm("truth_ik_sound")). For Interval, $ivl(1, 5)$ is true, $ivl(0, 0)$ is
false, and $ivl(0, 5)$ is undecided.

== Answering queries <sec:queries>

An assertion `__voblint_check(b)` asks whether $b$ holds in every store that
reaches its program point, and the analysis must answer from the abstract state
there. Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/assert.ml",
)[`assert`]
analysis asks the active analyses a query about the truth value of $b$, and
Voblint's combined analyzer does the same (@sec:coop-mcp). This section shows
how a non-relational domain decides $b$, which is the answer it contributes.

A domain answers two comparisons on abstract values, $"less"(a, b)$ for
$a < b$ and $"eq"(a, b)$ for $a = b$. A definite answer must hold for every
pair of integers the two values denote, and $"None"$, meaning unknown, is
always allowed (#isathm("cop_of_sound")):
$
  "less"(a, b) = "Some"(r) and i in conc(a) and j in conc(b) ==> (i < j) = r,
$
and likewise for $"eq"$. Interval decides $a < b$ when one interval lies
entirely below the other, where a shared endpoint suffices for the answer
false, and $a = b$ when the intervals are disjoint or the same single integer.
Sign decides $a < b$ whenever the signs separate the values. Parity only
refutes equality between an even and an odd value. Congruence decides $<$ only
for single integers and refutes equality when two residue classes are
disjoint.

A check evaluates its condition $b$ on an abstract state to _true_, _false_
or _unknown_. Each comparison in $b$ evaluates
its operands to abstract values $hat(a)$ and $hat(b)$ (@sec:domain-forward)
and asks one of the two comparisons, with the operands swapped or the answer
negated where needed:
$
  a < b & ~> "less"(hat(a), hat(b)), & quad a > b & ~> "less"(hat(b), hat(a)), & quad
  a == b & ~> "eq"(hat(a), hat(b)), \
  a <= b & ~> not "less"(hat(b), hat(a)), & quad a >= b & ~> not "less"(hat(a), hat(b)), & quad
  a != b & ~> not "eq"(hat(a), hat(b)).
$
Negation keeps _unknown_, and the connectives `!`, `&&` and `||` combine the
answers of their operands in three-valued logic, so a definite _false_ decides
`&&` and a definite _true_ decides `||`. Any other expression $e$ is read as
$e != 0$. A new domain therefore gets checks on arbitrary conditions by
providing the two comparisons. Their soundness is proved once for every domain
(#isathm("nonrel_classify_sound")). The answer _true_ certifies that $b$ holds
in every store the state describes, _false_ that it holds in none, and
_unknown_ makes no claim. In Sign, with $x$ non-positive and $y$ positive,
`x <= y && y != 0` is answered from $"less"(hat(y), hat(x))$ and
$"eq"(hat(y), hat(0))$ alone (@fig:query-tree). A non-relational analysis that
runs alone decides its checks this way (#isaconst("nonrel_classify")). In the
combined analyzer, its query handler answers the question about $b$ with the
same evaluation, converted to the shared answer type of @sec:coop-queries.

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
  caption: [How forward evaluation answers a compound condition, in Sign
    with #raw(_q.state) (claim #claim-ref("dom-query-tree-sign")). Each comparison becomes
    one of the domain's two comparisons (blue), as $~>$ marks; the answer follows
    the colon. Negation flips a definite answer,
    and `&&` is true because both operands are, so the check is
    #_q.verdict.],
) <fig:query-tree>

Both operands of a connective are evaluated in the same state, so for $x$ in
$ivl(1, 2)$, `x == 1 || x == 2` stays unknown, although every store satisfies
it (claim #claim-ref("dom-disjunction-one-state")). Goblint is more precise
here. CIL compiles `&&` and `||` into branches
(#link("https://github.com/goblint/cil/blob/d97418f2e8d2aa88a36c22397c38ccf4d3ffbcde/src/frontc/cabs2cil.ml#L5220-L5255")[`cabs2cil.ml`]),
and where `x == 1` fails, Goblint's interval refinement narrows $ivl(1, 2)$ to
$ivl(2, 2)$
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/baseInvariant.ml#L395-L410")[`baseInvariant.ml`],
@saan26phd[§4.5.1, Rem. 8]). Voblint's interval refinement of a failed
equality would also exclude the endpoint, but Voblint evaluates a check in one
state and refines only at a guard.

== Learning from a guard #thy-badge("Voblint_Nonrelational", "Nonrelational_Transfer") <sec:branches>

When the analysis enters a branch, it knows whether the condition held. On
the true arm of `if (0 < x)`, for example, $x$ is positive. Ignoring this is
sound, since the state before the branch contains every store that takes
either arm, but it costs precision, as the following program shows.

#let _g = claim-row("dom-guard-interval", "12:3")
#align(center, block(width: 60%, {
  show raw: set text(size: 6.5pt)
  listing(
    lang: "c",
    claim: "dom-guard-interval",
    ```
    i32 x = __voblint_nondet_int();
    if (x < -1000 || x > 1000) {
      x = 0;
    }
    i32 y;
    if (0 < x) {
      y = x;
    } else {
      y = - x;
    }
    __voblint_check(y >= 0);
    ```.text,
  )
}))

The first branch keeps $x$ between $-1000$ and $1000$. In this range `- x`
cannot wrap, so $y$ ends up as $|x|$ and the check always holds. Without the
bound it could fail, since at $x = -2^31$, `- x` wraps to $-2^31$. Without
refinement, however, the analysis learns nothing from either condition, $x$
and $y$ keep the top value of their kind, and the check stays unknown.
Backward refinement runs the condition in reverse, as in the backward abstract
interpretation of tests by Cousot @cousot99[§§8.5, 10.1] and the backward
analysis of Nipkow and Klein @nipkow14[§13.7]. Given abstract operands
$a_1, a_2$ of a comparison that must hold, the domain returns refined operands
$a'_1, a'_2$ that keep every concrete pair satisfying it. For $<$:
$
  n_1 in conc(a_1) and n_2 in conc(a_2) and n_1 < n_2
  ==> n_1 in conc(a'_1) and n_2 in conc(a'_2),
$
and likewise for the other comparison operators (#isathm("refine_ik_sound")).
An operand that is a sum or a difference passes the refinement on to its own
operands by inverting the operation, over the mathematical integers when it
cannot overflow and otherwise at its kind under the overflow policy.

The refined operand is then combined with the value known before. Nipkow and
Klein use the lattice meet and require it to be exact on the denoted sets.
Voblint asks only for an intersection that keeps every integer both operands
share (#isathm("meet_ik_sound")), for Interval the meet of
@sec:domain-carrier-laws. In the program above, $x$ starts at
$ivl(-2^31, 2^31 - 1)$. The false arm of the first condition refines it to
$ivl(-1000, 1000)$, and joining the true arm's $0$ keeps that interval. The
second condition refines $x$ to $ivl(1, 1000)$ on its true arm and to
$ivl(-1000, 0)$ on its false arm, each arm bounds $y$ from the refined $x$,
and the join yields #raw(_g.state).

The guard refinement applies the comparison refinements along the Boolean
structure of the condition, in the manner of the backward filter of Nipkow and
Klein @nipkow14[§13.7.1]. It never removes a store at which the guard has the
required truth value, provided the answers of other analyses are true, the
same premise as for evaluation (@sec:domain-forward)
(#isathm("nonrel_refine_sound")). This is exactly what the branch needs. A
conjunction is refined from left to right, each conjunct once and without
iterating to a local fixpoint, so the bounds can depend on the order of the
conjuncts. With Interval, `0 < i && i < j && j < 10` bounds $j$ to $ivl(2, 9)$
but $i$ only from below, and the reversed order bounds $i$ to $ivl(1, 8)$ but
$j$ only from above (claim #claim-ref("dom-conjunct-order")). The refinements
are sound but not the most precise possible. A quotient, for instance, stops
the refinement, so Interval cannot learn $y <= 9$ from `y / 2 < 5`, although it
holds in every run.

The branch transfer first drops an arm that the truth test rules out and
otherwise applies the refinement. It inherits the refinement's soundness
(#isathm("nonrel_branch_sound")). A disjunction needs one more step, because
its arms are joined inside the transfer, before the test after the transfer
can mark them unreachable (@fig:domain-reachability). The refinement therefore
replaces each comparison that empties one of its variables by the bottom state.
An arm that is a conjunction of comparisons and contains such a comparison then
adds nothing to the join, and the test after the transfer
turns a joined bottom state into #ctor("Bot") (@sec:nonrel-state). A guard refines a
relational state as well. On the true arm of `if (x < y)`, the state of
@sec:rel-state adds the pair $x <= y$, losing the strictness, which is sound
but less precise, and this refinement satisfies the same statement
(#isathm("ord_branch_sound")).

== The complete domain interface #thy-badge("Voblint_Nonrelational", "Nonrelational_Transfer") <sec:domain-contract>

The operations of this chapter fall into two groups. The _carrier operations_
serve the solver. They are the order, join, bottom and top, widening,
narrowing and emptiness test of @sec:domain-carrier-laws, together with their
versions at a kind (@sec:domain-kinds). The _primitives_ mirror the program's
operations at a machine kind. They are the constants and arithmetic of forward
evaluation (@sec:domain-forward), the comparisons (@sec:queries), and the
comparison refinements and the intersection (@sec:branches). Every
non-relational domain supplies both groups as an instance of the class
#isalocale("kind_int_domain"), whose laws are the soundness conditions of this
chapter (@fig:domain-carrier).

The class contains no transfer function, because the primitives determine
every edge. An assignment overwrites the variable with the abstract value of
the right-hand side, converted to the variable's kind, and a branch applies the
refinement of @sec:branches. Procedure entry evaluates the arguments in the
caller's state, binds them to the formal parameters, and sets every other
local of the callee to #ctor("KTop"). These transfers are defined and proved
sound once for every instance (#isathm("nonrel_spec_sound")), so a new
non-relational domain supplies values and primitives only.

#figure(
  domain-tree("carrier"),
  kind: image,
  placement: top,
  caption: [What a non-relational domain supplies over its carrier type
    #raw("'a"), down to the class #isalocale("kind_int_domain") an analysis
    instantiates. Each class lists the operations and laws it declares, which
    the classes below it inherit. Arrows point to what a class extends. A class
    that carriers instantiate has a heavier border and lists its instances.
    Rows the text does not discuss: #isalocale("warrowing") combines widening
    and narrowing in one update (@sec:widening), #isaconst("to_string") prints a
    value, #isaconst("cast_ik") converts a value to another kind,
    #isaconst("raw_aop_ik") computes over $ZZ$ for the backward step of
    @sec:branches, #isaconst("fits_ik") tests that a value lies in a kind's
    range, and #isaconst("answer_ik") and #isaconst("of_answer_ik") convert to
    and from the answers of @sec:coop-queries, whose record type
    #isatype("int_dom") instantiates the domain as well. #isatype("int_tuple") is the reduced product of
    @sec:reduced-product.
    Color gives where a node is declared: #swatch(vb.hol) HOL,
    #swatch(vb.solver) the vendored solver, #swatch(vb.voblint) Voblint.],
) <fig:domain-carrier>

== A carrier the interface excludes <sec:no-defexc>

Voblint cannot host every domain Goblint offers. The verified solver requires
its values to form a #isalocale("bounded_semilattice_sup_bot")
(#isalocale("TD_side_upd_rule")), whose join is a _least_ upper bound
(#isalocale("semilattice_sup")), and the generic framework inherits the
requirement. It excludes every carrier in which two values have upper bounds
but no least one.

Goblint's exclusion-set domain
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/cdomain/value/cdomains/int/defExcDomain.ml",
)[`DefExc`]
becomes such a carrier in Voblint's setting. In Goblint, an exclusion value
also stores a _bit range_ $r$, which bounds the integers it denotes to those of
a given bit width, such as the range of its kind. A Voblint carrier denotes
mathematical integers, and the kind's range is attached outside it
(@sec:domain-kinds), so the carrier must drop $r$. A non-bottom value is then `Definite n`, denoting
${n}$, or `Excluded S` for a finite set $S$, denoting $ZZ without S$
(@fig:defexc). `Definite 1` and `Definite 2` have no least upper bound. Every
`Excluded {p}` with $p in.not {1, 2}$ lies above both, so by monotonicity of
$conc$ a least upper bound $u$ would satisfy
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
  placement: auto,
  caption: [Goblint's exclusion sets without a bit range, ordered bottom to
    top: `Definite n` denotes ${n}$ and `Excluded S` denotes $ZZ without S$.
    Every `Excluded S` with $1, 2 in.not S$ lies above `Definite 1` and
    `Definite 2`. The blue chain of such upper bounds descends forever, and
    each of its elements lies above both values (dotted). A least upper bound
    would denote ${1, 2}$ (dashed), which no value does. Illustrative, not
    machine-checked.],
) <fig:defexc>

Goblint's bit range avoids this argument. Goblint writes a non-bottom value
with a range as `Excluded (S, r)`, denoting the integers $r$ admits minus $S$.
If $R$ is that set of integers, then `Excluded (S, r)` with
$S = R without {1, 2}$ denotes exactly ${1, 2}$, although the
join of two distinct `Definite` values returns `Excluded ({0}, r)` instead, or
excludes nothing if one of them is $0$. Voblint could admit this carrier only
by carrying the range inside the carrier value, or by weakening
#isalocale("semilattice_sup") to an upper-bound law throughout the solver and
the framework.

The laws of the domain interface make every operation keep the stores its
inputs admit, but each concerns a single value or state. @ch:analysis-interface
states what an analysis must prove about the edges and calls along which a
program moves its state.
