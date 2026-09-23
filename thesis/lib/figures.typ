#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/cetz:0.5.2"
#import "@preview/commute:0.3.0" as commute
#import "@preview/subpar:0.2.2"
#import "theme.typ": vb
#import "code.typ": listing

// Reusable figure vocabulary. Same principle as the LaTeX style file: a CFG
// node looks the same everywhere, and restyling all of them is one edit.

// ---------------------------------------------------------- trust status ---
#let _status = (
  proved: (vb.proved, vb.proved.lighten(88%)),
  trusted: (vb.trusted, vb.trusted.lighten(86%)),
  unproved: (vb.unproved, vb.unproved.lighten(90%)),
)

#let stage(pos, body, kind: "proved", ..args) = {
  let (line, fill) = _status.at(kind)
  node(
    pos,
    align(center, body),
    stroke: 0.9pt + line,
    fill: fill,
    corner-radius: 3pt,
    inset: 7pt,
    ..args,
  )
}

#let flow(from, to, label: none, ..args) = edge(
  from,
  to,
  "->",
  stroke: 0.8pt + vb.neutral,
  label: if label != none {
    text(size: 0.62em, font: "DejaVu Sans Mono", fill: vb.proved, label)
  },
  ..args,
)

#let badge(body, color) = box(
  inset: (x: 3pt, y: 1pt),
  radius: 2pt,
  fill: color.lighten(88%),
  stroke: 0.6pt + color,
  text(size: 0.7em, fill: color, body),
)
#let proved-badge = badge([proved], vb.proved)
#let trusted-badge = badge([trusted], vb.trusted)
#let unproved-badge = badge([unverified], vb.unproved)

// ------------------------------------------------------------- CFG nodes ---
#let ppoint(pos, body, ..args) = node(
  pos,
  body,
  shape: circle,
  stroke: 0.9pt + vb.neutral,
  fill: white,
  inset: 4pt,
  ..args,
)

#let entry-node(pos, body, ..args) = node(
  pos,
  body,
  stroke: 0.9pt + vb.accent,
  fill: vb.accent.lighten(90%),
  corner-radius: 2pt,
  inset: 5pt,
  ..args,
)

#let result-node = entry-node

#let intra-edge(from, to, label: none, ..args) = edge(
  from,
  to,
  "->",
  stroke: 0.9pt + vb.neutral,
  label: if label != none { text(size: 0.62em, font: "DejaVu Sans Mono", label) },
  ..args,
)

#let call-edge(from, to, label: none, ..args) = edge(
  from,
  to,
  "-->",
  stroke: (paint: vb.accent, thickness: 0.9pt, dash: "dashed"),
  label: if label != none {
    text(size: 0.62em, font: "DejaVu Sans Mono", fill: vb.accent, label)
  },
  ..args,
)

// ---------------------------------------------------------- solver state ---
#let unk(pos, body, state: "stable", ..args) = {
  let (line, fill) = if state == "stable" {
    (vb.stable, vb.stable.lighten(85%))
  } else if state == "unstable" {
    (vb.unstable, vb.unstable.lighten(80%))
  } else if state == "called" {
    (vb.called, vb.called.lighten(90%))
  } else {
    (vb.muted, white)
  }
  node(pos, body, shape: circle, stroke: 1pt + line, fill: fill, inset: 4pt, ..args)
}

#let global-unk(pos, body, ..args) = node(
  pos,
  body,
  stroke: 0.9pt + vb.neutral,
  fill: vb.muted.lighten(85%),
  inset: 5pt,
  ..args,
)

#let dep-edge(from, to, ..args) = edge(from, to, "->", stroke: 0.7pt + vb.muted, ..args)

// A side effect is drawn double-tipped; a withdrawn contribution is dashed.
#let side-edge(from, to, ..args) = edge(from, to, "->>", stroke: 1pt + vb.called, ..args)
#let withdrawn-edge(from, to, ..args) = edge(
  from,
  to,
  "-->",
  stroke: (paint: vb.called.lighten(35%), thickness: 1pt, dash: "dashed"),
  ..args,
)

// -------------------------------------------------------- locale diagram ---
#let locale-node(pos, name, ..args) = node(
  pos,
  raw(name),
  stroke: 0.9pt + vb.neutral,
  fill: white,
  corner-radius: 2pt,
  inset: 5pt,
  ..args,
)

#let instance-node(pos, name, ..args) = node(
  pos,
  raw(name),
  stroke: 0.9pt + vb.accent,
  fill: vb.accent.lighten(90%),
  corner-radius: 2pt,
  inset: 5pt,
  ..args,
)

#let import-edge(from, to, ..args) = edge(from, to, "->", stroke: 0.9pt + vb.neutral, ..args)
#let sublocale-edge(from, to, ..args) = edge(
  from,
  to,
  "-->",
  stroke: (paint: vb.accent, thickness: 0.9pt, dash: "dashed"),
  ..args,
)
#let interp-edge(from, to, ..args) = edge(
  from,
  to,
  "->",
  stroke: (paint: vb.proved, thickness: 0.9pt, dash: "dotted"),
  ..args,
)

// ------------------------------------------------------------- lattices ----
// A Hasse diagram from a node table and a cover relation.
#let hasse(nodes, covers, spacing: (11mm, 8mm)) = diagram(
  spacing: spacing,
  node-inset: 3pt,
  ..nodes.map(((pos, label)) => node(pos, label)),
  ..covers.map(((a, b)) => edge(a, b, "-", stroke: 0.8pt + vb.neutral)),
)

// --------------------------------------------------------- boxed display ---
// The dominant figure kind in this literature: a framed block of equations.
#let rhsbox(body) = block(
  width: 100%,
  fill: vb.bg,
  stroke: 0.7pt + vb.frame,
  radius: 3pt,
  inset: 10pt,
  {
    // Equations inside a figure box are referred to by the figure number.
    set math.equation(numbering: none)
    body
  },
)

// ---------------------------------------------- fixpoint iteration plot ----
// After Concrete Semantics Fig. 13.11: the iteration drawn against `f x` and
// `x`, so the picture shows *why* widening terminates rather than only that a
// bound jumped. Three traces share one pair of axes: plain iteration climbing
// to the fixpoint, widening jumping past it, narrowing descending back.
#let iteration-plot(
  f: x => 0.55 * x + 2.2, // the monotone function being iterated
  start: 0.4,
  steps: 5,
  widen-to: 7.4,
  narrow-steps: 3,
  size: (7.4, 5.0),
) = cetz.canvas({
  import cetz.draw: *
  let (w, h) = size
  let sx = x => x / 9 * w
  let sy = y => y / 9 * h

  // axes
  line((0, 0), (w + 0.3, 0), mark: (end: "straight"), stroke: 0.8pt + vb.neutral)
  line((0, 0), (0, h + 0.3), mark: (end: "straight"), stroke: 0.8pt + vb.neutral)
  content((w + 0.35, -0.05), anchor: "west", text(0.85em)[$x$])
  content((-0.05, h + 0.35), anchor: "south", text(0.85em)[$f x$])

  // identity, then f
  line((0, 0), (w, h), stroke: (paint: vb.muted, dash: "dashed", thickness: 0.7pt))
  let pts = range(0, 46).map(i => {
    let x = i / 45 * 9
    (sx(x), sy(f(x)))
  })
  line(..pts, stroke: 1pt + vb.neutral)

  // plain iteration: the staircase up to the fixpoint
  let x = start
  for _ in range(steps) {
    let y = f(x)
    line((sx(x), sy(x)), (sx(x), sy(y)), stroke: 0.9pt + vb.accent)
    line((sx(x), sy(y)), (sx(y), sy(y)), stroke: 0.9pt + vb.accent)
    x = y
  }

  // widening: one jump past the fixpoint
  line((sx(x), sy(x)), (sx(x), sy(widen-to)), stroke: (paint: vb.unstable, thickness: 1.2pt))
  line(
    (sx(x), sy(widen-to)),
    (sx(widen-to), sy(widen-to)),
    mark: (end: "straight"),
    stroke: (paint: vb.unstable, thickness: 1.2pt),
  )

  // narrowing: descending back toward the fixpoint
  let d = widen-to
  for _ in range(narrow-steps) {
    let y = calc.max(f(d), f(d))
    line((sx(d), sy(d)), (sx(d), sy(y)), stroke: (paint: vb.proved, thickness: 1pt, dash: "dotted"))
    line((sx(d), sy(y)), (sx(y), sy(y)), stroke: (paint: vb.proved, thickness: 1pt, dash: "dotted"))
    d = y
  }
})

// ------------------------------------------------- simulation diagram ------
// After Concrete Semantics Fig. 8.4 / 10.8: a lemma drawn rather than stated.
// Two levels related by a vertical relation; the claim is that the square
// commutes. Drawing both directions of an iff is two of these side by side.
// `commute` is used rather than a hand-built square: it is purpose-made for
// this shape and places arrow tips and labels without coaxing.
#let simulation(
  top-left: [],
  top-right: [],
  bottom-left: [],
  bottom-right: [],
  top-label: [],
  bottom-label: [],
  left-label: [],
  right-label: [],
  dashed-bottom: false,
) = commute.commutative-diagram(
  commute.node((0, 0), top-left),
  commute.node((0, 1), top-right),
  commute.node((1, 0), bottom-left),
  commute.node((1, 1), bottom-right),
  commute.arr((0, 0), (0, 1), top-label),
  ..(
    if dashed-bottom {
      (commute.arr((1, 0), (1, 1), bottom-label, "dashed"),)
    } else {
      (commute.arr((1, 0), (1, 1), bottom-label),)
    }
  ),
  commute.arr((0, 0), (1, 0), left-label),
  commute.arr((0, 1), (1, 1), right-label),
)

// -------------------------------------------- annotations as tuples --------
// After Concrete Semantics Fig. 13.8: the abstract state laid out as
// annotation points by variables, which is what a termination measure sums
// over. Makes "one abstract value per variable per program point" concrete.
#let annotation-grid(points, vars, values) = table(
  columns: vars.len() + 1,
  align: center + horizon,
  stroke: (x, y) => (
    left: if x == 1 { 0.7pt + vb.neutral } else { 0.4pt + vb.frame },
    top: if y == 1 { 0.7pt + vb.neutral } else { 0.4pt + vb.frame },
  ),
  inset: 6pt,
  [], ..vars.map(v => text(fill: vb.neutral, style: "italic", v)),
  ..points
    .enumerate()
    .map(((i, p)) => (
      text(fill: vb.accent, p),
      ..vars.enumerate().map(((j, _)) => values.at(i).at(j)),
    ))
    .flatten(),
)

// ------------------------------------------------------------ algorithms ---
// `algorithm2e` sets a rule, then "Algorithm N: <caption>", then the body.
// Typst has no algorithm float, so this builds one: its own counter and
// supplement so it is not numbered among the figures, the caption above the
// body, and full measure rather than shrink-to-fit -- an algorithm that is
// narrower than the text column reads as an afterthought. lovelace sizes its
// grid to content, so the body must end with an #h(1fr) on the last line for
// the rules to reach the full measure.
#let algorithm(body, caption: none, label-name: none) = {
  let fig = figure(
    kind: "algorithm",
    supplement: [Algorithm],
    caption: caption,
    placement: none,
    block(width: 100%, breakable: false, {
      set align(left)
      body
    }),
  )
  if label-name == none { fig } else { [#fig #label(label-name)] }
}

// ------------------------------------------------------- multi-part figures -
// subpar gives real subfigures -- each with its own caption, its own label and
// its own reference -- instead of an (a)/(b) grid whose parts cannot be cited.
// It carries its own numbering, though, so the chapter prefix has to be handed
// to it explicitly or a subfigure reads "Figure 2." in the middle of chapter 3.
#let chapter-numbering(n) = context {
  let c = counter(heading).get()
  let chapter = if c.len() > 0 { c.at(0) } else { 0 }
  [#chapter.#n]
}

// A reference to a part ("Figure 5.2b") is resolved by the `show ref` rule in
// tum.typ, at the part's own location: subpar's `numbering-sub-ref` would run
// at the citing sentence and count the part's own kind.
#let subfigures(..args) = subpar.grid(numbering: chapter-numbering, ..args)


// ------------------------------------------------------------------ parts --
// A part divider groups the chapters that follow it. It is a level-1 heading,
// so the outline lists it and PDF readers bookmark it, with `numbering: none`
// so it takes no chapter number; an unnumbered heading does not advance the
// heading counter, so the chapters keep their numbers. The chapter show rule
// would force the heading onto a fresh page with a chapter's typography, so a
// scoped rule renders it as a divider page instead. Only the title goes into
// the heading body: the outline reproduces that body, so a kicker or spacing
// placed there would show up in the contents as a second, blank entry. The
// roman numeral comes from `part-counter`, which the contents entry reads back
// at the heading's location.
#let part-counter = counter("voblint-part")

// Chapters open on the next page (openany), so a part does too: forcing a
// recto here would leave a blank verso before every part.
#let part(title) = {
  pagebreak(weak: true)
  part-counter.step()
  {
    show heading.where(level: 1): it => {
      v(1fr)
      align(center, {
        text(0.9em, fill: vb.muted, tracking: 2pt)[PART #context part-counter.display("I")]
        v(0.6em)
        // Full text width and no hyphenation: a title such as "What Must Be
        // Over-Approximated" must not be broken at its hyphen.
        block(width: 100%, {
          set par(justify: false)
          text(
            font: "Latin Modern Roman 12",
            size: 20.74pt,
            weight: "bold",
            hyphenate: false,
            it.body,
          )
        })
      })
      v(1.6fr)
    }
    heading(level: 1, numbering: none, supplement: [Part], title)
  }
  pagebreak(weak: true)
}

// The contents entry for a part: a bold, unnumbered group line without a page
// number, set off from the chapters it groups. Every other level-1 entry is
// left to the default.
#let part-outline-entry(it) = {
  if it.element.supplement == [Part] {
    let n = part-counter.at(it.element.location()).first()
    block(above: 14pt, below: 0pt, link(it.element.location(), text(
      font: "Latin Modern Sans",
      weight: "bold",
    )[Part #numbering("I", n): #it.element.body]))
  } else {
    it
  }
}


// ------------------------------------------------------- playground runs --
// A README playground figure, read from the copy tools/playground_figures.py
// keeps under shared/generated/playground/ together with the link that
// reopens the run. The caption ends with that link, so a reader of the PDF can
// open the same program at the same settings.
#let _playground = json("/shared/generated/playground/playground.json")

#let playground-settings(name) = {
  let r = _playground.at(name)
  let parts = ("analysis " + r.analysis, "globals " + r.globals, "context " + r.context)
  if "k" in r { parts.push("k = " + r.k) }
  raw(parts.join(", "))
}

// `crop: (x0, y0, x1, y1)`, fractions of the screenshot, shows one pane of it
// at `width` (then a length), so its code stays at a readable size.
#let playground-figure(
  name,
  caption,
  width: 100%,
  crop: none,
  label: none,
  placement: none,
) = {
  let r = _playground.at(name)
  let path = "/shared/generated/playground/" + r.image
  let shot = if crop == none { image(path, width: width) } else {
    let (x0, y0, x1, y1) = crop
    // The PNG header holds the pixel size: width at byte 16, height at 20.
    let png = read(path, encoding: none)
    let be32(i) = array(png.slice(i, i + 4)).fold(0, (a, b) => a * 256 + b)
    let aspect = be32(20) / be32(16)
    layout(size => {
      let width = if type(width) == ratio { size.width * width } else { width }
      let full = width / (x1 - x0)
      let height = full * aspect
      block(
        width: width,
        height: height * (y1 - y0),
        clip: true,
        // Sized to the whole image: an image larger than the clipping block
        // would otherwise be centred in it.
        align(top + left, move(dx: -full * x0, dy: -height * y0, box(
          width: full,
          height: height,
          image(path, width: full),
        ))),
      )
    })
  }
  figure(
    shot,
    placement: placement,
    caption: [#caption #h(0.4em) #link(r.url, text(fill: vb.accent, size: 0.9em)[open this run]).],
  )
}

// The program a playground figure was run on, as a listing linked to that run.
#let playground-program(name) = {
  let r = _playground.at(name)
  listing(
    read("/shared/generated/playground/" + r.program),
    lang: "c",
    analysis: r.analysis,
    globals: r.globals,
    ctx: r.context,
    k: if "k" in r { int(r.k) } else { auto },
  )
}

// ------------------------------------------------------- integer strips ---
// A set of integers drawn over a window lo..hi, one cell per integer, with an
// overflow cell at each end that is filled when the set continues past it.
// Analyzer values are parsed from the CLI's printed form, so a strip drawn from
// a registered claim cannot disagree with what the claim quotes.

#let _bound(s) = if s.contains("∞") { none } else { int(s.replace("−", "-")) }

// The set a printed abstract integer denotes, as a predicate. Understands the
// forms the CLI prints: ⊤, ⊥, n, [l,u], c+mℤ, the Sign names, and the Int
// product `signs:…; intervals:…; parities:…; congruences:…`.
#let printed-set(v) = {
  let v = v.trim()
  if v.contains(";") {
    let parts = v.split(";").map(p => printed-set(p.split(":").at(1)))
    return x => parts.all(p => p(x))
  }
  if v == "⊤" or v == "" { return x => true }
  if v == "⊥" { return x => false }
  let sign = (
    "+": x => x > 0,
    "-": x => x < 0,
    "0": x => x == 0,
    "≥0": x => x >= 0,
    "≤0": x => x <= 0,
  )
  if v in sign { return sign.at(v) }
  let ivl = v.match(regex("^\[([^,]+),([^\]]+)\]$"))
  if ivl != none {
    let (l, u) = ivl.captures.map(_bound)
    return x => (l == none or l <= x) and (u == none or x <= u)
  }
  let cong = v.match(regex("^(-?\d+)\+(\d+)ℤ$"))
  if cong != none {
    let (c, m) = cong.captures.map(int)
    return x => calc.rem-euclid(x - c, m) == 0
  }
  assert(v.match(regex("^-?\d+$")) != none, message: "unparsed abstract value " + v)
  x => x == int(v)
}

// kind(x) picks each cell's fill: "run" (a value some execution has), "extra"
// (admitted, reached by no execution), "cond" (a condition's truth set), none.
#let int-strip(lo, hi, kind, left: none, right: none, cell: 4.6mm) = {
  let fill(k) = if k == "run" { vb.proved.lighten(25%) } else if k == "extra" {
    vb.accent.lighten(72%)
  } else if k == "cond" { vb.neutral.lighten(55%) } else { none }
  let box-of(k, body: none) = box(
    width: cell,
    height: 3.6mm,
    radius: 1pt,
    stroke: 0.5pt + vb.frame,
    fill: fill(k),
    align(center + horizon, text(size: 6pt, body)),
  )
  let left = if left == none { kind(lo - 1) } else { left }
  let right = if right == none { kind(hi + 1) } else { right }
  (
    box-of(left, body: sym.dots.h),
    ..range(lo, hi + 1).map(x => box-of(kind(x))),
    box-of(right, body: sym.dots.h),
  )
}

// The axis row matching int-strip: labels every `step`-th integer.
#let int-axis(lo, hi, step: 1) = (
  [],
  ..range(lo, hi + 1).map(x => if calc.rem-euclid(x, step) == 0 {
    text(size: 6.5pt, fill: vb.muted, str(x).replace("-", "−"))
  } else { [] }),
  [],
)

// ------------------------------------------------- registered CLI output ---
// Readers for thesis/shared/generated/<claim>.txt, so a figure quotes the
// analyzer's output by name and a changed output fails the build or the check.

// One variable's printed value at one node of a `--graph-snapshot` claim;
// "⊥" at a node the snapshot marks unreachable.
#let snapshot-var(name, node, var) = {
  let lines = read("/shared/generated/" + name + ".txt").split("\n")
  let i = lines.position(l => l.starts-with("  " + node + ": "))
  assert(i != none, message: "claim " + name + " has no node " + node)
  let rows = lines.slice(i + 1)
  let end = rows.position(l => not l.starts-with("      "))
  let rows = if end == none { rows } else { rows.slice(0, end) }
  if rows.any(l => l.trim() == "unreachable") { return "⊥" }
  let row = rows.find(l => l.trim().starts-with(var + "="))
  assert(row != none, message: "claim " + name + " has no " + var + " at " + node)
  row.trim().slice(var.len() + 1)
}

// One row of a claim's check or diagnostics table, found by its first cell
// (a source location) or by `cond` (the check's condition), as a dictionary.
#let check-row(name, loc: none, cond: none) = {
  let rows = read("/shared/generated/" + name + ".txt")
    .split("\n")
    .map(l => l.trim().split(regex("\s{2,}")))
  let row = rows.find(c => c.len() >= 4 and (c.at(0) == loc or (cond != none and c.at(2) == cond)))
  assert(
    row != none,
    message: "claim " + name + " has no row " + repr(if loc == none { cond } else { loc }),
  )
  (
    loc: row.at(0),
    point: row.at(1),
    cond: row.at(2),
    verdict: row.at(3),
    state: row.at(4, default: ""),
  )
}
