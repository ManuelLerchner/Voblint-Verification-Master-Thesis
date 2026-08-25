#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/cetz:0.5.2"
#import "@preview/commute:0.3.0" as commute
#import "@preview/subpar:0.2.2"
#import "theme.typ": vb

// Reusable figure vocabulary. Same principle as the LaTeX style file: a CFG
// node looks the same everywhere, and restyling all of them is one edit.

// ---------------------------------------------------------- trust status ---
#let _status = (
  proved:   (vb.proved,   vb.proved.lighten(88%)),
  trusted:  (vb.trusted,  vb.trusted.lighten(86%)),
  unproved: (vb.unproved, vb.unproved.lighten(90%)),
)

#let stage(pos, body, kind: "proved", ..args) = {
  let (line, fill) = _status.at(kind)
  node(pos, align(center, body),
       stroke: 0.9pt + line, fill: fill, corner-radius: 3pt,
       inset: 7pt, ..args)
}

#let flow(from, to, label: none, ..args) = edge(
  from, to, "->", stroke: 0.8pt + vb.neutral,
  label: if label != none {
    text(size: 0.62em, font: "DejaVu Sans Mono", fill: vb.proved, label)
  },
  ..args,
)

#let badge(body, color) = box(
  inset: (x: 3pt, y: 1pt), radius: 2pt,
  fill: color.lighten(88%), stroke: 0.6pt + color,
  text(size: 0.7em, fill: color, body),
)
#let proved-badge   = badge([proved], vb.proved)
#let trusted-badge  = badge([trusted], vb.trusted)
#let unproved-badge = badge([unverified], vb.unproved)

// ------------------------------------------------------------- CFG nodes ---
#let ppoint(pos, body, ..args) = node(
  pos, body, shape: circle, stroke: 0.9pt + vb.neutral, fill: white,
  inset: 4pt, ..args)

#let entry-node(pos, body, ..args) = node(
  pos, body, stroke: 0.9pt + vb.accent, fill: vb.accent.lighten(90%),
  corner-radius: 2pt, inset: 5pt, ..args)

#let result-node = entry-node

#let intra-edge(from, to, label: none, ..args) = edge(
  from, to, "->", stroke: 0.9pt + vb.neutral,
  label: if label != none { text(size: 0.62em, font: "DejaVu Sans Mono", label) },
  ..args)

#let call-edge(from, to, label: none, ..args) = edge(
  from, to, "-->", stroke: (paint: vb.accent, thickness: 0.9pt, dash: "dashed"),
  label: if label != none {
    text(size: 0.62em, font: "DejaVu Sans Mono", fill: vb.accent, label)
  },
  ..args)

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
  node(pos, body, shape: circle, stroke: 1pt + line, fill: fill,
       inset: 4pt, ..args)
}

#let global-unk(pos, body, ..args) = node(
  pos, body, stroke: 0.9pt + vb.neutral, fill: vb.muted.lighten(85%),
  inset: 5pt, ..args)

#let dep-edge(from, to, ..args) = edge(from, to, "->",
  stroke: 0.7pt + vb.muted, ..args)

// A side effect is drawn double-tipped; a withdrawn contribution is dashed.
#let side-edge(from, to, ..args) = edge(from, to, "->>",
  stroke: 1pt + vb.called, ..args)
#let withdrawn-edge(from, to, ..args) = edge(from, to, "-->",
  stroke: (paint: vb.called.lighten(35%), thickness: 1pt, dash: "dashed"),
  ..args)

// -------------------------------------------------------- locale diagram ---
#let locale-node(pos, name, ..args) = node(
  pos, raw(name), stroke: 0.9pt + vb.neutral, fill: white,
  corner-radius: 2pt, inset: 5pt, ..args)

#let instance-node(pos, name, ..args) = node(
  pos, raw(name), stroke: 0.9pt + vb.accent, fill: vb.accent.lighten(90%),
  corner-radius: 2pt, inset: 5pt, ..args)

#let import-edge(from, to, ..args) = edge(from, to, "->",
  stroke: 0.9pt + vb.neutral, ..args)
#let sublocale-edge(from, to, ..args) = edge(from, to, "-->",
  stroke: (paint: vb.accent, thickness: 0.9pt, dash: "dashed"), ..args)
#let interp-edge(from, to, ..args) = edge(from, to, "->",
  stroke: (paint: vb.proved, thickness: 0.9pt, dash: "dotted"), ..args)

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
  width: 100%, fill: vb.bg, stroke: 0.7pt + vb.frame, radius: 3pt,
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
  f: x => 0.55 * x + 2.2,      // the monotone function being iterated
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
  line((sx(x), sy(x)), (sx(x), sy(widen-to)),
       stroke: (paint: vb.unstable, thickness: 1.2pt))
  line((sx(x), sy(widen-to)), (sx(widen-to), sy(widen-to)),
       mark: (end: "straight"), stroke: (paint: vb.unstable, thickness: 1.2pt))

  // narrowing: descending back toward the fixpoint
  let d = widen-to
  for _ in range(narrow-steps) {
    let y = calc.max(f(d), f(d))
    line((sx(d), sy(d)), (sx(d), sy(y)),
         stroke: (paint: vb.proved, thickness: 1pt, dash: "dotted"))
    line((sx(d), sy(y)), (sx(y), sy(y)),
         stroke: (paint: vb.proved, thickness: 1pt, dash: "dotted"))
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
  top-left: [], top-right: [], bottom-left: [], bottom-right: [],
  top-label: [], bottom-label: [], left-label: [], right-label: [],
  dashed-bottom: false,
) = commute.commutative-diagram(
  commute.node((0, 0), top-left),
  commute.node((0, 1), top-right),
  commute.node((1, 0), bottom-left),
  commute.node((1, 1), bottom-right),
  commute.arr((0, 0), (0, 1), top-label),
  ..(if dashed-bottom {
      (commute.arr((1, 0), (1, 1), bottom-label, "dashed"),)
    } else {
      (commute.arr((1, 0), (1, 1), bottom-label),)
    }),
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
  ..points.enumerate().map(((i, p)) => (
    text(fill: vb.accent, p),
    ..vars.enumerate().map(((j, _)) => values.at(i).at(j)),
  )).flatten(),
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

#let subfigures(..args) = subpar.grid(
  numbering: chapter-numbering,
  numbering-sub-ref: (m, n) => context {
    let c = counter(heading).get()
    let chapter = if c.len() > 0 { c.at(0) } else { 0 }
    [#chapter.#m#numbering("a", n)]
  },
  ..args,
)
