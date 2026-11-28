// Visual language of the talk: 16:9 pages on a light ground, a thin dark
// brand bar, one bold claim per slide with its key words coloured, and
// figures instead of bullet text.
#import "@preview/cetz:0.5.2"
#import "../lib/theme.typ": vb

#let ink = rgb("#111111")
#let paper = rgb("#F4F5F5")
#let night = rgb("#0F1E25")
#let blue = vb.accent
#let red = vb.unproved
#let green = vb.proved
#let amber = vb.trusted
#let marker = rgb("#FFF200")
#let grey = rgb("#8C969B")
#let pale = rgb("#E3E6E7")

#let width = 1280pt
#let height = 720pt
#let margin = (x: 64pt, y: 48pt)

#let deck(body) = {
  set document(title: [Voblint: Verifying a Context-Sensitive Abstract Interpreter], author: (
    "Manuel Lerchner",
  ))
  set page(width: width, height: height, margin: margin, fill: paper)
  // Arrows, crosses and check marks Roboto lacks come from DejaVu Sans Mono.
  set text(font: ("Roboto", "DejaVu Sans Mono"), size: 28pt, fill: ink)
  set par(leading: 0.55em)
  show raw: set text(font: "Isabelle DejaVu Sans Mono", size: 0.9em)
  show math.equation: set text(font: "Latin Modern Math")
  body
}

// Coloured, bold key word inside a claim.
#let b(c, body) = text(fill: c, weight: "bold", body)
#let small(body) = text(size: 18pt, fill: grey, body)
#let cite(body) = text(size: 16pt, fill: grey, body)

#let brand-bar(section) = place(top + left, dx: -margin.x, dy: -margin.y, block(
  width: width,
  height: 56pt,
  fill: night,
  inset: (x: 28pt),
  align(horizon, grid(
    columns: (auto, auto, 1fr),
    column-gutter: 12pt,
    align: horizon,
    image("assets/voblint.png", height: 36pt),
    text(fill: white, size: 22pt)[Voblint],
    align(right, text(fill: grey, size: 18pt, section)),
  )),
))

// One logical slide: its timing and notes feed build.py; `steps` repeats the
// page for a build, passing the step number (1-based) to `body`.
#let talk-slide(
  id,
  title,
  seconds,
  body,
  section: none,
  notes: [],
  sources: none,
  steps: 1,
) = {
  for step in range(1, steps + 1) {
    page[
      #if step == 1 [
        #metadata((id: id, title: title, seconds: seconds, notes: notes)) <talk-slide>
      ]
      #brand-bar(section)
      #v(40pt)
      #block(below: 24pt, text(size: 44pt, weight: "bold", title))
      #if type(body) == function { body(step) } else { body }
      #if sources != none { place(bottom + left, cite(sources)) }
      #place(bottom + right, small(if id < 100 { str(id) } else { "Backup" }))
    ]
  }
}

// A slide whose only content is one sentence.
#let statement-slide(id, seconds, kicker, body, notes: []) = page[
  #metadata((id: id, title: kicker, seconds: seconds, notes: notes)) <talk-slide>
  #align(horizon)[
    #text(size: 22pt, style: "italic", weight: "bold", kicker)
    #v(24pt)
    #text(size: 52pt, weight: "bold", body)
  ]
]

// Crop a region, in source pixels, out of a raster image of size (iw, ih).
#let crop(path, iw, ih, x, y, w, h, width: auto, height: auto) = {
  let scale = if width != auto { width / w } else { height / h }
  block(width: w * scale, height: h * scale, clip: true, radius: 10pt, place(
    top + left,
    dx: -x * scale,
    dy: -y * scale,
    image(path, width: iw * scale, height: ih * scale),
  ))
}

#let card(body, c, w: 300pt, h: 170pt) = box(
  width: w,
  height: h,
  radius: 12pt,
  fill: white,
  stroke: 2pt + c,
  inset: 18pt,
  align(center + horizon, text(size: 26pt, weight: "bold", body)),
)

#let link-mark(mark, c, label) = box(width: 130pt, align(center + horizon)[
  #text(size: 60pt, fill: c, weight: "bold", mark)\
  #text(size: 18pt, fill: c, label)
])

// The claim → statement → proof picture; slides 4 and 14 fill it.
#let checked-chain(meaning, statement, proof) = align(center, grid(
  columns: 5,
  align: horizon,
  card(meaning, grey),
  link-mark([?], red, [humans review]),
  card(statement, grey),
  link-mark([✓], green, [kernel checks]),
  card(proof, grey),
))

#let checklist(items, step, colours: none) = for (i, name) in items.enumerate() {
  let done = i < step
  let now = i + 1 == step
  let c = if colours == none { ink } else { colours.at(i) }
  block(
    below: 10pt,
    inset: (x: 10pt, y: 8pt),
    fill: if now { marker } else if done { pale } else { none },
    text(
      size: 32pt,
      fill: if done { c } else { grey.lighten(30%) },
      weight: if now { "bold" } else { "regular" },
    )[#if done [✓] else [#h(0.9em)] #h(6pt) #name],
  )
}
