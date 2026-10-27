#import "@preview/touying:0.8.0": *
#import themes.simple: simple-theme, slide
#import "../lib/theme.typ": vb

#let deck(body) = {
  show: simple-theme.with(
    aspect-ratio: "4-3",
    header: none,
    header-right: none,
    footer: none,
    footer-right: none,
    subslide-preamble: none,
    config-page(width: 960pt, height: 720pt, margin: (x: 44pt, y: 22pt), fill: white),
    config-info(title: [Voblint], author: [Manuel Lerchner]),
  )
  set text(font: "Latin Modern Sans", size: 24pt, fill: vb.ink)
  set par(leading: 0.65em, spacing: 0.8em)
  set math.equation(numbering: none)
  set list(
    marker: box(width: 7pt, height: 7pt, fill: rgb("#0065BD")),
    indent: 0pt,
    body-indent: 0.9em,
    spacing: 0.75em,
  )
  show raw: set text(font: "Isabelle DejaVu Sans Mono", size: 0.85em)
  body
}

#let muted(body) = text(fill: vb.neutral, body)
#let accent(body) = text(fill: vb.accent, weight: "bold", body)
#let lead(body) = text(size: 30pt, weight: "bold", body)
#let subhead(body) = block(below: 14pt, text(size: 25pt, weight: "bold", fill: vb.accent, body))
#let aside(body) = text(size: 20pt, fill: vb.neutral, body)
#let rule = line(length: 100%, stroke: 0.7pt + vb.frame)

#let talk-slide(id, title, duration, body, sources: [], notes: [], media: none) = slide[
  #metadata((id: id, title: title, seconds: duration, notes: notes, media: media)) <talk-slide>
  #grid(
    columns: (1fr,),
    rows: (98pt, 76pt, 440pt, auto),
    row-gutter: 0pt,
    [
      #grid(
        columns: (1fr, auto),
        align: horizon,
        text(
          size: 17pt,
          fill: rgb("#0065BD"),
        )[Voblint · Master’s thesis\ Isabelle/HOL formalization],
        image("assets/tum.png", height: 42pt),
      )
      #v(14pt)
      #line(length: 100%, stroke: 0.8pt + rgb("#0065BD"))
    ],
    text(size: 35pt, weight: "bold", fill: black, title),
    block(breakable: false, body),
    [
      #v(5pt)
      #grid(
        columns: (1fr, auto),
        column-gutter: 12pt,
        text(size: 19pt, sources),
        text(size: 16pt, fill: vb.neutral, if id <= 20 { str(id) + " / 20" } else {
          "Backup " + str(id - 20)
        }),
      )
    ],
  )
  #speaker-note[#notes]
]

#let step(label, detail, color: vb.accent) = align(center)[
  #block(width: 100%, inset: (y: 14pt, x: 8pt), stroke: (bottom: 2pt + color))[
    #text(size: 24pt, weight: "bold", label)
  ]
  #v(10pt)
  #text(size: 19pt, fill: vb.neutral, detail)
]

#let pipeline() = grid(
  columns: (1fr, 24pt, 1fr, 24pt, 1fr, 24pt, 1fr),
  align: horizon,
  step([Program], [source semantics]),
  [→],
  step([Equations], [analysis + contexts]),
  [→],
  step([Solver], [inherited verification], color: vb.solver),
  [→],
  step([Report], [semantic verdicts], color: vb.thm),
)

#let result(label, description, color: vb.thm) = [
  #text(size: 24pt, weight: "bold", fill: color, label)
  #h(12pt)
  #description
]


#let sections = (
  [Motivation and objective],
  [Foundations: language and calling contexts],
  [Implementation and verification in Isabelle],
  [Results, validation, and demonstration],
  [Discussion, future work, and conclusion],
)

#let roadmap(id, current) = talk-slide(
  id,
  [Outline],
  10,
  [
    #v(12pt)
    #for (i, name) in sections.enumerate() [
      #block(below: 23pt)[
        #text(
          size: 28pt,
          weight: if i + 1 == current { "bold" } else { "regular" },
          fill: if i + 1 == current { rgb("#0065BD") } else { vb.neutral },
        )[
          #(str(i + 1) + ".") #h(12pt) #name
        ]
      ]
    ]
  ],
  sources: [#sections.at(current - 1)],
  notes: [
    Brief transition: #sections.at(current - 1). Point to the highlighted section;
    do not read the entire outline aloud.
  ],
)
