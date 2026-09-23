// The Goblint comparison, rendered from the rows of the explainer's alignment
// list. `tools/goblint_alignment.py` extracts them into the JSON read here, so
// the page and the appendix cannot disagree; edit `pages/index.html`, never
// this data.
#import "theme.typ": tint, vb
#import "code.typ": isaconst, isalink, isalocale, isathm, isatype

#let alignment = json("/shared/generated/goblint-alignment.json")

// Shape carries the status in greyscale; colour repeats it.
#let alignment-status = (
  modeled: (title: [modeled], color: vb.proved, fill: 1),
  simplified: (title: [simplified], color: vb.trusted, fill: 0.5),
  absent: (title: [not modeled], color: vb.unproved, fill: 0),
)

#let alignment-mark(status) = {
  let s = alignment-status.at(status)
  let r = 0.32em
  box(baseline: 0.05em, circle(
    radius: r,
    stroke: 0.8pt + s.color,
    fill: if s.fill == 1 { s.color } else if s.fill == 0 { none } else { tint(s.color, 60%) },
  ))
}

#let alignment-count(status) = alignment.rows.filter(r => r.status == status).len()

#let _cite(ref) = {
  if ref.kind == "const" { isaconst(ref.name) } else if ref.kind == "type" {
    isatype(ref.name)
  } else if ref.kind == "locale" { isalocale(ref.name) } else if ref.kind == "thm" {
    isathm(ref.name)
  } else if ref.kind == "theory" {
    isalink("theory", ref.name, text(
      font: "DejaVu Sans Mono",
      size: 0.85em,
      fill: vb.accent,
      ref.name.split(".").last(),
    ))
  } else { panic("unknown citation kind " + ref.kind) }
}

// The site's label, followed by the formal names it links to when the label
// is a description rather than those names.
#let _voblint(v) = {
  let cites = v.refs.map(_cite).join(" / ")
  let names = v.refs.map(r => r.name.split(".").last()).join(" / ")
  // Long formal names may break after an underscore instead of overrunning the note.
  show "_": "_" + sym.zws
  if v.refs.len() == 0 { text(fill: vb.muted, v.label) } else if v.label == names {
    cites
  } else [#v.label \ #text(size: 0.9em, cites)]
}

#let _goblint(g) = [
  #link(g.url, text(font: "DejaVu Sans Mono", size: 0.85em, g.name)) \
  #text(font: "DejaVu Sans Mono", size: 7pt, fill: vb.neutral, g.file.split("/").last())
]

#let alignment-table() = {
  set text(size: 0.9em)
  set par(justify: false)
  // A row split across pages separates a construct from its note.
  set table.cell(breakable: false)
  table(
    columns: (1fr, 1.15fr, 2.2fr),
    align: left + top,
    stroke: (x, y) => if y == 0 { (bottom: 0.6pt + vb.neutral) } else {
      (bottom: 0.3pt + vb.frame)
    },
    table.header([*Goblint construct*], [*Voblint counterpart*], [*Note*]),
    ..for (status, s) in alignment-status {
      let rows = alignment.rows.filter(r => r.status == status)
      (
        // A subheader: Typst keeps it with the first row of its group.
        table.header(level: 2, repeat: false, table.cell(colspan: 3, fill: tint(s.color, 90%))[
          #alignment-mark(status) #h(0.3em) *#s.title* (#rows.len())
        ]),
        ..for r in rows {
          (_goblint(r.goblint), _voblint(r.voblint), r.note.replace("'", "’"))
        },
      )
    },
  )
}
