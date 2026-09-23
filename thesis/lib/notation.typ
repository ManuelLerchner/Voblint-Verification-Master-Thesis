// The notation table of appendix B, rendered from the data
// `tools/notation.py` derives from the theories. The README and the explainer
// render the same file, so edit `shared/notation.toml` (reading and meaning)
// or the theories (everything else), never the rendered table.
#import "theme.typ": vb
#import "code.typ": entity, isai, isalocale

#let notation = json("/shared/generated/notation.json")
#let _links = json("/shared/generated/links.json")

// `_x_` is a metavariable, `{...}` an Isabelle fragment in ASCII symbols.
#let _prose(s) = {
  let pos = 0
  for m in s.matches(regex("\\{([^}]*)\\}|_([^_]+)_")) {
    if m.start > pos { s.slice(pos, m.start) }
    if m.captures.at(0) != none { isai(m.captures.at(0)) } else { emph(m.captures.at(1)) }
    pos = m.end
  }
  if pos < s.len() { s.slice(pos) }
}

#let _small(body) = text(size: 7pt, fill: vb.neutral.lighten(15%), body)

// The declaring constant, linked, with its theory beneath it.
#let _decl(f) = {
  entity(f.cite.name, vb.const, kind: "const", display: f.const)
  let page = f.href.split("#").first()
  linebreak()
  // The same theory style as the anchor index of appendix B.1.
  link(_links.base + page, text(font: "DejaVu Sans Mono", size: 7pt, fill: vb.neutral, f.theory))
}

#let _cells(e) = {
  let forms = e.forms
  let symbol = forms.map(f => f.symbol).dedup().map(isai).join([ \ ])
  let decls = forms.map(_decl).join([ \ ])
  if e.local != none {
    let l = e.local
    symbol += if e.kind == "named" {
      [ \ #isai(l.symbol) #_small[only within #isalocale(l.scope), which fixes its environment]]
    } else {
      [ \ #_small[within #isalocale(l.scope):] #isai(l.symbol)]
    }
  }
  if e.group == "shorthand" {
    decls = forms
      .map(f => [#_decl(
          f,
        ) \ #_small[in #isalocale(f.scope)#if not f.pretty_printed [, input only]]])
      .join([ \ ])
  }
  let meaning = _prose(e.meaning)
  if e.group == "shorthand" {
    meaning += [ \ #_small[stands for] #isai(forms.first().expands)]
  }
  // Long locale names may break after an underscore instead of running
  // into the margin.
  (
    symbol,
    _prose(e.reads),
    meaning,
    {
      show "_": "_" + sym.zws
      decls
    },
  )
}

#let notation-table() = {
  set text(size: 8pt)
  set par(first-line-indent: 0pt, justify: false)
  show raw: set text(size: 7.5pt)
  // A row split across pages separates a shorthand from its expansion.
  set table.cell(breakable: false)
  table(
    columns: (1.25fr, 0.95fr, 1.6fr, 1.05fr),
    align: left + top,
    stroke: none,
    inset: (x: 4pt, y: 3pt),
    table.header(
      table.hline(stroke: 0.5pt),
      [*Notation*],
      [*Reads as*],
      [*Meaning*],
      [*Declared by*],
      table.hline(stroke: 0.4pt),
    ),
    ..for (key, g) in notation.groups {
      let rows = notation.entries.filter(e => e.group == key)
      (
        // A subheader: Typst keeps it with the first row of its group.
        table.header(level: 2, repeat: false, table.cell(
          colspan: 4,
          inset: (x: 4pt, top: 7pt, bottom: 3pt),
        )[*#g.title*#if "note" in g [ #h(0.3em) #_small(g.note)]]),
        ..rows.map(_cells).flatten(),
      )
    },
    table.hline(stroke: 0.5pt),
  )
}
