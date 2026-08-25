#import "theme.typ": vb
#import "tum.typ": thm-rich

// Minimal theorem environments, numbered per chapter. Kept local rather than
// pulled from a package so the numbering scheme matches the LaTeX side
// exactly and nothing has to be re-learned when comparing the two.

// Kept as a name other modules import, but the numbering itself comes from the
// rich-counter in tum.typ, which restarts at each chapter without a reset rule.
#let thm-counter = counter("theorem")

#let _thm-block(kind, name, isa-name, body, italic: true) = {
  (thm-rich.step)()
  block(above: 1.1em, below: 1.1em, width: 100%, {
    strong[#kind #context (thm-rich.display)("1.1")]
    if name != none [ (#name)]
    strong[.]
    h(0.4em)
    if italic { emph(body) } else { body }
    if isa-name != none {
      block(width: 100%, above: 0.3em, align(right,
        text(size: 0.75em, font: "DejaVu Sans Mono", fill: vb.proved, isa-name)))
    }
  })
}

#let theorem(body, name: none, isa: none)    = _thm-block("Theorem", name, isa, body)
#let lemma(body, name: none, isa: none)      = _thm-block("Lemma", name, isa, body)
#let corollary(body, name: none, isa: none)  = _thm-block("Corollary", name, isa, body)
#let definition(body, name: none, isa: none) = _thm-block("Definition", name, isa, body, italic: false)
#let example(body, name: none, isa: none)    = _thm-block("Example", name, isa, body, italic: false)

// Reset the theorem counter at every chapter, matching LaTeX's [chapter].
#let reset-theorems-on-chapter = {
  show heading.where(level: 1): it => { thm-counter.update(0); it }
}
