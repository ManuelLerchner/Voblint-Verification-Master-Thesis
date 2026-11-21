#import "theme.typ": vb
#import "tum.typ": thm-rich
#import "code.typ": isaname

// Minimal theorem environments, numbered per chapter. Kept local rather than
// pulled from a package so the numbering scheme matches the LaTeX side
// exactly and nothing has to be re-learned when comparing the two.

// Kept as a name other modules import, but the numbering itself comes from the
// rich-counter in tum.typ, which restarts at each chapter without a reset rule.
#let thm-counter = counter("theorem")

// `Definition 3.1: Expressions (exp).` The formal source takes the round
// parentheses of inline references. `cmd` remains checked source metadata.
// A statement stays on one page, so its premises are never cut from its
// conclusion. Definitions and examples may span rule systems and split unless
// the call passes `breakable: false`.
#let _thm-block(kind, name, isa-name, body, italic: true, cmd: none, breakable: false) = {
  (thm-rich.step)()
  block(above: 1.1em, below: 1.1em, width: 100%, breakable: breakable, {
    strong[#kind #context (thm-rich.display)("1.1")#if name != none [: #name]]
    if isa-name != none { [ (#isaname(isa-name))] }
    strong[.]
    h(0.4em)
    if italic { emph(body) } else { body }
  })
}

#let theorem(body, name: none, isa: none) = _thm-block("Theorem", name, isa, body)
#let lemma(body, name: none, isa: none) = _thm-block("Lemma", name, isa, body)
#let corollary(body, name: none, isa: none) = _thm-block("Corollary", name, isa, body)
#let definition(body, name: none, isa: none, cmd: none, breakable: true) = _thm-block(
  "Definition",
  name,
  isa,
  body,
  italic: false,
  cmd: cmd,
  breakable: breakable,
)
#let example(body, name: none, isa: none, breakable: true) = _thm-block(
  "Example",
  name,
  isa,
  body,
  italic: false,
  breakable: breakable,
)

// Reset the theorem counter at every chapter, matching LaTeX's [chapter].
#let reset-theorems-on-chapter = {
  show heading.where(level: 1): it => {
    thm-counter.update(0)
    it
  }
}
