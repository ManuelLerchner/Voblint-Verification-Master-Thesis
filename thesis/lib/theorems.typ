#import "theme.typ": vb
#import "tum.typ": thm-rich
#import "code.typ": isacmd, isaname
#import "sources.typ": proved

// Minimal theorem environments, numbered per chapter. Kept local rather than
// pulled from a package so the numbering scheme matches the LaTeX side
// exactly and nothing has to be re-learned when comparing the two.

// Kept as a name other modules import, but the numbering itself comes from the
// rich-counter in tum.typ, which restarts at each chapter without a reset rule.
#let thm-counter = counter("theorem")

// The header names the result twice: by its number and title, and by the
// Isabelle name it is stated under, which links to the rendered theory. A
// definition also names its declaring command (`datatype exp`), which
// thesis-refs checks against the sources.
#let _thm-block(kind, name, isa-name, body, italic: true, cmd: none, sticky: false) = {
  (thm-rich.step)()
  block(above: 1.1em, below: 1.1em, width: 100%, sticky: sticky, {
    strong[#kind #context (thm-rich.display)("1.1")]
    if name != none or isa-name != none {
      [ (]
      if name != none { name }
      if name != none and isa-name != none { [, ] }
      if cmd != none { [#isacmd(cmd) ] }
      if isa-name != none { isaname(isa-name) }
      [)]
    }
    strong[.]
    h(0.4em)
    if italic { emph(body) } else { body }
  })
}

// With `statement: true`, the proved Isabelle statement of `isa` follows the
// prose directly, and the theorem sticks to it across a page break.
#let _stated(kind, body, name, isa, statement) = {
  _thm-block(kind, name, isa, body, sticky: statement)
  if statement { proved(isa) }
}
#let theorem(body, name: none, isa: none, statement: false) = _stated(
  "Theorem",
  body,
  name,
  isa,
  statement,
)
#let lemma(body, name: none, isa: none, statement: false) = _stated(
  "Lemma",
  body,
  name,
  isa,
  statement,
)
#let corollary(body, name: none, isa: none, statement: false) = _stated(
  "Corollary",
  body,
  name,
  isa,
  statement,
)
// A definition may carry the Isabelle declaration it describes. The snippet is
// set as a numbered figure right below the definition, never floated, and the
// definition sticks to it, so prose and declaration cannot be separated.
#let definition(
  body,
  name: none,
  isa: none,
  cmd: none,
  snippet: none,
  snippet-caption: none,
  snippet-label: none,
  snippet-size: 6.2pt,
) = {
  _thm-block("Definition", name, isa, body, italic: false, cmd: cmd, sticky: snippet != none)
  if snippet != none {
    let fig = figure(
      {
        show raw.where(block: true): set text(size: snippet-size)
        snippet
      },
      kind: image,
      placement: none,
      caption: snippet-caption,
    )
    if snippet-label != none [#fig #snippet-label] else { fig }
  }
}
#let example(body, name: none, isa: none) = _thm-block("Example", name, isa, body, italic: false)

// Reset the theorem counter at every chapter, matching LaTeX's [chapter].
#let reset-theorems-on-chapter = {
  show heading.where(level: 1): it => {
    thm-counter.update(0)
    it
  }
}
