#import "theme.typ": vb
#import "code.typ": decode-isabelle, isabelle-syntax, isabelle-font

// Everything the thesis shows from the formalization comes through here, and
// nothing is retyped. Two sources, generated outside Typst and committed:
//
//   /shared/generated/snippets/<name>.thy   source text of a declaration,
//                                           lifted by name (tools/snippets.py)
//   /shared/generated/facts.json            the statement Isabelle proved,
//                                           exported from a built session
//                                           (tools/facts.py)
//
// A name that does not resolve is a compile error, not a silently wrong page.

#let _facts = json("/shared/generated/facts.json")

#let _frame(body, breakable: false) = block(
  width: 100%, fill: vb.bg, stroke: 0.7pt + vb.frame, radius: 3pt,
  inset: 8pt, breakable: breakable, align(left, body),
)

/// Source text of a declaration, exactly as the theory states it.
/// The leading provenance comment is kept: a reader should be able to open
/// the file it names.
#let thy(name, breakable: false) = _frame(
  text(font: isabelle-font,
       raw(decode-isabelle(read("/shared/generated/snippets/" + name + ".thy")),
           lang: "isabelle", block: true, syntaxes: isabelle-syntax)),
  breakable: breakable,
)

/// The statement Isabelle proved, not a paraphrase of it.
#let stmt(name) = {
  assert(name in _facts.facts,
         message: "no exported statement for `" + name + "` -- add it to "
                  + "thesis/shared/facts.toml and run thesis/tools/facts.py --write")
  _frame(text(font: isabelle-font,
              raw(decode-isabelle(_facts.facts.at(name).statement),
                  lang: "isabelle", block: true, syntaxes: isabelle-syntax)))
}

/// A theorem environment whose body *is* the exported statement.
#let proved(name, note: none) = {
  block(above: 1.1em, below: 1.1em, {
    if note != none { note; v(0.4em) }
    stmt(name)
    v(0.25em)
    align(right, text(size: 0.75em, font: "DejaVu Sans Mono", fill: vb.proved,
                      name))
  })
}
