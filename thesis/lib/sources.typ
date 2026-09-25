#import "code.typ": decode-isabelle, isabelle-syntax, isalink, isathm

// Everything the thesis shows from the formalization comes through here, and
// nothing is retyped. Two sources, generated outside Typst and committed:
//
//   /shared/generated/snippets/<name>.thy   source text of a declaration,
//                                           lifted by name (tools/snippets.py);
//                                           a theorem is cut before its proof
//   /shared/generated/facts.json            the facts a built session proves,
//                                           with their theory (tools/facts.py)
//
// A name that does not resolve is a compile error, not a silently wrong page.

#let _facts = json("/shared/generated/facts.json")

// codly draws the frame and line numbers, as for every other listing.
#let _snippet(name, kind) = isalink(kind, name, raw(
  decode-isabelle(read("/shared/generated/snippets/" + name + ".thy")),
  lang: "isabelle",
  block: true,
  syntaxes: isabelle-syntax,
))

/// Source text of a declaration, exactly as the theory states it.
/// The leading provenance comment is kept: a reader should be able to open
/// the file it names.
// A short declaration stays on one page, away from which its last clauses
// would lose the text that explains them. A long one may break: kept whole, it
// would push a half-empty page ahead of it.
#let _long-snippet = 18
#let _breakable(name) = (
  read("/shared/generated/snippets/" + name + ".thy").split("\n").len() > _long-snippet
)

#let thy(name) = block(
  above: 0.9em,
  below: 0.9em,
  breakable: _breakable(name),
  _snippet(name, "any"),
)

// The pretty-printer breaks a rule for its own margin, which leaves `𝒢,Π ⊢`
// alone on a line. Rebreak it as a rule reads: one premise per line, the
// conclusion after `⟹`, and a long conclusion before its step arrow.
// An equation keeps Isabelle's own breaks, which fall at its `let` bindings.
// `c1.0` is how Isabelle prints a variable whose name ends in a digit.
#let _reflow-rule(s) = {
  let s = s.replace(regex("([A-Za-z_]\\d+)\\.0\\b"), m => m.captures.at(0))
  if not s.contains("⟹") and not s.contains("⊢") { return s.trim() }
  let flat = s.replace(regex("\\s+"), " ").trim()
  let (prems, concl) = if flat.starts-with("⟦") {
    let (p, c) = flat.split("⟧ ⟹ ")
    (p.slice("⟦".len()).split("; "), c)
  } else { ((), flat) }
  let concl = if concl.clusters().len() > 80 {
    concl.replace(regex(" (→\\S*) "), m => "\n    " + m.captures.at(0) + " ")
  } else { concl }
  if prems.len() == 0 { return concl }
  let n = prems.len()
  let lines = prems
    .enumerate()
    .map(((i, p)) => (
      (if i == 0 { "⟦" } else { " " }) + p + (if i + 1 < n { ";" } else { "⟧" })
    ))
  lines.join("\n") + "\n⟹ " + concl.replace("\n", "\n  ")
}

/// A fact as the built session prints it (facts.json), for a rule of an
/// inductive definition, which has no source text of its own to lift.
#let stated(name) = {
  assert(
    name in _facts.facts,
    message: "`" + name + "` is not an exported fact -- add it to thesis/shared/facts.toml",
  )
  block(breakable: false, {
    isalink("thm", name, raw(
      _reflow-rule(decode-isabelle(_facts.facts.at(name).statement)),
      lang: "isabelle",
      block: true,
      syntaxes: isabelle-syntax,
    ))
    v(0.25em)
    align(right, text(size: 0.75em, isathm(name)))
  })
}

/// The notation a declaration gives a constant, read from its lifted source
/// text: `mixfix("numeric_domain", "gamma")` is the symbol the theory declares.
#let mixfix(snippet, const) = {
  let src = read("/shared/generated/snippets/" + snippet + ".thy")
  let m = src.match(regex(
    "\\b" + const + "\\s*::\\s*\"[^\"]*\"\\s*\\((?:infix[lr]?\\s*)?\"([^\"]+)\"",
  ))
  assert(m != none, message: "no mixfix for `" + const + "` in snippet `" + snippet + "`")
  decode-isabelle(m.captures.at(0))
}

/// A theorem as its theory states it: the `assumes`/`shows` header without
/// the proof. The name must also be a fact the built session proves, in the
/// theory the text was lifted from (checked by tools/facts.py).
#let proved(name, note: none) = {
  assert(
    name in _facts.facts,
    message: "`"
      + name
      + "` is not an exported fact -- add it to thesis/shared/facts.toml "
      + "and run pixi run thesis-facts-write",
  )
  block(above: 1.1em, below: 1.1em, breakable: _breakable(name), {
    if note != none {
      note
      v(0.4em)
    }
    _snippet(name, "thm")
  })
}
