#import "theme.typ": vb
#import "isabelle-symbols.typ": isabelle-symbols

// Isabelle's own DejaVu build, vendored under assets/fonts. Stock DejaVu Sans
// Mono has no glyph for several symbols a statement can contain (\<And> among
// them), and a missing glyph in a theorem statement is a silently wrong page,
// not a cosmetic problem. Same font the Prover IDE uses, so a snippet looks
// the same on the page as it does in jEdit.
#let isabelle-font = ("Isabelle DejaVu Sans Mono", "DejaVu Sans Mono")

// Isabelle snippets are stored ASCII-only in the sources. `decode-isabelle`
// turns `\<Longrightarrow>` into the glyph, using Isabelle's own symbol table,
// so a snippet can be pasted straight out of a theory file.
//
// Sub- and superscript markers (`\<^sub>`, `\<^sup>`) have no standalone
// glyph in a monospace run, so they are dropped rather than rendered as the
// combining characters Isabelle uses internally.
#let decode-isabelle(s) = {
  let out = s
  for (name, glyph) in isabelle-symbols.pairs() {
    if name.starts-with("^") { continue }
    out = out.replace("\\<" + name + ">", glyph)
  }
  out = out.replace(regex("\\\\<\\^(sub|sup|bold)>"), "")
  out
}

#let isabelle-syntax = "../assets/isabelle.sublime-syntax"

// An Isabelle snippet. Pass a raw block; its text is decoded first. The frame
// and line numbers come from codly, configured once in thesis.typ.
#let isa(body, breakable: false) = {
  let src = if type(body) == str { body } else { body.text }
  raw(decode-isabelle(src), lang: "isabelle", block: true, syntaxes: isabelle-syntax)
}

// Inline Isabelle: `#isai("a \<sqsubseteq> b")`
#let isai(s) = text(font: isabelle-font, raw(
  decode-isabelle(s),
  lang: "isabelle",
  syntaxes: isabelle-syntax,
))

// A listing in one of the other languages of the thesis.
#let listing(body, lang: none, breakable: false) = {
  let src = if type(body) == str { body } else { body.text }
  raw(src, lang: lang, block: true)
}

// References to entities that exist in the formalization. The typographic
// distinction between "a mathematical object" and "an identifier in a theory"
// stays visible on the page -- and, where the rendered theories have been
// built, the name is also a link to the definition itself.
//
// URLs are never guessed here. scripts/check_thesis_links.py resolves each one
// against an `id="<Theory>.<name>|<kind>"` anchor in Isabelle's HTML output and
// writes only the ones it verified, so a link on the page is a link that
// resolved at build time. Before the theories are rendered the map is empty and
// names simply appear unlinked.
#let _links = json("/shared/generated/links.json")

#let _url(kind, name) = {
  let key = kind + ":" + name
  if _links.base != "" and key in _links.links {
    _links.base + _links.links.at(key)
  } else { none }
}

// A name is coloured by what it is only when it is also a link to it; a name
// the map could not resolve stays in the plain identifier colour, so colour on
// the page means "click here".
#let entity(name, color, kind: none, display: none) = {
  let href = if kind == none { none } else { _url(kind, name) }
  let fill = if href == none { vb.plain } else { color }
  let body = text(fill: fill, font: "DejaVu Sans Mono", size: 0.85em, if display == none {
    name
  } else { display })
  if href == none { body } else { link(href, body) }
}
#let isathm(name) = entity(name, vb.thm, kind: "thm")
#let isaconst(name) = entity(name, vb.const, kind: "const")
#let isatype(name) = entity(name, vb.type, kind: "type")
#let isalocale(name) = entity(name, vb.locale, kind: "locale")
#let isacmd(name) = entity(name, vb.trusted)   // an Isabelle command
#let isasession(n) = entity(n, vb.muted)
#let isafile(p) = entity(p, vb.muted)

// The Isabelle name a theorem environment carries. Its kind is whatever the
// rendered theories say it is: the checker records the resolved kind under
// `any:<name>` and the colour follows it.
#let isaname(name) = {
  let key = "any:" + name
  if _links.base != "" and key in _links.links {
    let kind = _links.links.at(key).split("%7C").last()
    let color = (fact: vb.thm, thm: vb.thm, const: vb.const, type: vb.type, locale: vb.locale).at(
      kind,
      default: vb.plain,
    )
    link(_links.base + _links.links.at(key), text(
      fill: color,
      font: "DejaVu Sans Mono",
      size: 0.85em,
      name,
    ))
  } else {
    text(fill: vb.plain, font: "DejaVu Sans Mono", size: 0.85em, name)
  }
}

// One of a locale's named assumptions, such as INIT of the coverage locale: small
// capitals in the locale colour, linking to the assumption's own anchor.
#let oblig(name, of: "ltr_coverage") = {
  let href = _url("thm", of + "." + name)
  // Latin Modern's small capitals are a face of their own, as cmcsc10 is.
  let body = text(
    font: "Latin Modern Roman Caps",
    fill: if href == none { vb.plain } else { vb.locale },
    lower(name),
  )
  if href == none { body } else { link(href, body) }
}

// The Concrete Semantics marker: a small boxed `thy` beside a heading, linking
// to the rendered theory the section is about. Renders as plain text until the
// theories are built.
#let thy-badge(session, theory) = {
  let href = if _links.base == "" { none } else {
    _links.base + "Voblint/" + session + "/" + theory + ".html"
  }
  let body = box(
    inset: (x: 3pt, y: 1pt),
    radius: 2pt,
    baseline: -0.35em,
    stroke: 0.6pt + vb.accent,
    text(size: 0.5em, font: "DejaVu Sans Mono", fill: vb.accent)[thy],
  )
  h(0.35em)
  if href == none { body } else { link(href, body) }
}

// The Concrete Semantics Fig. 4.1 table -- Isabelle symbols beside their ASCII
// forms -- but computed rather than curated: it scans the material the thesis
// actually quotes and lists exactly the symbols that appear in it. Add a
// snippet that uses a new symbol and the table grows on the next build.
#let symbols-used(sources) = {
  let seen = ()
  for src in sources {
    for m in src.matches(regex("\\\\<[A-Za-z^_]+>")) {
      let name = m.text.slice(2, -1)
      if name not in seen and name in isabelle-symbols and not name.starts-with("^") {
        seen.push(name)
      }
    }
  }
  seen.sorted()
}

#let symbol-table(sources, columns: 3) = {
  let names = symbols-used(sources)
  let cell(name) = (
    text(font: isabelle-font, size: 0.9em, isabelle-symbols.at(name)),
    raw("\\<" + name + ">"),
  )
  table(
    columns: (auto, auto) * columns,
    align: (center + horizon, left + horizon) * columns,
    stroke: none,
    inset: (x: 6pt, y: 3.5pt),
    ..names.map(cell).flatten(),
  )
}
