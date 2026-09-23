#import "theme.typ": vb
#import "isabelle-symbols.typ": isabelle-symbols
#import "@preview/codly:1.3.0": local as codly-local

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
// Sub- and superscript markers (`\<^sub>`, `\<^sup>`, `\<^bsub>…\<^esub>`)
// have no glyph of their own. Decoding brackets their argument with
// private-use characters, and `isabelle-scripts`, applied to every Isabelle
// raw block and inline span, sets the bracketed text as a real sub- or
// superscript. The highlighter still sees one run of text, so a subscript
// inside a string keeps the string's colour.
#let _sub = ("\u{E000}", "\u{E001}")
#let _sup = ("\u{E002}", "\u{E003}")
#let _script-arg = "(\\\\<[A-Za-z]+>|.)"
#let decode-isabelle(s) = {
  // A raw block is set line by line, so a script spanning a line break is
  // closed and reopened around it.
  let wrap(pair) = m => (
    pair.at(0) + m.captures.at(0).replace("\n", pair.at(1) + "\n" + pair.at(0)) + pair.at(1)
  )
  let out = s
  out = out.replace(regex("(?s)\\\\<\\^bsub>(.*?)\\\\<\\^esub>"), wrap(_sub))
  out = out.replace(regex("\\\\<\\^sub>" + _script-arg), wrap(_sub))
  out = out.replace(regex("\\\\<\\^sup>" + _script-arg), wrap(_sup))
  for (name, glyph) in isabelle-symbols.pairs() {
    if name.starts-with("^") { continue }
    out = out.replace("\\<" + name + ">", glyph)
  }
  out = out.replace(regex("\\\\<\\^(sub|sup|bold)>"), "")
  out
}

// Private-use markers are three bytes each in UTF-8.
#let _script-body(m) = m.text.slice(3, -3)
#let isabelle-scripts(body) = {
  show regex(_sub.at(0) + "[^" + _sub.at(1) + "]*" + _sub.at(1)): m => sub(
    size: 0.7em,
    _script-body(m),
  )
  show regex(_sup.at(0) + "[^" + _sup.at(1) + "]*" + _sup.at(1)): m => super(
    size: 0.7em,
    _script-body(m),
  )
  body
}

#let isabelle-syntax = "../assets/isabelle.sublime-syntax"

// An Isabelle snippet. Pass a raw block; its text is decoded first. The frame
// and line numbers come from codly, configured once in thesis.typ.
#let isa(body, breakable: false) = {
  let src = if type(body) == str { body } else { body.text }
  block(above: 0.9em, below: 0.9em, raw(
    decode-isabelle(src),
    lang: "isabelle",
    block: true,
    syntaxes: isabelle-syntax,
  ))
}

// Inline Isabelle: `#isai("a \<sqsubseteq> b")`. Sub- and superscripts are set
// as such, so `\<C>\<^bsub>\<G>,g,S\<^esub>` reads as the theories print it.
#let isai(s) = text(font: isabelle-font, raw(
  decode-isabelle(s),
  lang: "isabelle",
  syntaxes: isabelle-syntax,
))

// ------------------------------------------------------- VIMP playground ---
// Every VIMP listing links to the browser playground, preloaded with the
// program it shows. The link is computed here from the listing's own text, so
// no chapter holds a URL that can drift from its program;
// thesis/tools/vimp_listings.py decodes every link in the built PDF and
// compares it with the listing.

// A regression fixture, linked to its file in the repository. The path is
// relative to tests/regression; thesis/tools/vimp_listings.py checks that it
// exists, and that no fixture path appears in the chapters without this link.
#let repo-blob = "https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/main/"
#let fixture(path, label: none) = link(
  repo-blob + "tests/regression/" + path,
  raw(if label == none { path } else { label }),
)

#let playground-base = "https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html"

// What the playground selects when a link names nothing (pages/playground.html;
// the check fails when the page changes them).
#let playground-defaults = (
  "analysis": "interval",
  "globals": "warrow",
  "context": "call-string",
  "k": 1,
)

// Programs and settings of the claims in shared/claims.toml, extracted by
// vimp_listings.py because Typst reads nothing outside thesis/.
#let _vimp-claims = json("/shared/generated/vimp-claims.json")

#let _b64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"

// base64url without padding, as the playground's packSource writes it.
#let _base64url(data) = {
  let out = ""
  let i = 0
  while i < data.len() {
    let chunk = data.slice(i, calc.min(i + 3, data.len()))
    let n = chunk.len()
    let v = chunk.at(0).bit-lshift(16)
    if n > 1 { v = v.bit-or(chunk.at(1).bit-lshift(8)) }
    if n > 2 { v = v.bit-or(chunk.at(2)) }
    for j in range(n + 1) {
      let idx = v.bit-rshift(18 - 6 * j).bit-and(63)
      out += _b64.at(idx)
    }
    i += 3
  }
  out
}

// Typst has no compressor, but a raw-deflate stream may consist of stored
// (uncompressed) blocks, and DecompressionStream("deflate-raw") in the
// playground inflates those like any other. The link is longer than the Share
// button's; it opens the same program.
#let _deflate-stored(data) = {
  if data.len() == 0 { return (1, 0, 0, 255, 255) }
  let out = ()
  let i = 0
  while i < data.len() {
    let len = calc.min(65535, data.len() - i)
    let final = if i + len == data.len() { 1 } else { 0 }
    let nlen = 65535 - len
    out += (final, len.bit-and(255), len.bit-rshift(8), nlen.bit-and(255), nlen.bit-rshift(8))
    out += data.slice(i, i + len)
    i += len
  }
  out
}

// A fragment without a top-level declaration would not parse on its own, so
// its link opens it as the body of `main`.
#let vimp-program(shown) = if shown.match(regex("(?m)^(fun|global)\\b")) != none { shown } else {
  (
    "fun main() {\n"
      + shown.split("\n").map(l => if l == "" { l } else { "  " + l }).join("\n")
      + "\n}"
  )
}

// `ctx` is the playground's `context` parameter; `context` is a Typst keyword.
#let playground-link(program, analysis: "interval", globals: "warrow", ctx: "call-string", k: 1) = {
  let query = "?analysis=" + analysis + "&globals=" + globals + "&context=" + ctx
  if ctx == "call-string" { query += "&k=" + str(k) }
  playground-base + query + "#code=" + _base64url(_deflate-stored(array(bytes(program))))
}

// A listing. VIMP (`lang: "c"`) carries a playground link on its language tag.
// `claim` names an entry of shared/claims.toml whose fixture this listing shows
// or excerpts: the link then opens the whole fixture, without its comments, at
// the claim's settings.
// `program` is the whole program a listing split across panes is part of.
// Otherwise the link opens the text shown, at the given or the playground's
// settings.
#let listing(
  body,
  lang: none,
  breakable: false,
  claim: none,
  program: none,
  analysis: auto,
  globals: auto,
  ctx: auto,
  k: auto,
) = {
  let src = if type(body) == str { body } else { body.text }
  let code = raw(src, lang: lang, block: true)
  if lang != "c" { return code }

  assert(
    claim == none or claim in _vimp-claims,
    message: "No VIMP claim " + repr(claim) + "; run pixi run thesis-vimp-write",
  )
  let run = if claim == none { playground-defaults } else {
    playground-defaults + _vimp-claims.at(claim).settings
  }
  let given = ("analysis": analysis, "globals": globals, "context": ctx, "k": k)
    .pairs()
    .filter(((_, v)) => v != auto)
    .to-dict()
  let settings = run + given
  assert(claim == none or program == none, message: "listing: pass claim or program, not both")
  let part-of = program
  let program = if claim != none { _vimp-claims.at(claim).program } else if part-of != none {
    part-of
  } else { vimp-program(src) }
  let url = playground-link(
    program,
    analysis: settings.analysis,
    globals: settings.globals,
    ctx: settings.at("context"),
    k: settings.k,
  )

  [#metadata((
    shown: src,
    program: program,
    url: url,
    claim: claim,
    part-of: part-of,
    given: given,
    settings: settings,
  )) <vimp-listing>]
  // A program split by a page break is hard to read; VIMP listings are short.
  block(above: 0.9em, below: 0.9em, breakable: false, codly-local(code, languages: (
    c: (name: link(url)[VIMP #sym.arrow.tr], color: vb.keyword),
  )))
}

// References to entities that exist in the formalization. The typographic
// distinction between "a mathematical object" and "an identifier in a theory"
// stays visible on the page -- and, where the rendered theories have been
// built, the name is also a link to the definition itself.
//
// URLs are never guessed here. scripts/check_thesis_links.py resolves each one
// against an `id="<Theory>.<name>|<kind>"` anchor in Isabelle's HTML output and
// writes only the ones it verified, so a link on the page is a link that
// resolved at build time. Missing formal links fail rendering.
#let _links = json("/shared/generated/links.json")

#let _url(kind, name) = {
  let key = kind + ":" + name
  assert(
    _links.base != "" and key in _links.links,
    message: "Missing Isabelle HTML link for " + key + "; run pixi run thesis-links-write",
  )
  _links.base + _links.links.at(key)
}

#let isalink(kind, name, body) = link(_url(kind, name), body)

// Formal entities require links. Command syntax and repository paths are
// code labels and have no project-definition anchor.
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
#let isasession(n) = entity(n, vb.muted, kind: "session")
#let isafile(p) = entity(p, vb.muted)

// The Isabelle name a theorem environment carries. Its kind is whatever the
// rendered theories say it is: the checker records the resolved kind under
// `any:<name>` and the colour follows it.
#let isaname(name) = {
  let key = "any:" + name
  let href = _url("any", name)
  let kind = _links.links.at(key).split("%7C").last()
  let color = (fact: vb.thm, thm: vb.thm, const: vb.const, type: vb.type, locale: vb.locale).at(
    kind,
    default: vb.plain,
  )
  link(href, text(
    fill: color,
    font: "DejaVu Sans Mono",
    size: 0.85em,
    name,
  ))
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
// to the rendered theory the section is about.
#let thy-badge(session, theory) = {
  let href = _url("theory", session + "." + theory)
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
