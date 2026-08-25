#import "@preview/rich-counters:0.2.2": rich-counter
#import "theme.typ": vb

// Theorems, lemmas and definitions share one sequence that restarts at each
// chapter. A rich-counter states that directly -- it inherits one level from
// the headings -- instead of a show rule that resets a bare counter and has to
// be kept in step with wherever the number is displayed.
//
// Figures, tables and algorithms deliberately do *not* use one: Typst resolves
// `@fig:...` through its own figure counters, so driving their numbering from
// a parallel counter numbers the caption right and every cross-reference as
// `3.0`. Those are reset per chapter instead, further down.
#let thm-rich = rich-counter(identifier: "voblint-theorem", inherited_levels: 1)

// Page geometry and front matter mirroring the unofficial TUM Informatics
// thesis template: A4, 11pt, binding correction, cover page followed by a
// bilingual title page and the disclaimer.

#let thesis(
  title: "",
  title-de: "",
  doctype: "Master's Thesis",
  study-program: "Informatics",
  author: "",
  supervisor: "",
  advisors: (),
  date: "",
  logo: "../assets/tumlogo.svg",
  body,
) = {
  set document(title: title, author: author)

  set page(
    paper: "a4",
    margin: (inside: 3.2cm, outside: 2.4cm, top: 2.8cm, bottom: 3.0cm),
    binding: left,
    numbering: none,
  )
  set text(font: "New Computer Modern", size: 11pt,
           lang: "en")
  set par(justify: true, leading: 0.62em, spacing: 1.0em)
  set heading(numbering: "1.1")

  show heading.where(level: 1): it => {
    pagebreak(weak: true)
    v(2.2cm)
    counter(figure.where(kind: image)).update(0)
    counter(figure.where(kind: table)).update(0)
    counter(figure.where(kind: "algorithm")).update(0)
    block(below: 1.4em, text(size: 1.9em, weight: "bold", {
      if it.numbering != none {
        context counter(heading).display(it.numbering)
        h(0.5em)
      }
      it.body
    }))
  }
  show heading.where(level: 2): set text(size: 1.25em)
  show heading.where(level: 3): set text(size: 1.08em)

  set math.equation(numbering: "(1)")
  show link: set text(fill: black)

  // Chapter-prefixed numbering. In a caption the numbering function runs at
  // the figure's own location, so reading the heading counter there is right.
  // In a *reference* it runs at the reference site, which silently renders a
  // chapter-3 figure as "Figure 1.1" when cited from chapter 1 -- so
  // references are resolved separately, in the `show ref` rule below.
  set figure(numbering: n => context {
    let c = counter(heading).get()
    let chapter = if c.len() > 0 { c.at(0) } else { 0 }
    [#chapter.#n]
  })

  show ref: it => {
    let el = it.element
    if el == none or el.func() != figure or el.numbering == none {
      return it
    }
    // Resolve both halves of the number where the figure is, not where the
    // sentence citing it happens to sit.
    let loc = el.location()
    let chapter = counter(heading).at(loc).at(0, default: 0)
    let n = counter(figure.where(kind: el.kind)).at(loc).at(0, default: 0)
    link(loc, [#el.supplement #chapter.#n])
  }
  // Algorithms carry their caption above the body, as algorithm2e does.
  show figure.where(kind: "algorithm"): set figure.caption(position: top)
  show figure.caption: it => block(width: 92%, align(left, {
    set text(size: 0.92em)
    set par(justify: true)
    strong[#it.supplement #context it.counter.display(it.numbering).: ]
    it.body
  }))

  set table(stroke: none)
  set raw(tab-size: 2)
  // Isabelle's DejaVu build, vendored under assets/fonts: stock DejaVu Sans
  // Mono has no glyph for \<And> and friends, and a missing glyph inside a
  // theorem statement is a wrong page, not a cosmetic problem. It is DejaVu
  // plus the extra symbols, so ordinary listings are unaffected.
  show raw: set text(font: ("Isabelle DejaVu Sans Mono", "DejaVu Sans Mono"))

  // ------------------------------------------------------------- cover ----
  set align(center)
  v(3.5cm)
  image(logo, width: 4cm)
  v(5mm)
  text(size: 1.5em)[SCHOOL OF COMPUTATION, INFORMATION AND TECHNOLOGY]
  v(4mm)
  text(size: 1.1em)[DER TECHNISCHEN UNIVERSITÄT MÜNCHEN]
  v(24mm)
  text(size: 1.25em)[#doctype in #study-program]
  v(20mm)
  text(size: 1.9em, weight: "bold", title)
  v(15mm)
  text(size: 1.5em, author)
  pagebreak(to: "odd")

  // --------------------------------------------------------- title page ---
  v(1cm)
  image(logo, width: 4cm)
  v(5mm)
  text(size: 1.5em)[SCHOOL OF COMPUTATION, INFORMATION AND TECHNOLOGY]
  v(4mm)
  text(size: 1.1em)[DER TECHNISCHEN UNIVERSITÄT MÜNCHEN]
  v(24mm)
  text(size: 1.25em)[#doctype in #study-program]
  v(18mm)
  text(size: 1.4em, weight: "bold", title)
  v(8mm)
  text(size: 1.4em, weight: "bold", title-de)
  v(12mm)
  table(
    columns: 2, align: (right, left), column-gutter: 1em, row-gutter: 0.8em,
    text(size: 1.15em)[Author:],     text(size: 1.15em)[#author],
    text(size: 1.15em)[Supervisor:], text(size: 1.15em)[#supervisor],
    text(size: 1.15em)[Advisors:],   text(size: 1.15em)[#advisors.join(" & ")],
    text(size: 1.15em)[Date:],       text(size: 1.15em)[#date],
  )
  pagebreak(to: "odd")

  // --------------------------------------------------------- disclaimer ---
  set align(left)
  v(0.62fr)
  [I confirm that this #lower(doctype) is my own work and I have documented
   all sources and material used.]
  v(15mm)
  [Munich, #date #h(5cm) #author]
  v(0.38fr)
  pagebreak(to: "odd")

  // ------------------------------------------------------- front matter ---
  set page(numbering: "i")
  counter(page).update(1)

  body
}

// Switch from roman front matter to arabic main matter.
#let main-matter() = {
  pagebreak(to: "odd")
  set page(numbering: "1")
  counter(page).update(1)
}
