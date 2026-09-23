#import "@preview/rich-counters:0.2.2": rich-counter
#import "@preview/hydra:0.6.3": hydra
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

// Page geometry and typography of the TUM Informatics thesis template (KOMA
// scrbook, 11pt, Computer Modern), measured from a thesis typeset with it
// rather than transcribed from its sources: text block, running heads, the
// sans-serif headings with KOMA's trailing-period numbering, the cover, the
// bilingual title page and the disclaimer. Every length below is in points on
// A4 and names the position it reproduces.

//
// The fonts are Latin Modern, the OpenType release of Computer Modern with the
// same metrics and design sizes, vendored under assets/fonts. Typst does no
// optical sizing, so each use names the design size LaTeX would scale:
// Roman 17 for the cover's 20.74pt lines, Roman 12 bold for the titles and the
// centred front-matter headings, Roman 12 for 14.4pt, Roman 10 for the text.

#let serif = "Latin Modern Roman"
#let serif-12 = "Latin Modern Roman 12"
#let serif-17 = "Latin Modern Roman 17"
#let sans = "Latin Modern Sans"

// The text block: 431.8pt wide, from 89.9pt on an odd page's inner edge; the
// first baseline at 113pt and the last at 722.5pt.
#let margin-top = 101.5pt
// Typst measures a line from the cap height, so a line of size S is 0.685S
// tall and the leading is what the baseline pitch leaves over.
#let leading-for(pitch, size) = pitch - 0.685 * size
#let margin-bottom = 115pt
// One-sided: the TUM two-sided margins (89.9pt inside, 73.6pt outside)
// averaged, so the text width is unchanged.
#let margin-inside = 81.75pt
#let margin-outside = 81.75pt
#let rule = 0.4pt

// The running head sits above a rule at 81.9pt and shows the chapter, in
// italics; a chapter's first page has none. The page number sits below a rule
// at 759.4pt, on the right.
#let opener-page(pg) = query(heading.where(level: 1)).any(h => h.location().page() == pg)

#let running-head() = context {
  let pg = here().page()
  if opener-page(pg) {
    return
  }
  // hydra supplies the candidates; the filters pick KOMA's mark: the first
  // heading of the level that starts on this page, otherwise the last one
  // before it, and for a section only while its chapter is the current one.
  // Front-matter chapters and part dividers carry no mark.
  let marks = h => h != none and h.numbering != none and h.supplement != [Part]
  let mark = (ctx, cand) => {
    numbering(cand.numbering, ..counter(heading).at(cand.location()))
    h(0.5em)
    cand.body
  }
  let level = 1
  let title = hydra(
    level,
    prev-filter: (ctx, cands) => cands.primary.next == none and marks(cands.primary.prev),
    next-filter: (ctx, cands) => marks(cands.primary.next),
    display: mark,
    skip-starting: false,
  )
  set text(style: "italic")
  block(width: 100%, below: 0pt, {
    if title != none {
      align(right, title)
    } else {
      v(1.2em)
    }
    v(0.5pt)
    line(length: 100%, stroke: rule)
  })
}

#let running-foot() = context {
  let pg = here().page()
  // A part divider is a bare page, as in KOMA's empty page style; a chapter's
  // first page keeps its number.
  if query(heading.where(level: 1, supplement: [Part])).any(h => h.location().page() == pg) {
    return
  }
  stack(dir: ttb, spacing: 3.2pt, line(length: 100%, stroke: rule), if page.numbering != none {
    align(right, counter(page).display(page.numbering))
  })
}

// A front-matter chapter (acknowledgements, abstract): a centred serif title
// with its baseline at 195pt and the text from 248.6pt, under an empty head.
#let front-chapter(body) = {
  show heading.where(level: 1): it => {
    pagebreak(weak: true)
    // Tighter than the TUM LaTeX template (83.5pt / 40.2pt) so the abstract
    // fits on one page.
    v(4pt)
    align(center, text(font: serif-12, size: 14.4pt, weight: "bold", it.body))
    v(8pt)
  }
  body
}

#let thesis(
  title: "",
  title-de: "",
  doctype: "Master's Thesis",
  study-program: "Informatics",
  author: "",
  supervisor: "",
  examiner: "",
  date: "",
  logo: "../assets/tumlogo.svg",
  body,
) = {
  set document(title: title, author: author)

  set page(
    paper: "a4",
    margin: (
      inside: margin-inside,
      outside: margin-outside,
      top: margin-top,
      bottom: margin-bottom,
    ),
    binding: left,
    numbering: none,
  )
  // Symbols the text face lacks (primes, arrows) come from the math face, as
  // they would in LaTeX, rather than from an unrelated fallback font.
  set text(font: (serif, "Latin Modern Math"), size: 11pt, lang: "en")
  // 13.55pt between baselines, paragraphs marked by a 1em indent, not a gap.
  set par(justify: true, leading: 6pt, spacing: 6pt, first-line-indent: 11pt)
  set heading(numbering: "1.1.")

  // A reference to a top-level heading says "Chapter", not "Section". Typst's
  // default supplement is "Section" at every level, which silently mislabels
  // every cross-chapter reference.
  show heading.where(level: 1): set heading(supplement: [Chapter])

  // Headings are set ragged right and never hyphenated, as KOMA sets them.
  show heading: set par(justify: false)
  show heading: set text(hyphenate: false)

  // Chapter titles: 20.74pt sans bold with the baseline at 169.4pt, the number
  // set off by an em, the first line of text 36pt below.
  show heading.where(level: 1): it => {
    pagebreak(weak: true)
    counter(figure.where(kind: image)).update(0)
    counter(figure.where(kind: table)).update(0)
    counter(figure.where(kind: "algorithm")).update(0)
    v(53.4pt)
    block(below: 28.7pt, text(font: sans, size: 20.74pt, weight: "bold", {
      if it.numbering != none {
        counter(heading).display(it.numbering)
        h(0.75em)
      }
      it.body
    }))
  }
  show heading.where(level: 2): it => block(
    above: 25pt,
    below: 14.5pt,
    text(font: sans, size: 14.4pt, weight: "bold", {
      if it.numbering != none {
        counter(heading).display(it.numbering)
        h(0.5em)
      }
      it.body
    }),
  )
  show heading.where(level: 3): it => block(
    above: 22pt,
    below: 10.8pt,
    text(font: sans, size: 12pt, weight: "bold", {
      if it.numbering != none {
        counter(heading).display(it.numbering)
        h(0.5em)
      }
      it.body
    }),
  )

  // Display equations are unnumbered, as with LaTeX's `\\[ \\]`: the grammars and
  // definitions here fill the line and nothing refers to them by number.
  set math.equation(numbering: none)
  show math.equation: set text(font: "Latin Modern Math")
  show link: set text(fill: black)

  // Chapter-prefixed numbering. In a caption the numbering function runs at
  // the figure's own location, so reading the heading counter there is right.
  // In a *reference* it runs at the reference site, which silently renders a
  // chapter-3 figure as "Figure 1.1" when cited from chapter 1 -- so
  // references are resolved separately, in the `show ref` rule below.
  let chapter-number(loc) = {
    let c = counter(heading).at(loc).at(0, default: 0)
    let chapters = query(heading.where(level: 1).before(loc))
    let h = chapters.last(default: none)
    if h != none and type(h.numbering) == str and h.numbering.starts-with("A") {
      numbering("A", c)
    } else {
      str(c)
    }
  }
  set figure(numbering: n => context [#chapter-number(here()).#n])

  show ref: it => {
    let el = it.element
    if el == none or el.numbering == none {
      return it
    }
    let loc = el.location()
    // A heading is numbered "3.1." on the page and in the contents, as KOMA
    // does, but a reference to it reads "Section 3.1".
    if el.func() == heading {
      let pattern = if type(el.numbering) == str { el.numbering.trim(".", at: end) } else {
        el.numbering
      }
      let in-appendix = type(el.numbering) == str and el.numbering.starts-with("A")
      let supplement = if in-appendix and el.level == 1 { [Appendix] } else { el.supplement }
      return link(loc, [#supplement #numbering(pattern, ..counter(heading).at(loc))])
    }
    if el.func() != figure {
      return it
    }
    // Resolve both halves of the number where the figure is, not where the
    // sentence citing it happens to sit.
    let chapter = chapter-number(loc)
    // A subpar part is the only unlisted figure. Its own counter may be of
    // another kind (a listing inside an image figure), so it takes the number
    // of the enclosing figure and its position among the parts.
    if el.outlined == false {
      let parent = query(figure.where(kind: image, outlined: true).before(loc)).last()
      let n = counter(figure.where(kind: image)).at(parent.location()).first()
      let sub = counter("__subpar:sub-figure-counter").at(loc).first() + 1
      return link(loc, [#el.supplement #chapter.#n#numbering("a", sub)])
    }
    let n = counter(figure.where(kind: el.kind)).at(loc).at(0, default: 0)
    link(loc, [#el.supplement #chapter.#n])
  }
  // Algorithms carry their caption above the body, as algorithm2e does.
  show figure.where(kind: "algorithm"): set figure.caption(position: top)
  show figure.caption: it => block(width: 92%, align(left, {
    set text(size: 0.92em)
    set par(justify: true)
    strong[#it.supplement #context it.counter.display(it.numbering): ]
    it.body
  }))
  // KOMA's \textfloatsep and \intextsep: a float or an in-text figure stands
  // 18pt clear of the text around it, so a caption never sits on the next
  // paragraph. A subfigure starts its grid cell, where weak spacing vanishes.
  set place(clearance: 18pt)
  show figure: it => if it.placement == none {
    v(14pt, weak: true)
    it
    v(18pt, weak: true)
  } else { it }

  // The contents, as KOMA sets it: chapters in bold sans without leaders,
  // sections and subsections in serif with dot leaders, numbers in fixed
  // columns (16.4pt for a chapter, then 34.2pt and 31.4pt), 11pt of air above
  // each chapter line.
  show outline.entry: it => {
    let el = it.element
    if el.func() == figure and el.numbering != none {
      let loc = el.location()
      let chapter = chapter-number(loc)
      let n = counter(figure.where(kind: el.kind)).at(loc).at(0, default: 0)
      // The list is rendered after the chapters; resolve at the figure itself.
      return link(loc, it.indented([#el.supplement #chapter.#n], it.inner()))
    }
    if el.func() != heading {
      return it
    }
    let indent = (0pt, 16.4pt, 50.6pt).at(it.level - 1)
    let numw = (16.4pt, 34.2pt, 31.4pt).at(it.level - 1)
    let prefix = it.prefix()
    let row = {
      h(indent)
      if prefix != none {
        box(width: numw, prefix)
      }
      it.body()
      if it.level == 1 {
        h(1fr)
      } else {
        h(0.5em)
        box(width: 1fr, repeat(gap: 0.55em)[.])
        h(0.5em)
      }
      it.page()
    }
    if it.level == 1 {
      block(above: 14pt, below: 0pt, link(el.location(), text(font: sans, weight: "bold", row)))
    } else {
      block(above: 6.05pt, below: 0pt, link(el.location(), row))
    }
  }

  set table(stroke: none, align: left)
  // A narrow cell cannot be justified without rivers or forced breaks.
  show table.cell: set par(justify: false)
  show table.cell: set text(hyphenate: false)
  set raw(tab-size: 2)
  // Isabelle's DejaVu build, vendored under assets/fonts: stock DejaVu Sans
  // Mono has no glyph for \<And> and friends, and a missing glyph inside a
  // theorem statement is a wrong page, not a cosmetic problem. It is DejaVu
  // plus the extra symbols, so ordinary listings are unaffected.
  show raw: set text(font: ("Isabelle DejaVu Sans Mono", "DejaVu Sans Mono"))
  // One size for every listing, in running text or inside a figure: Typst's
  // default scales raw text with its surroundings (6.4pt in an 8pt figure).
  show raw.where(block: true): set text(size: 8pt)

  // ------------------------------------------------------------- cover ----
  // Positions are the glyph tops the template produces: logo 102pt, school
  // 187pt, thesis kind 327pt, title 404pt, author 513pt; 25pt between the
  // baselines of a two-line school name or title.
  // The cover is centred on the page, the title page on the text block, so
  // the cover's content is shifted left by half the margin difference.
  let head-block(logo-top: 0pt, dx: 0pt) = {
    place(top + center, dx: dx, dy: logo-top, image(logo, width: 4cm))
    place(top + center, dx: dx, dy: logo-top + 85.2pt, block(width: 100%, {
      set par(justify: false, leading: leading-for(25pt, 20.74pt))
      text(font: serif-17, size: 20.74pt)[SCHOOL OF COMPUTATION, INFORMATION AND TECHNOLOGY]
    }))
    place(top + center, dx: dx, dy: logo-top + 144.1pt, text(
      font: serif-12,
      size: 12pt,
    )[DER TECHNISCHEN UNIVERSITÄT MÜNCHEN])
    place(top + center, dx: dx, dy: logo-top + 225.1pt, text(
      font: serif-12,
      size: 14.4pt,
    )[#doctype in #study-program])
  }
  set align(center)
  let cover-dx = -(margin-inside - margin-outside) / 2
  head-block(logo-top: 102pt - margin-top, dx: cover-dx)
  place(top + center, dx: cover-dx, dy: 404pt - margin-top, block(width: 100%, {
    set par(justify: false, leading: leading-for(25pt, 20.74pt))
    text(font: serif-12, size: 20.74pt, weight: "bold", title)
  }))
  place(top + center, dx: cover-dx, dy: 513pt - margin-top, text(
    font: serif-17,
    size: 17.28pt,
    author,
  ))
  pagebreak(weak: true)

  // --------------------------------------------------------- title page ---
  head-block(logo-top: 102pt - margin-top)
  place(top + center, dy: 395pt - margin-top, block(width: 100%, {
    set par(justify: false, leading: leading-for(17.3pt, 17.28pt))
    text(font: serif-12, size: 17.28pt, weight: "bold", title)
  }))
  place(top + center, dy: 456pt - margin-top, block(width: 100%, {
    set par(justify: false, leading: leading-for(17.3pt, 17.28pt))
    text(font: serif-12, size: 17.28pt, weight: "bold", title-de)
  }))
  place(top + left, dx: 51.2pt, dy: 517pt - margin-top, {
    set text(font: serif-12, size: 14.4pt)
    set align(left)
    table(
      columns: (80.7pt, auto),
      align: (left, left),
      inset: 0pt,
      row-gutter: leading-for(20pt, 14.4pt),
      [Author:], [#author],
      [Supervisor:], [#supervisor],
      [Examiner:], [#examiner],
      [Date:], [#date],
    )
  })
  pagebreak(weak: true)

  // --------------------------------------------------------- disclaimer ---
  set align(left)
  place(top + left, dy: 553pt - margin-top, {
    set par(first-line-indent: 0pt)
    [I confirm that this #lower(doctype) is my own work and I have documented
      all sources and material used.]
    v(56.5pt)
    [Munich, #date]
  })
  place(top + left, dx: 237.5pt, dy: 553pt + 2 * 13.55pt + 56.5pt - margin-top, [#author])
  pagebreak(weak: true)

  // ------------------------------------------------------- front matter ---
  set page(
    numbering: "i",
    header: running-head(),
    footer: running-foot(),
    header-ascent: margin-top - 81.8pt,
    footer-descent: 759.9pt - (841.89pt - margin-bottom),
  )
  counter(page).update(1)

  body
}

// Switch from roman front matter to arabic main matter.
#let main-matter() = {
  pagebreak(weak: true)
  set page(numbering: "1")
  counter(page).update(1)
}
