#import "lib/tum.typ": front-chapter, thesis
#import "lib/theme.typ": vb
#import "lib/code.typ": isabelle-scripts
#import "@preview/codly:1.3.0": codly, codly-init
#import "lib/theorems.typ": thm-counter
#import "lib/figures.typ": part, part-outline-entry
#import "@preview/glossarium:0.5.10": make-glossary, print-glossary, register-glossary
#import "lib/glossary.typ": entries as glossary-entries, print-thesis-glossary

#show: make-glossary
#register-glossary(glossary-entries)

#show: thesis.with(
  title: "Voblint: Towards a Verified Goblint-style Analysis Pipeline in Isabelle/HOL",
  title-de: "Voblint: Hin zu einer verifizierten Analyse-Pipeline im Stil von Goblint in Isabelle/HOL",
  doctype: "Master's Thesis",
  study-program: "Informatics",
  author: "Manuel Lerchner",
  supervisor: "Alexandra Graß & Helmut Seidl",
  examiner: "Francisco Javier Esparza Estaun",
  date: "01.12.2026",
)

// Listings: codly draws the frame and the line numbers for every raw block,
// so lib/code.typ hands it bare `raw` content. A language tag names what a
// block is in the thesis's terms, not the highlighter's: the VIMP programs
// are highlighted as C.
#show: codly-init.with()
#codly(
  zebra-fill: none,
  fill: vb.bg,
  stroke: 0.7pt + vb.frame,
  radius: 3pt,
  display-icon: false,
  // Tighter than codly's 0.32em rows: a 13-line program should not take a
  // third of a page.
  inset: (x: 0.32em, y: 0.2em),
  number-format: n => text(fill: vb.muted, size: 0.75em, str(n)),
  // The tag sits inside the frame, clear of its top and right edges.
  lang-inset: (x: 0.4em, y: 0.12em),
  lang-outset: (x: -0.25em, y: 0em),
  // One-line programs are only one row tall; a full-size tag would overflow.
  lang-format: (lang, icon, color) => box(
    radius: 2pt,
    fill: color.lighten(80%),
    stroke: 0.5pt + color,
    inset: (x: 0.4em, y: 0.12em),
    text(size: 0.78em, fill: color.darken(20%), lang),
  ),
  languages: (
    c: (name: "VIMP", color: vb.keyword),
    isabelle: (name: "Isabelle", color: vb.accent),
    ocaml: (name: "OCaml", color: vb.trusted),
  ),
)

#show raw.where(lang: "isabelle"): isabelle-scripts

// Theorem numbering restarts at every chapter.
#show heading.where(level: 1): it => {
  thm-counter.update(0)
  it
}

// Front matter chapters are unnumbered.
#set heading(numbering: none)

#front-chapter({
  include "content/acknowledgements.typ"
  include "content/abstract.typ"
  include "content/ai-use.typ"
})

#show outline.entry.where(level: 1): part-outline-entry
// The template leaves 11pt more between the title and the first entry than
// between a chapter title and its text.
#heading(outlined: false)[Contents]
#v(10.9pt)
#outline(title: none, depth: 2)

// ------------------------------------------------------------ main matter --
#pagebreak(weak: true)
#set page(numbering: "1")
#counter(page).update(1)
#set heading(numbering: "1.1.")
#counter(heading).update(0)

#part("The Problem", lbl: <part:problem>)
#include "content/01-introduction.typ"
#include "content/02-background.typ"

#part("What Must Be Over-Approximated", lbl: <part:over-approx>)
#include "content/03-program-model.typ"
#include "content/04-traces.typ"

#part("The Analyzer", lbl: <part:analyzer>)
#include "content/05-domains.typ"
#include "content/06-analysis-interface.typ"
#include "content/07-equations.typ"
#include "content/08-solving.typ"
#include "content/09-results.typ"

#part("Instances and Practice", lbl: <part:instances>)
#include "content/10-instances.typ"
#include "content/11-executable.typ"
#include "content/12-evaluation.typ"

#part("Assessment", lbl: <part:assessment>)
#include "content/13-related.typ"
#include "content/14-conclusion.typ"

// Appendices retain stable labels while using a separate alphabetic counter.
#set heading(numbering: "A.1.")
#counter(heading).update(0)
#include "content/appendices.typ"

// -------------------------------------------------------------- back matter -
#set heading(numbering: none)
#pagebreak(weak: true)
#outline(title: [List of Figures], target: figure.where(kind: image))
#outline(title: [List of Tables], target: figure.where(kind: table))

#pagebreak(weak: true)
= Glossary <glossary>
#print-thesis-glossary(print-glossary)

#pagebreak(weak: true)
#bibliography("literature.bib", style: "assets/plain-numeric.csl")

// The figure gallery is a working reference, not thesis content: one instance
// of every figure kind, with placeholder payloads. It sits after the
// bibliography while drafting and is deleted before submission.
#pagebreak(weak: true)
#include "content/03-gallery.typ"
