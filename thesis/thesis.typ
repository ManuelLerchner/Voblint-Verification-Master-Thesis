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
#outline(title: none, depth: 3)

// ------------------------------------------------------------ main matter --
#pagebreak(to: "odd")
#set page(numbering: "1")
#counter(page).update(1)
#set heading(numbering: "1.1.")
#counter(heading).update(0)

#part("The Problem")
#include "content/01-introduction.typ"
#include "content/02-background.typ"

#part("What Must Be Over-Approximated")
#include "content/03-program-model.typ"
#include "content/04-traces.typ"

#part("The Analyzer")
#include "content/05-domains.typ"
#include "content/06-analysis-interface.typ"
#include "content/07-equations.typ"
#include "content/08-solving.typ"
#include "content/09-results.typ"

#part("Instances and Practice")
#include "content/10-instances.typ"
#include "content/11-executable.typ"
#include "content/12-evaluation.typ"

#part("Assessment")
#include "content/13-related.typ"
#include "content/14-conclusion.typ"

// The figure gallery is a working reference, not thesis content: one instance
// of every figure kind, with placeholder payloads. Build it with
// `typst compile --input gallery=1 ...` while drafting; it is never part of the
// document proper, and it is deleted before submission.
#if sys.inputs.at("gallery", default: none) != none {
  include "content/03-gallery.typ"
}

// Appendices retain stable labels while using a separate alphabetic counter.
#set heading(numbering: "A.1.")
#counter(heading).update(0)
#include "content/appendices.typ"

// -------------------------------------------------------------- back matter -
#set heading(numbering: none)
#pagebreak(to: "odd")
#outline(title: [List of Figures], target: figure.where(kind: image))
#outline(title: [List of Tables], target: figure.where(kind: table))

#pagebreak(to: "odd")
= Glossary <glossary>
#print-thesis-glossary(print-glossary)

#pagebreak(to: "odd")
#bibliography("literature.bib", style: "assets/alpha-plain.csl")
