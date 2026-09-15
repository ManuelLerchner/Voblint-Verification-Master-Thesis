#import "lib/tum.typ": thesis
#import "lib/theorems.typ": thm-counter
#import "@preview/glossarium:0.5.10": make-glossary, print-glossary, register-glossary
#import "lib/glossary.typ": entries as glossary-entries

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

// Theorem numbering restarts at every chapter.
#show heading.where(level: 1): it => {
  thm-counter.update(0)
  it
}

// Front matter chapters are unnumbered.
#set heading(numbering: none)

#include "content/acknowledgements.typ"
#include "content/abstract.typ"

#outline(depth: 2)

// ------------------------------------------------------------ main matter --
#pagebreak(to: "odd")
#set page(numbering: "1")
#counter(page).update(1)
#set heading(numbering: "1.1")
#counter(heading).update(0)

#include "content/01-introduction.typ"
#include "content/02-background.typ"
#include "content/03-gallery.typ"

// -------------------------------------------------------------- back matter -
#set heading(numbering: none)
#pagebreak(to: "odd")
#outline(title: [List of Figures], target: figure.where(kind: image))
#outline(title: [List of Tables], target: figure.where(kind: table))

#pagebreak(to: "odd")
= Glossary <glossary>
#print-glossary(glossary-entries)

#pagebreak(to: "odd")
#bibliography("literature.bib", style: "assets/alpha-plain.csl")
