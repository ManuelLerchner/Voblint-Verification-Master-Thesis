# Paper

A conference paper derived from the Voblint thesis, targeting ITP 2027
(LIPIcs, 16 pages excluding references, no appendix). Status: **complete draft**, not yet submitted.

```text
paper/
  main.tex                 LIPIcs document
  latexmkrc                adds lipics/ and sty/ to TEXINPUTS, builds into _build/
  macros.tex               notation; one macro per concept
  sections/                one file per section, in reading order
  snippets.txt             Isabelle declarations and theorems the paper shows
  generated/               derived from thesis sources; never edit by hand
    *.tex                  snippets rendered with isabelle.sty
    references.bib         the cited subset of thesis/literature.bib
    stats.tex              \stat{key} from thesis stats.json and profiling.json (not committed)
    contexts.tex           context-policy table from the ctx-mutual-* claims
    scale.tex              per-layer size table from scripts/pages_stats.py
    costs.tex              per-policy solve cost from the committed profiling snapshot
  tools/
    snippets.py            thesis snippet -> LaTeX (--write / --check)
    bib.py                 cited keys -> references.bib (--write / --check)
    stats.py               stats.json, profiling.json -> \stat macros
    contexts.py            ctx-mutual-* claims -> context-policy table
    scale.py               per-layer statistics -> size table (needs the pixi env)
    costs.py               profiling snapshot -> per-policy cost table
  lipics/                  lipics-v2021 class (Dagstuhl, LPPL), vendored
  sty/                     isabelle.sty, isabellesym.sty (Isabelle2025-2), vendored
  OUTLINE.md               section plan, page budget, cut list
  STYLEGUIDE.md            venue format and writing rules
  research/                related-paper survey and venue/writing research
  reviews/                 simulated journal reviews, meta-review, response
```

## Build

```sh
pixi run paper-generated   # after adding a snippet or citation
pixi run paper             # checks drift, then builds paper/_build/main.pdf
```

LaTeX comes from the system TeX Live (`latexmk`, `pdflatex`), not from pixi.
`\stat{...}` reads `thesis/shared/generated/stats.json`, which every thesis
build writes; run `pixi run thesis-draft` first on a fresh checkout.

## Rules

- No new claims. Every statement traces to a theorem in `src/` or a section
  of `thesis/content/`; the repository `CLAUDE.md` claim discipline applies.
- Theorem statements shown verbatim come from `snippets.txt`, never retyped.
  Add a name there (it must exist in `thesis/shared/snippets.toml`), then run
  `pixi run paper-generated`.
- Citations must exist in `thesis/literature.bib`. `bib.py` fails otherwise.
- Repository numbers go through `\stat{key}`.
- Isabelle names in prose use `\isaname{...}`.

## Before submission

- ITP review is lightweight double-blind: add `anonymous` to the class
  options, drop `\relatedversiondetails`, `\supplementdetails` and the
  acknowledgements, and upload a scrubbed archive as supplementary material.
- Decide co-authorship (the thesis supervisors are only acknowledged).
