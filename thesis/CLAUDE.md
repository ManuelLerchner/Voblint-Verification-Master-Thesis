# Thesis conventions

Typst-specific rules for everything under `thesis/`. The project contract in
`../.claude/CLAUDE.md` still applies; `docs/THESIS_BLUEPRINT.md` is the plan
the chapters are written from, and `README.md` here explains the tooling's
purpose. This file is what to follow when editing.

## Build and check

```sh
pixi run thesis-typst          # the build: warnings are errors
pixi run thesis-draft          # same, warnings allowed while drafting
pixi run thesis-watch          # live rebuild
pixi run typst-format          # typstyle, 100 columns
pixi run thesis-check          # every drift check below
```

Every `.typ` edit ends with `thesis-typst` green and `typst-format-check`
clean. The checks that keep the text honest, and what each one reads:

| Task | Fails when |
| --- | --- |
| `thesis-refs` | an `isa*("…")` or `isa: "…"` names nothing in the theories, cites the wrong kind, or a declared multi-word name (`valid_ltr`, `EA_Assign`) is written as prose without markup |
| `thesis-links` | a name the markup links has no anchor in the rendered theories (`--write` regenerates `shared/generated/links.json`; `--live` checks the deployed pages) |
| `thesis-snippets`, `thesis-facts`, `thesis-claims` | a quoted definition, theorem statement or analyzer output no longer matches the sources |
| `thesis-figures` | an SVG extracted from the explainer drifted |
| `thesis-playground` | a README playground figure, its program or its link no longer matches `docs/images` and `docs/readme-figures` (`shared/playground-figures.toml` lists them; `playground-figure(name, caption)` places one) |

Never write an Isabelle name in backticks or plain text. Wrap it, so it is
checked, coloured and linked:

| Helper | For | Colour |
| --- | --- | --- |
| `isaconst`, `isathm`, `isatype`, `isalocale` | constants, facts, types, locales | blue, green, purple, teal |
| `oblig("INIT")` | a named assumption of `ltr_coverage` (`of:` for another locale) | teal small capitals |
| `ctor("Root")` | a datatype constructor in notation | purple sans |
| `keyw("while")` | a VIMP keyword in notation | maroon bold |
| `isai("a \<le> b")`, `isa(```…```)` | inline and block Isabelle, ASCII symbols decoded | listing |

A name whose link the map cannot resolve renders in plain grey: colour on the
page means "click here". Theorem environments take `isa: "name"` and print it,
linked, in the header: `Definition 3.1 (Expressions, exp).`

## Typography

The template reproduces the TUM Informatics LaTeX thesis (KOMA scrbook, 11pt),
measured from a document typeset with it. `lib/tum.typ` holds every length in
points and names the position it reproduces; change a number there, not the
element that reads it.

- Fonts are Latin Modern, vendored in `assets/fonts` (the OpenType release of
  Computer Modern, same metrics and design sizes). Typst does no optical
  sizing, so each use names the design size LaTeX would scale: Roman 17 for
  the cover's 20.74pt lines, Roman 12 bold for titles, Roman Caps for small
  capitals, Sans bold for headings. Symbols the text face lacks come from
  Latin Modern Math, listed as the fallback.
- Headings are sans, ragged, unhyphenated, numbered `3.1.`; a reference to
  one reads "Section 3.1". Parts are `#part("Title")`, bare pages that do not
  step the chapter counter.
- Running heads come from `hydra`, filtered to KOMA's mark rule: the first
  section starting on the page, else the last before it; chapter on even
  pages, section on odd; none on openers, parts and front matter.
- Paragraphs are marked by a 1em indent, not a gap. Display equations are
  unnumbered; nothing is referenced by equation number.
- Listings go through `codly`: `listing(lang: "c")` for VIMP (shown as VIMP),
  `isa` for Isabelle, `lang: "ocaml"` for generated code. The frame and line
  numbers are codly's; do not wrap a raw block in another block.
- Multi-part figures use `subfigures(...)` (subpar) so each part has its own
  label; plots use lilaq; diagrams use fletcher and commute; proof trees use
  curryst. Colours come from `lib/theme.typ` only.

## Checking a page

Do not judge layout from the source. Render the page and look at it:

```sh
pdftoppm -r 80 -f 21 -l 21 -png thesis/Voblint_Thesis.pdf /tmp/p
pdftotext -f 21 -l 21 -bbox-layout thesis/Voblint_Thesis.pdf -   # glyph positions
pdffonts thesis/Voblint_Thesis.pdf                                 # no Libertinus, no NewCM text
```

A build can succeed with the wrong font (Typst falls back silently on missing
glyphs), so `pdffonts` is part of verifying a typography change. `pdftotext
-bbox-layout` gives the numbers to compare against the reference measurements
recorded in `lib/tum.typ`.
