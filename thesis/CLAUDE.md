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
| `thesis-snippets` | a declaration or theorem statement shown with `thy`/`proved` no longer matches its source text |
| `thesis-facts` | a fact in `shared/facts.toml` is not proved by the built session, its printed statement changed, or a `proved` snippet comes from another theory than the one proving it |
| `thesis-claims` | quoted analyzer output no longer matches the analyzer |
| `thesis-figures` | an SVG extracted from the explainer drifted |
| `thesis-playground` | a README playground figure, its program or its link no longer matches `docs/images` and `docs/readme-figures` (`shared/playground-figures.toml` lists them; `playground-figure(name, caption)` places one) |
| `thesis-stats` | `shared/generated/stats.json` no longer matches what `scripts/pages_stats.py` measures (`thesis-stats-write` regenerates it), or a line of `content/` naming lines, theories, files, sessions, fixtures, cases or lemmas carries a number outside `stat()` and outside the commented `ALLOW` list in `tools/stats.py` |
| `thesis-alignment` | `shared/generated/goblint-alignment.json` no longer matches the `align-list` rows of `pages/index.html`, which appendix C renders (`thesis-alignment-write` refreshes it; edit the page, never the JSON) |
| `thesis-notation` | `shared/generated/notation.json`, the README's Notation block or the explainer's legend no longer matches the declarations in the theories, a declaration changed shape, or a symbol's anchor is missing from the rendered theories (`thesis-notation-write` refreshes all three; edit `shared/notation.toml` or the theories, never the output) |
| `thesis-vimp` | a VIMP listing's playground link does not decode to the program it shows, names a setting the playground lacks, is missing from the PDF's link annotations, or runs a claimed or fixture program at other settings; or VIMP code reaches the document outside `listing(lang: "c")` (`thesis-vimp-source` is the no-build part; `thesis-vimp-write` refreshes `shared/generated/vimp-claims.json`) |

Never write an Isabelle name in backticks or plain text. Wrap it, so it is
checked, coloured and linked:

| Helper | For | Colour |
| --- | --- | --- |
| `isaconst`, `isathm`, `isatype`, `isalocale` | constants, facts, types, locales | blue, green, purple, teal |
| `oblig("INIT")` | a named assumption of `ltr_coverage` (`of:` for another locale) | teal small capitals |
| `ctor("Root")` | a datatype constructor in notation | purple sans |
| `keyw("while")` | a VIMP keyword in notation | maroon bold |
| `isai("a \<le> b")`, `isa(```…```)` | inline and block Isabelle, ASCII symbols decoded | listing |
| `thy("name")` | a declaration lifted verbatim from the theories (`shared/snippets.toml`) | listing |
| `listing(```…```, lang: "c")` | a VIMP program, linked to the playground by its `VIMP ↗` tag; `claim: "name"` opens that claim's fixture at its settings (required when showing a claimed or fixture program at non-default settings, and for an excerpt), `program:` the whole program a split listing belongs to, `analysis:`/`globals:`/`ctx:`/`k:` override the playground defaults | listing |
| `proved("name", note: [...])` | a theorem statement: its source `assumes`/`shows` header without the proof, listed in both `snippets.toml` and `facts.toml` | listing |
| `fixture("group/kind/NN-name.vimp", label: …)` | a regression fixture named in prose, linked to its file under `tests/regression` on GitHub; `thesis-vimp-source` fails on a missing file or a backticked `.vimp` path without the helper | text |
| `stat("corpus.cases")`, `stat-sum(..)`, `stat-percent(part, whole)`, `stat-keys(prefix)` | a repository figure (line counts, theory files, corpus sizes) from `lib/stats.typ`, grouped as `62,098`; an unknown key fails the build. Never type such a number. Write `#stat("k")\;` before a semicolon, which would otherwise end the call | text |

A formal citation whose link the map cannot resolve fails the build. Regenerate
the map and run `pixi run thesis-links`; do not replace it with plain text.
This includes generated snippets/statements and session/theory references.
Theorem environments take `isa: "name"` and print it,
linked, in the header: `Definition 3.1 (Expressions, exp).`

## Scope: an overview of the formalization

The Isabelle formalization is the contribution. The thesis is its overview: it
gives context, the mathematical background the reader needs, the design
choices and why they were made, and the results with their exact boundary.

- Do not rephrase Isabelle proofs. No case-by-case proof walkthroughs, no lemma
  inventories, no prose reconstruction of an induction. Cite the theorem
  (linked) and, where a proof has one, name the key idea in a sentence or two.
- A theorem appears when the reader needs its statement to follow the argument.
  Supporting lemmas stay in the theories.
- Prefer a design choice with its rejected alternative over a description of
  the construction's internals.
- When in doubt, shorten and link.

## Notation is frozen

One notation serves the theories and the thesis; it is declared in the
theories and rendered from `shared/generated/notation.json`. Global notation
covers semantic concepts only (execution, simulation, concretization,
evaluation, the trace and collecting sets); locale-local abbreviations cover
repeated proof plumbing and introduce no constants. Add new notation only for a
central semantic concept that occurs prominently in theorem statements and
reads clearly better as a symbol. Never add a thesis-only symbol for an
Isabelle object; write its name with the checked helpers.

## Motivated exposition

The Isabelle development already establishes that the results hold. The thesis
explains what exactly holds, why that statement is the right one, and why each
definition is needed (Tao's "digestion", Sanderson's "motivated explanation").

- Introduce a substantial definition only after the reader has met the problem
  it solves. Per abstraction: state the desired property, show the simpler
  construction and where it fails (one equation, figure or small program),
  then give the abstraction as the minimal fix and its formal definition.
- Open a section with the question it answers, never with an Isabelle
  identifier. The identifier anchors the idea after the idea is on the page.
- Keep the staging short: motivation 2-5 paragraphs, one failed model, a crisp
  definition, the consequence that matters, the pointer to what it forces next.
  No pages of simulated false starts; the reconstruction need not be historical.
- Organize by the dependency of ideas, justify by the dependency of proofs.
- State each limitation once, where it bites. Do not attach a "this does not
  establish ..." sentence to every paragraph; collect scope qualifications in
  the trust-boundary and limitations sections and reference them.
- Acceptance test for every section: the author could explain it at the
  defense without notes or AI assistance. If a passage only restates an
  Isabelle name, it is not finished.

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
- Listings go through `codly`: `listing(lang: "c")` for VIMP (shown as VIMP,
  never a bare ```` ```c ```` block or `raw(lang: "c")`, which carry no
  playground link), `isa` for Isabelle, `lang: "ocaml"` for generated code. The frame and line
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
