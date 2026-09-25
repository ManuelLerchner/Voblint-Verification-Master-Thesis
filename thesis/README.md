# Thesis

The Voblint thesis, in Typst.

```text
thesis/
  thesis.typ      the document
  lib/            style: palette, notation, figures, code, theorems, sources
  content/        chapters
  assets/         fonts, bibliography style, Isabelle syntax definition, logo
  shared/         inputs and generated material both the tools and the text read
  tools/          the generators that keep the text honest
```

## Build

Everything runs through pixi, including Typst itself -- there is nothing to
install by hand, and CI runs the same commands a working copy does.

```sh
pixi run thesis-typst      # warnings are errors; prints pages and words
pixi run thesis-draft      # same, but warnings do not stop the build
pixi run thesis-watch      # live rebuild
pixi run thesis-generated  # re-extract snippets, claims, theorem statements, figures
pixi run thesis-check      # every drift check
```

`--root` is `thesis/`, so the document reads generated material by absolute
path (`/shared/generated/...`) and Graphviz sources are laid out inside the
document with no build step.

## Why Typst

The one thing that argued for LaTeX was Isabelle's document preparation:
`@{thm foo}` typesets the statement Isabelle actually proved, and the build
fails when `foo` is gone. That guarantee is available here too --
`tools/snippets.py` lifts the statement as the theory writes it and
`tools/facts.py` checks against a built session that the fact is proved, in
that theory -- and it does not require writing prose inside theory files to get
it. A third check with no LaTeX equivalent, `claims.py`, follows from the same
idea.

Everything else was already in Typst's favour: sub-second incremental builds,
errors that name the symbol and suggest the fix, `diagraph` laying out Graphviz
sources inside the document, and `fletcher`/`commute` routing diagrams that
TikZ needs hand-placed coordinates for. And because Typst is a programming
language, the symbol table, the link map and the theorem statements are read
directly rather than preprocessed into an intermediate file.

## The style library

The rule the whole document follows: never write a semantic bracket, a sharp, a
lattice symbol or a figure colour at the call site. Go through the library, so
a notational decision is one edit rather than a hundred.

| File | Holds |
| --- | --- |
| `lib/theme.typ` | the palette; every figure draws from it |
| `lib/math.typ` | notation, grounded in `docs/GLOSSARY.md` |
| `lib/figures.typ` | figure vocabulary: CFG nodes, solver states, trust badges, lattices, simulation squares, iteration plots, algorithms, subfigures |
| `lib/code.typ` | Isabelle/VIMP/OCaml listings, symbol decoding, entity references |
| `lib/sources.typ` | `thy()` and `proved()` -- declarations and theorem statements lifted from the theories |
| `lib/stats.typ` | `stat()` and friends -- repository figures measured by `scripts/pages_stats.py` |
| `lib/theorems.typ` | theorem environments, numbered per chapter |
| `lib/glossary.typ` | the vocabulary the thesis assumes |
| `lib/tum.typ` | page geometry and front matter |

## Keeping the thesis honest

The thesis checks are wired into `pixi run thesis-check`; the reference and
snippet checks also run at commit time.

### `pixi run thesis-refs` -- does this still exist?

Every reference to a real entity goes through a function that also declares its
kind, and `scripts/check_thesis_refs.py` resolves each one against the command
that declares it in the theories:

| call | resolves against |
| --- | --- |
| `isathm("X")` | `lemma` / `theorem` / `corollary` / `proposition` X |
| `isaconst("X")` | `definition` / `fun` / `abbreviation` / `inductive` X, or a record field |
| `isatype("X")` | `datatype` / `type_synonym` / `record` X |
| `isalocale("X")` | `locale` / `class` X |
| `isasession("X")` | a session declared in some ROOT |
| `isacmd("X")` | an Isabelle outer-syntax command |

The kind is the point. A plain "does this identifier occur anywhere" test
passes when a lemma is downgraded to a definition or a locale is replaced by a
record -- so those are reported separately, as deviations rather than as
misses. Unresolved names come with a spelling suggestion.

### `pixi run thesis-snippets` -- is this still what the theory says?

Declarations are cited by **name** in `shared/snippets.toml`, never by line
range, and `tools/snippets.py` lifts each one's source text into
`shared/generated/snippets/`. The name has to resolve, and the extracted text
is committed, so a rename fails and an edit to a shown definition surfaces as a
diff.

A `lemma`, `theorem`, `corollary` or `proposition` is cut at its first proof
command, so a theorem snippet is its `fixes`/`assumes`/`shows` header in the
author's notation. This is the only way the thesis shows a formal statement.

```typst
#thy("numeric_domain")     // the declaration, verbatim, with its file header
#proved("run_voblint_certified_source_sound", note: [...]) // a theorem statement and its linked name
```

Both render as an ordinary codly listing: one frame, line numbers, the
`assets/isabelle.sublime-syntax` highlighting.

### `pixi run thesis-facts` -- is this still what Isabelle proves?

A snippet is source text; it does not show that the build accepted the proof.
`shared/facts.toml` lists the theorems the thesis cites as results;
`tools/facts.py` starts the built session and asks Isabelle for each one's
statement and the theory that proves it, stored in
`shared/generated/facts.json`. The check fails when a fact no longer resolves,
when its printed statement changes, or when a theorem shown with `proved` was
lifted from a different theory than the one proving it. `proved(name)` also
refuses to compile unless `name` is in `facts.json`, so every displayed
theorem appears in both manifests.

The printed statements are not rendered. They stay in `facts.json` because a
statement can change with no edit to its source text (a changed abbreviation,
notation or locale), and the diff then surfaces here. Coverage is bounded by
what is built: a fact whose session has no heap is reported as unresolved,
naming the session.

### `pixi run thesis-claims` -- does the analyzer still print this?

`shared/claims.toml` declares the command behind each figure built from
analyzer output; `tools/claims.py --check` re-runs every one and fails on a
diff, quoting the `why` line so the failure names the sentence that is now
wrong.

### `pixi run thesis-playground` -- is this still the run the README shows?

The README's playground figures are captured, not drawn, and each links to the
run it shows. `shared/playground-figures.toml` names the screenshot, the
program and the settings of every figure the thesis places;
`tools/playground_figures.py` copies image and program under
`shared/generated/playground/` (Typst reads nothing above its root) and derives
the link with the encoder the playground's Share button uses. A recaptured
figure or an edited program fails the check until the copy is regenerated.

```typst
#playground-figure("contexts", [The same two calls, without and with contexts])
#playground-program("contexts")      // the program, as a listing
```

### `pixi run thesis-vimp` -- does this listing open its own program?

Every VIMP listing links to the playground: the `VIMP ↗` tag on its frame opens
the program, preloaded, at the listing's settings. `listing(lang: "c")` in
`lib/code.typ` computes the link while the document compiles, so no chapter
holds a URL. The playground reads `#code=` as raw deflate in base64url; Typst
has no compressor, so the helper writes stored (uncompressed) deflate blocks,
which the playground's `DecompressionStream("deflate-raw")` inflates like the
Share button's output. A fragment without a `fun` is opened as the body of
`main`.

```typst
#listing(lang: "c", ```...```)                          // playground defaults
#listing(lang: "c", ctx: "none", ```...```)             // interval, warrow, no contexts
#listing(lang: "c", claim: "dom-crt-congruence", ```...```) // the claim's fixture and settings
```

`tools/vimp_listings.py --check` queries the compiled document for every
listing, decodes each link and compares the decoded text with the program
shown (or with the claim's fixture, of which the listing must be a copy or an
excerpt), validates the settings against `pages/playground.html`, parses every
linked program with `voblint --parse-only`, and requires each link as a URI
annotation in a freshly compiled PDF. A listing that shows a registered claim's
program or a regression fixture must use the settings one of them runs with.
Any block of VIMP code outside the helper, a ```` ```c ```` block or
`raw(lang: "c")`, fails the check. Typst reads nothing above its root, so
`--write` extracts each claim's program (comments removed) and settings into
`shared/generated/vimp-claims.json`.

### `pixi run thesis-notation` -- is this still the notation the theories declare?

Appendix B's notation table, the README's Notation section and the legend above
the explainer's flagship theorems are one table. `shared/notation.toml` types
only how to read each symbol and what it means; `tools/notation.py` finds the
declaration and derives the rest: the symbol from its mixfix, the theory, the
scope (global or the declaring locale), the print mode (`abbreviation (input)`
is never printed), a locale abbreviation's expansion and the global set it
abbreviates, and the anchor in the rendered theories. It recognizes only the
declaration shapes the table uses and fails with a file and line on any other.
`--write` writes `shared/generated/notation.json` and the two marked blocks
(`<!-- notation:begin -->` ... `<!-- notation:end -->`) in `README.md` and
`pages/index.html`; `--check` fails when any of them is stale, and verifies
every anchor against `build/isabelle-html` when it exists (`--lenient` falls
back to the link map). `lib/notation.typ` renders the appendix table.

### `pixi run thesis-stats` -- is this still the size of the repository?

Line counts, theory files and regression-corpus sizes are measured, never
typed. `tools/stats.py` reads the collection `scripts/pages_stats.py` builds
for the project site, drops the per-commit fields, flattens it to dotted keys
and writes `shared/generated/stats.json`; the site and the thesis therefore
count with the same rules. `#stat("isabelle.lines")` prints a figure with the
site's grouping (`62,098`), `stat-sum` and `stat-percent` combine figures, and
`stat-keys("corpus.by_group.")` enumerates a breakdown, which is how the corpus
table in the appendix is built. An unknown key fails the build.

The AI-use statement reads `shared/generated/ai-use-stats.json`, a manual
snapshot that `tools/ai_use_stats.py` computes from the git history and the
local Claude Code and Codex session logs. Those logs exist only on the author's
machine, so the script is deliberately not part of `thesis-check`, CI or any
pixi task; rerun it by hand before a submission build.

The check fails when the committed JSON differs from a fresh measurement
(`pixi run thesis-stats-write` refreshes it, and `thesis-generated` includes
it) and when a line in `content/` that names lines, theories, files, sessions,
fixtures, cases, lemmas or similar holds a numeral with two or more digits
outside `stat()`, code or math. Numbers that are not statistics, such as a pull
request number, go in the commented `ALLOW` list in `tools/stats.py`; an entry
that no longer matches is reported too. Single digits and spelled-out numbers
are not scanned. Like `pages-stats`, it needs the vendored solver checked out.
It runs in the pre-push hook and in CI, not before each commit, because any
theory or fixture edit changes the measurement.

### `pixi run thesis-links` -- does this link reach the definition?

Isabelle's HTML output carries a per-entity anchor
(`id="CFG_Def.pp|type"`), so a citation lands on the definition rather than the
theory page. URLs are never guessed at render time:
`scripts/check_thesis_links.py` resolves each cited name against a real anchor
and writes only the verified ones to `shared/generated/links.json`.

Validation happens in three places, because a link points at a *deployed* page
and only one of them can see it:

| where | mode | gates? |
| --- | --- | --- |
| working copy and pre-commit | `--check --lenient` | **yes** for missing targets; local anchor verification may be skipped |
| CI, the job that renders the HTML | `--write` + drift warning | no |
| CI on main, after Pages publishes | `--live` | **yes** |

`--from-live` builds the map from the published site rather than a local
`docs/html`, which is the reliable source: the two drift apart in both
directions.

Every entity function links automatically, and `#thy-badge("Session", "Theory")`
gives the standalone marker for a section heading. Generated declarations and
statements also link to their formal sources. Missing map entries fail rendering;
there is no unlinked fallback. `pixi run thesis-links-coverage` checks coverage
without an HTML build. Regenerate targets with `pixi run thesis-links-write`,
or use the checker with `--write --from-live` to resolve published definitions.

## Isabelle in the text

Theory sources are ASCII-only, so a snippet arrives as `\<Longrightarrow>`
rather than as the glyph. `tools/gen_isabelle_symbols.py` turns Isabelle's own
`etc/symbols` into a lookup table (`lib/isabelle-symbols.typ`, regenerate with
`pixi run thesis-symbols`) and `lib/code.typ` applies it. Highlighting uses
`assets/isabelle.sublime-syntax`, written for this thesis because no Isabelle
syntax definition exists in a format `syntect` accepts.

`assets/fonts/` carries Isabelle's own DejaVu build. Stock DejaVu Sans Mono has
no glyph for several symbols a statement contains -- `\<And>` among them -- and
a missing glyph inside a theorem statement is a wrong page, not a cosmetic
problem. `lib/tum.typ` applies the family to `raw` through a show rule, which is
the only lever that beats Typst's own default for code blocks.

## Generated figures

Figures that state facts about the formalization are generated, not drawn.

| Figure | Source | Generator |
| --- | --- | --- |
| CFGs, traces, solver states | analyzer GraphViz output | `diagraph`, inline |
| locale hierarchy | `Locale.pretty_locale_deps` | `tools/locale_graph.ML` |
| class hierarchy | `class_deps` | Isabelle command |
| what a theorem rests on | `thm_deps` | Isabelle command |
| oracle / `sorry` audit | `thm_oracles` | Isabelle command |
| session graph | `isabelle build -g` | Isabelle |
| analyzer output quoted in a figure | the CLI itself | `tools/claims.py` |
| Isabelle symbol table | the symbols the text quotes | `lib/code.typ` |
| regression matrix | `tests/run.py` | to be written |
| size figures, corpus table | `scripts/pages_stats.py` | `tools/stats.py`, `lib/stats.typ` |

`thm_oracles` is worth calling out: its output is machine-checked evidence that
an endpoint theorem rests on no oracle and no admitted subgoal. Most comparable
theses assert that in prose.

## Figure gallery

`content/03-gallery.typ` is not thesis content. It holds one instance of every
figure kind the thesis needs, so a new figure starts as a copy of a working
one. Delete the chapter before submission.

## Numbering

Two traps worth knowing, both already handled in `lib/tum.typ`:

- A numbering function that builds a chapter prefix from the heading counter is
  correct in a caption and wrong in a cross-reference -- it runs where the
  number is *displayed*, so a chapter-1 reference to a chapter-3 figure renders
  "Figure 1.1". References are resolved separately, at the target's location.
- `rich-counters` cannot drive figure numbering, because Typst resolves
  `@fig:...` through its own figure counters. It is used for theorems, which
  are not referenced that way; figure counters are reset per chapter instead.
