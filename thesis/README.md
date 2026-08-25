# Thesis

The Voblint thesis, in Typst.

```
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
pixi run thesis-generated  # re-extract snippets, claims, theorem statements
pixi run thesis-check      # every drift check
```

`--root` is `thesis/`, so the document reads generated material by absolute
path (`/shared/generated/...`) and Graphviz sources are laid out inside the
document with no build step.

## Why Typst

The one thing that argued for LaTeX was Isabelle's document preparation:
`@{thm foo}` typesets the statement Isabelle actually proved, and the build
fails when `foo` is gone. That guarantee is available here too --
`tools/facts.py` exports the proved statement from a built session and the
template renders it -- and it does not require writing prose inside theory
files to get it. Two further checks with no LaTeX equivalent, `snippets.py` and
`claims.py`, follow from the same idea.

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
| `lib/sources.typ` | `thy()` and `stmt()` -- material lifted from the formalization |
| `lib/theorems.typ` | theorem environments, numbered per chapter |
| `lib/glossary.typ` | the vocabulary the thesis assumes |
| `lib/tum.typ` | page geometry and front matter |

## Keeping the thesis honest

Four checks, all wired into `pixi run ci`; the first two also run at commit
time.

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

```typst
#thy("sound_domain")     // the declaration, verbatim, with its file header
```

### `pixi run thesis-facts` -- is this still what Isabelle proves?

`shared/facts.toml` lists the theorems the thesis reproduces; `tools/facts.py`
starts the built session, asks Isabelle for each statement in ASCII symbol
form, and stores them in `shared/generated/facts.json`. An unlisted name is a
compile error and a changed statement is a diff.

```typst
#stmt("valid_ltr_eq_lfp")                  // the statement, nothing else
#proved("valid_ltr_eq_lfp", note: [...])   // statement plus its name, as a claim
```

Statements are exported with `show_types`, `show_sorts` and
`show_question_marks` off, and with Isabelle's own line breaks at a
76-character margin -- so a long statement arrives structured the way the
Prover IDE shows it rather than as a wall of text. Coverage is bounded by what
is built: a fact whose session has no heap is reported as unresolved, naming
the session.

### `pixi run thesis-claims` -- does the analyzer still print this?

`shared/claims.toml` declares the command behind each figure built from
analyzer output; `tools/claims.py --check` re-runs every one and fails on a
diff, quoting the `why` line so the failure names the sentence that is now
wrong.

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
| working copy, `pixi run thesis-check` | `--check --lenient` | no -- says why it could not run |
| CI, the job that renders the HTML | `--write` + drift warning | no |
| CI on main, after Pages publishes | `--live` | **yes** |

`--from-live` builds the map from the published site rather than a local
`docs/html`, which is the reliable source: the two drift apart in both
directions.

Every entity function links automatically, and `#thy-badge("Session", "Theory")`
gives the standalone marker for a section heading. Before the theories are
rendered the map is empty and names appear unlinked, so the document always
builds.

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
| regression matrix, size table | `tests/run.py`, source counts | to be written |

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
