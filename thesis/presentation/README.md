# Thesis presentation

Build the slides and timed speaker notes:

```sh
pixi run slides
```

Outputs are in `build/presentation/`: `voblint-slides.pdf` and
`speaker-notes.txt`. CI builds the deck in the thesis job, and the site
publishes it as `slides.pdf`, linked from every page's top navigation.

The deck has 25 main slides, planned at 19:05, and three backups. `build.py` fails on any Typst warning, on main slides out of order, and
on a main talk over 20 minutes.

## Style

16:9 pages, one claim per slide as its title with the key words coloured, and
figures instead of bullet text: side-by-side comparisons, a checklist build
beside a growing figure, statement slides. The opening and ending follow the
thesis introduction and conclusion; the middle works one example into the
formal argument; the demo runs live in the playground. `theme.typ` holds the
visual language; `slides.typ` holds the talk and its speaker notes.

Text is set in Roboto from the pixi environment (`font-ttf-roboto`), with
system fonts ignored, so the deck renders the same locally and in CI.

## Sources of figures

- Explainer SVGs lifted for the thesis, under `shared/generated/svg/`.
- Playground captures under `shared/generated/playground/`, guarded by
  `thesis-playground`.
- Analyzer verdicts through `claim-check`, guarded by `thesis-claims`.
- Theorem names through `isathm`, which fails the build on a missing link.
- Theorem statements through the generated snippets (`shared/generated/snippets`).
- Goblint comparison counts from `goblint-alignment.json`, written from the site.
- Context grids from the analyzer's graph snapshots (`claim-snapshot`).
- New drawings (timeline, pipelines, equations, abstract values, traces,
  contract diagram, nested sets, iceberg) are cetz code in `slides.typ` and
  `theme.typ`. `assets/banner.png` and `assets/goblint.svg` are copies of
  `docs/images/banner.png` and `pages/assets/logos/goblint.svg`, since the deck
  compiles with `thesis/` as its root.

`../presentation-outline.md` records the plan and the source status of every
external claim, in particular the 2026 results on slides 3 and 4.
