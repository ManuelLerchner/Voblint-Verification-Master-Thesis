# Thesis presentation

Build the slides and timed speaker notes:

```sh
pixi run slides
```

Outputs are in `build/presentation/`: `voblint-slides.pdf` and
`speaker-notes.txt`. CI builds the deck in the thesis job, and the site
publishes it as `slides.pdf`, linked from every page's top navigation.

The deck has 17 main slides, planned at 18 minutes of a 20-minute slot, and one
backup. `build.py` fails on any Typst warning, on main slides out of order, and
on a main talk over 20 minutes.

## Style

16:9 pages, one claim per slide as its title with the key words coloured, and
figures instead of bullet text: side-by-side comparisons, a checklist build
beside a growing figure, statement slides. The narrative follows a "why it
exists, a small example, the complexity that piles up, the bug that slips
through, what a proof changes, the running tool" arc. `theme.typ` holds the
visual language; `slides.typ` holds the talk and its speaker notes.

Text is set in Roboto from the pixi environment (`font-ttf-roboto`), with
system fonts ignored, so the deck renders the same locally and in CI.

## Sources of figures

- Explainer SVGs lifted for the thesis, under `shared/generated/svg/`.
- Playground captures under `shared/generated/playground/`, guarded by
  `thesis-playground`.
- Analyzer verdicts through `claim-check`, guarded by `thesis-claims`.
- Theorem names through `isathm`, which fails the build on a missing link.
- New drawings (timeline, abstract values, the checked-chain picture, nested
  sets) are cetz code in `slides.typ` and `theme.typ`.

`../presentation-outline.md` records the plan and the source status of every
external claim, in particular the 2026 results on slides 3 and 4.
