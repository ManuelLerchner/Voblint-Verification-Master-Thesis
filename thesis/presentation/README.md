# Thesis presentation

Build the PDF, timed speaker notes, and offline solver replay:

```sh
rtk pixi run python3 thesis/presentation/build.py
```

Outputs are in `build/presentation/`: `voblint-slides.pdf`,
`speaker-notes.txt`, `replay.html`, and `solve-replay.gif`.
The deck has 20 main slides totaling 20 minutes and four backup slides.
The PDF uses a static replay frame; open the companion HTML to play the GIF.
When `ffmpeg` is available, the build also creates an MP4 and uses native video
controls in the companion page, allowing playback to pause at a solver event.

The source uses [Touying 0.8.0](https://typst.app/universe/package/touying/).
Its local theme follows the shared TUM Beamer/Rochester layout in the author's
[IDP presentation](https://github.com/ManuelLerchner/ProliferatingCellCollectives-IDP/tree/HEAD/presentation)
and [bachelor presentation](https://github.com/ManuelLerchner/AutoPas-FuzzyTuning-Bachelor-Thesis/tree/HEAD/presentation):
white 4:3 pages, a blue header and rule, black titles, square bullets, and page
numbers. `assets/tum.png` comes from the IDP presentation's `figures/tum.png`.
The header uses this project's title instead of the other chair's affiliation.

Technical claims use baseline `3520a4ec77ac0a9c2a3f7812a37a69f4148128cd`.
The machine-integer outlook refers separately to branch revision
`31e267925ed730b8edc9c38aa2b2c21101d75531`; it is not part of that baseline.
Theorem links and displayed verdicts reuse the thesis's existing helpers and
generated claims. Speaker notes distinguish demonstrations, proof instances,
trusted components, and retrospective development findings.

Both reference decks repeat an outline at each section boundary. This deck uses
five ten-second transitions, included in the 20-minute timing: motivation,
foundations, implementation and verification, results, and discussion/outlook.

The title image `assets/voblint.png` is the existing 1024 × 1024 original from
`~/Downloads/voblint-favicon.png`, matching the repository's 256 × 256 favicon.
It is reused without image editing.
