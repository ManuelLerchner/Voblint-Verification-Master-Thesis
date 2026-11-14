# Site sources

`pixi run pages-dev` serves the explainer, playground, profiling page and proof map
at `http://localhost:8000`. The proof map is `proof-map.html`.

## Proof-map data

The JSON is generated at `build/isabelle-html/assets/proof-map.json`, under the
existing ignored build directory. `isabelle-html-build` generates it after the
HTML, so the same artifact supplies both the map and its documentation links in
CI. The Pages build copies it with the HTML; the development server serves it
through its existing HTML layer.

After building the Isabelle heaps and HTML, `pixi run proof-map-data` refreshes
just the map. The generator, source-page logic and styles are tracked; JSON is
not. A missing export produces a visible error instead of invented sample data.

Nodes are all entities in the Isabelle export, including generated facts. Edges
are statement/specification references, not proof dependencies. Wheel radial
layers use reference distance from the selected main results; disconnected
entities occupy the outer band. Session colors use the same dependency depths and CSS palette as the strata figure. The overview samples
ordinary marks deterministically and reveals them on zoom. Highlighted results
remain visible and become cards at close range. Main results are explicitly
listed in `proof-map.js`, following `docs/THEOREM_MAP.md`.

Checks: `pixi run pages-lint`, `pixi run pages-links`, and
`python3 -m unittest discover -s tests -p test_pages_proof_map.py`.

## Treemap screenshot

With `pages-dev` running and Playwright installed as for
`capture_readme_figures.mjs`, run `node scripts/capture_proof_map.mjs`.
It captures the treemap without browser controls and writes identical images
for the site and thesis. `pixi run proof-map-figure` checks both copies and
capture-source hashes. The metadata records the Isabelle export behind this
snapshot; regenerate the screenshot when refreshing the published corpus.
