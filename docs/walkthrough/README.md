# HTML walkthroughs

Static documentation for the Goblint formalization. One page per `src/` layer,
plus a hub and shared assets. **Committed in the repo; not deployed to GitHub
Pages** (the site is Isabelle browser info from `make html` → `docs/html/`).

**Open locally:** start at [`index.html`](index.html), or go directly to
[`pipeline/index.html`](pipeline/index.html) for the main end-to-end narrative.

## Layout

| Path | Topic |
| --- | --- |
| [`index.html`](index.html) | Hub — links to all layers |
| [`pipeline/index.html`](pipeline/index.html) | End-to-end soundness, running example |
| [`imp2/index.html`](imp2/index.html) | Syntax and small-step semantics |
| [`cfg/index.html`](cfg/index.html) | CFG core (def, paths, `to_cfg`) |
| [`cfg/collecting/index.html`](cfg/collecting/index.html) | `cfg_collect`, `runs_to`, bridges |
| [`domains/index.html`](domains/index.html) | Abstract domains |
| [`equations/index.html`](equations/index.html) | Equation systems and soundness |
| [`solver/index.html`](solver/index.html) | TD solver bridge |
| [`examples/index.html`](examples/index.html) | Executable examples |

## Shared assets

- [`walkthrough.css`](walkthrough.css) — layout, cards, tables, mermaid containers
- [`walkthrough.js`](walkthrough.js) — mermaid init, TOC scroll-spy

## Markdown companions

- [`../PROOF_OVERVIEW.md`](../PROOF_OVERVIEW.md) — theorem map (source of truth for names)
- [`../PROOF_PHASES.md`](../PROOF_PHASES.md) — phases and sorry inventory
- [`../../src/*/README.md`](../../src/README.md) — per-folder summaries in the repo

## Isabelle session browser info (generated, GitHub Pages)

From the repo root:

```bash
make html
```

Runs `isabelle build … -o browser_info` on session `Goblint_Formalization` and
copies the result to [`../html/`](../html/) (gitignored). Open
[`../html/isabelle/index.html`](../html/isabelle/index.html) after a local build.
CI deploys `docs/html/` to GitHub Pages on push to `main` (Isabelle browser info
only — not this walkthrough tree).

## Maintenance

When a layer changes materially, update the matching `index.html` and
`src/<layer>/README.md` together. Facts must match current `.thy` files (no
`big_step`, no `CFG_Collecting.thy` umbrella — use `CFG_Runs_To_Bridge`).
