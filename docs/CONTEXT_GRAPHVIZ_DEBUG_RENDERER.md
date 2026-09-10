# Context GraphViz Debug Renderer

Status: **superseded**. The API this document described
(`ctx_debug_graphviz_same_ctx_cfg_show_globals_default`, `ctx_debug_graphviz`,
`ctx_debug_graphviz_with_globals`, `EA_Enter`-labeled debug edges) has been
removed from the codebase; none of these constants exist in `.thy` sources
any more. It was a hand-rolled debug renderer for materializing a small,
explicitly-supplied list of contexts (e.g. `[SZero, SPos]`) as duplicated CFG
copies, predating the current contextual `analysis_result` architecture.

The production replacement is `--context-graph expanded` in
`src/Analysis/Reporting/Analysis_GraphViz.thy`: it renders every
context a solved, context-sensitive `analysis_result` actually covers
(`contexts_at`/`ordered_by_key`), not a hand-supplied list, sourced from the
one canonical result table rather than a caller-assembled node/edge list.
See `docs/CHECK_ARCHITECTURE.md`'s "Contextual result and GraphViz
presentation (collapsed vs. expanded)" section for the current architecture,
and `tests/regression/11-graph-snapshot/04-expanded_three_contexts.vimp`
onward for worked examples reachable through the `voblint` CLI
(`docs/CLI_DESIGN.md`).
