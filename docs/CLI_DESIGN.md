# CLI: `voblint`

Status: **implemented** (`cli/main.ml`, `cli/vimp_frontend.ml`). This document
originally sketched a `voblint-verify --file test.voblint` design (issue #29)
before implementation started; it now describes the actual, shipped CLI
instead, so a reader does not have to reconcile a stale design against the
real tool. Source file extension is `.vimp`, not `.voblint` — the grammar
itself is documented in `grammar/vimp.yaml`, not here.

## Shape

```text
voblint --analysis sign|interval|int [--context none|entry-state]
        [--context-graph collapsed|expanded]
        [--dot | --dot-full | --graph-snapshot]
        [--solver join|per-origin|warrow]
        [--timeout SECONDS] FILE.vimp
voblint --parse-only FILE.vimp
voblint --help
```

- `--analysis sign|interval|int` selects the domain (required unless
  `--parse-only`). `int` is the refining composite Sign x Interval x Parity x
  Congruence domain, fixed at its most precise refinement mode and the
  warrowing solver; it has no `--context`/`--solver` support.
- `--context none|entry-state` selects context sensitivity (default `none`).
  `entry-state` re-analyzes each callee per distinct entered-argument
  context; only `--analysis interval` supports it.
- `--context-graph collapsed|expanded` selects how `--dot`/`--dot-full`/
  `--graph-snapshot` render an `entry-state` result (default `collapsed`).
  This is a rendering choice over the same computed contextual result, not a
  different analysis — see `docs/CHECK_ARCHITECTURE.md`'s "Contextual result
  and GraphViz presentation" section for the full architecture and the CLI
  contract. Requires `--context entry-state`; combined with `--context none`
  it is a configuration error, not a silent fallback to `collapsed`.
- `--dot` / `--dot-full` / `--graph-snapshot` pick an output mode in place of
  the default plain-text check report: `--dot` annotates check nodes only,
  `--dot-full` annotates every node with its computed abstract state,
  `--graph-snapshot` emits a deterministic, DOT-free textual snapshot (used
  as the regression corpus's structural oracle, see `tests/run.py`).
- `--solver join|per-origin|warrow` bypasses the domain's production solver
  choice to exercise the vendored solver's update-rule discipline directly
  (experimental, issue #131); incompatible with `--context`/`--dot`/
  `--dot-full`/`--graph-snapshot`.
- `--parse-only` parses and exits without running any analysis.
- `--timeout SECONDS` bounds the analysis subprocess (default 10).

## Architecture

```text
FILE.vimp text
    |
    |  Vimp_lexer/Vimp_parser (cli/, generated from grammar/vimp.yaml by
    |  scripts/gen_vimp_menhir.py -- ocamllex + Menhir) via Vimp_frontend
    |  (hand-written glue); unverified adapter, not in the soundness scope
    v
imp_prog                              <- the same AST type the proved
    |                                     pipeline starts from
    v
Voblint_CLI.Analyse.analyse_with_state / analyse_ctx / analyse_with_solver
    |                                  <- Isabelle-generated (Voblint_Codegen
    |                                     session's export_code), the CLI's
    |                                     only production-facing entry points
    v
check_report_entry list, or a contextual_verdict report            (text)
    |                                                    (--dot/--dot-full/
    v                                                     --graph-snapshot)
Voblint_CLI.Example_State_Report_GraphViz.*_dot_auto / *_graph_snapshot_auto
    -> DOT / canonical-text rendering, sourced from the same one
       analysis_result the text report reads (never a second solve)
```

The parser is the only unverified component in this chain. Everything from
`imp_prog` onward is exported from Isabelle-generated OCaml; the CLI is
host-language plumbing over it (argument parsing, file I/O, the containment
subprocess below), not new proof work.

## Trust boundary

Stated in the CLI's own `--help` output too:

> Trust boundary: results are sound for the program this file's unverified
> parser actually built, not a guarantee that the parser read your source
> correctly. The analyzer core (parsing excluded) is generated from a
> machine-checked Isabelle/HOL proof.

A parser bug can change *which* program gets analyzed; it cannot invalidate
the analyzer's soundness theorem for the AST actually produced — the same
boundary Goblint's own unverified C frontend has relative to its analyzer
core.

## Known safety requirement: Interval containment

`analyse Interval_Analysis` is sound but not proven total: it can still
diverge on a finite program whose global-writing transfer depends
monotonically on the flow-insensitive global summary's own current value.
Reproductions during development included process/backend crashes, not just
long-running computation, so the containment mechanism is a killable
subprocess (`run_contained` in `cli/main.ml`), not an in-process timeout:

```text
CLI parent
    |
    +-- fork() analyzer worker
           |
           +-- run the requested analyse_*/*_auto call, write result to a temp file
```

The parent enforces a wall-clock timeout (`--timeout`, `SIGKILL` on expiry),
reports a controlled diagnostic on abnormal worker exit (crash, signal, or
timeout) rather than hanging silently, and removes the temp file via
`Fun.protect` regardless of outcome.

This is containment for a CLI, not a fix. The fix (if one lands) is a
proven-total or explicitly-scoped-nonterminating backend at the Isabelle
level; the subprocess boundary exists only because a CLI is where an
unsuspecting user actually hits the gap. The zero-formal EntryState
nontermination tracked separately (see the closing text block of
`Example_EntryState_GraphViz_Regression.thy`) is exactly the kind of case
this boundary is meant to contain, not fix.

## Explicit non-goals

- Parsing arbitrary C or another external source language.
- Verifying the parser itself.
- Runtime generation of proof objects.
- Comparison against Goblint's own output.
