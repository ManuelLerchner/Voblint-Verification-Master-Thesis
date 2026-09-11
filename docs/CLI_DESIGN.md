# CLI: `voblint`

Status: **implemented** (`cli/main.ml`, `cli/vimp_frontend.ml`). Source file
extension is `.vimp`; the grammar itself is documented in `grammar/vimp.yaml`,
not here.

## Shape

```text
voblint --analysis sign|interval|int|parity|congruence[,...]
        [--context none|entry-state|call-string] [--context-depth K]
        [--context-graph collapsed|expanded]
        [--dot | --dot-full | --graph-snapshot | --html | --html-out DIR]
        [--solver join|per-origin|warrow|warrow-per-origin]
        [--timeout SECONDS] FILE.vimp
voblint --parse-only FILE.vimp
voblint --help
```

- `--analysis sign|interval|int|parity|congruence` selects the domain (required
  unless `--parse-only`). `int` is the refining composite Sign x Interval x
  Parity x Congruence domain, fixed at its most precise refinement mode; its
  default solver is warrowing. `parity` is the four-element
  Bot/Even/Odd/Top lattice; it decides equalities only by refuting them
  across differing parities. `congruence` is the residue-class domain, one
  value constrained to `x = r (mod m)`. A comma list puts several domains side
  by side in one `--html` report and requires `--html` and `--context none`.
- `--context none|entry-state|call-string` selects context sensitivity
  (default `none`). `entry-state` re-analyzes each callee per distinct
  entered-argument context; `call-string` splits it by bounded call history
  instead and requires `--context-depth K` with `K >= 1`. Every domain has a
  routed instance at both, though not at every `--solver`: the resolver follows
  each pairing's proved capability, so an unproved solver/context pairing is a
  configuration error, not a silent fallback.
- Soundness does not follow the domain axis here. The theorem over `analyse`
  covers all five domains at `--context none` only; under `entry-state` and
  `call-string` what is proved is the weaker per-context bound. See
  [`docs/THEOREM_MAP.md`](THEOREM_MAP.md) for the exact shape.
- `--context-depth K` bounds the call string. Valid only with `--context
  call-string`; `K = 0` is rejected rather than treated as `--context none`.
- `--context-graph collapsed|expanded` selects how `--dot`/`--dot-full`/
  `--graph-snapshot`/`--html` render an `entry-state` result, for every domain.
  This is a rendering choice over the same computed contextual result, not a
  different analysis — see `docs/CHECK_ARCHITECTURE.md`'s "Contextual result
  and GraphViz presentation" section for the full architecture and the CLI
  contract. `expanded` is the default under `--context entry-state`: a run
  asked for per-context precision, and the collapsed view joins it away, so a
  point dead in one activation and live in another reads as live. An explicit
  `expanded` requires `--context entry-state`: `--context none` has one context
  to draw and `--context call-string` renders per-context already, so asking
  for `expanded` at either is a configuration error, not a silent fallback.
- `--dot` / `--dot-full` / `--graph-snapshot` pick an output mode in place of
  the default plain-text check report: `--dot` annotates check nodes only,
  `--dot-full` annotates every node with its computed abstract state,
  `--graph-snapshot` emits a deterministic, DOT-free textual snapshot (used
  as the regression corpus's structural oracle, see `tests/run.py`). `--html`
  writes a browsable result directory instead (see `docs/HTML_REPORT.md`).
- `--solver join|per-origin|warrow|warrow-per-origin` bypasses the domain's
  production solver choice to exercise the vendored solver's update-rule
  discipline directly (experimental). Which disciplines a domain accepts at
  each context is the resolver's table (`Config_Tables.thy`): `interval` takes
  all four everywhere; `int` all four at `--context none` and `join`/`warrow`
  at the two context modes; `sign`, `parity` and `congruence` take `join`
  everywhere and `per-origin` at `--context none` only. The text report and
  `--html` display a chosen discipline; `--dot`/`--dot-full`/`--graph-snapshot`
  do not, and `--html` with `--solver` requires `--context none`.
- `--parse-only` parses and exits without running any analysis. A
  syntactically valid but ill-formed program still exits 0 here; the full run
  rejects it with exit 4.
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
Voblint_CLI.Generated.run_voblint domain solver context view prog
    |                                  <- Isabelle-generated (Voblint_Codegen
    |                                     session's export_code), the CLI's
    |                                     only analysis entry point: it checks
    |                                     well-formedness, resolves the
    |                                     configuration, and runs the plan
    v
Malformed_Program | Unsupported_Configuration | Analysed out
    |
    v
out_checks (text report) / out_graph (--dot, --dot-full, --html)
                         / out_snapshot (--graph-snapshot)
    -> DOT and HTML drawn by cli/dot_render.ml and cli/html_report.ml,
       all sourced from the one solve that produced `out` (never a second)
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

Interval analysis is sound but not proven total: no theorem shows the solver
terminates on every program, so termination is a premise of each soundness
theorem, discharged per program. Interval's carrier has infinite height, and
the join-based disciplines (`--solver join`, `per-origin`) have no termination
guarantee on it. Reproductions during development included process/backend
crashes, not just long-running computation, so the containment mechanism is a
killable subprocess (`run_contained` in `cli/main.ml`), not an in-process
timeout:

```text
CLI parent
    |
    +-- fork() analyzer worker
           |
           +-- run the requested run_voblint call, write result to a temp file
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
`Example_EntryState_Graph_Regression.thy`) is exactly the kind of case
this boundary is meant to contain, not fix.

## Explicit non-goals

- Parsing arbitrary C or another external source language.
- Verifying the parser itself.
- Runtime generation of proof objects.
- Comparison against Goblint's own output.
