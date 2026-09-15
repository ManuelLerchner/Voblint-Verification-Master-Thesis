# CLI: `voblint`

Status: **implemented** (`cli/entry/voblint.ml`, `cli/frontend/vimp_frontend.ml`). Source file
extension is `.vimp`; the grammar itself is documented in `manifests/vimp-grammar.yaml`,
not here.

## Shape

```text
voblint --analysis sign|interval|int|parity|congruence[,...]
        [--context none|entry-state|call-string] [--context-depth K]
        [--dot | --graph-snapshot | --html | --html-out DIR]
        [--globals join|per-origin|warrow|warrow-per-origin]
        [--timeout SECONDS] FILE.vimp
voblint --parse-only FILE.vimp
voblint --help
```

- `--analysis sign|interval|int|parity|congruence` selects the domain (required
  unless `--parse-only`). `int` is the refining composite Sign x Interval x
  Parity x Congruence domain, fixed at its most precise refinement mode.
  `parity` is the four-element Bot/Even/Odd/Top lattice; it decides equalities
  only by refuting them across differing parities. `congruence` is the residue-class domain, one
  value constrained to `x = r (mod m)`. A comma list puts several domains side
  by side in one `--html` report and requires `--html` and `--context none`.
- `--context none|entry-state|call-string` selects context sensitivity
  (default `none`). `entry-state` re-analyzes each callee per distinct
  entered-argument context; `call-string` splits it by bounded call history
  instead and requires `--context-depth K`. Every domain serves every context
  mode at every `--globals` rule.
- `run_voblint_certified_source_sound` covers every domain, rule and context
  mode. Under `entry-state` and `call-string` its table claim is existential in
  the context: the store sits in the entry of at least one context its call
  history is admitted at. See [`docs/THEOREM_MAP.md`](THEOREM_MAP.md) for the
  exact shape.
- `--context-depth K` bounds the call string. Valid only with `--context
  call-string`; `K >= 0`, and a negative `K` is rejected. `K = 0` keeps no call
  site, so every callee shares one context over a still call-string-keyed
  equation system.
- `--dot` / `--graph-snapshot` pick an output mode in place of the default
  plain-text check report. Both draw the one contextual graph: one node per
  `(pp, ctx)`, each carrying its procedure-local state (formals, locals, return
  slot) and its check findings; a context-free run has the single unit
  context. Declared globals are not repeated per node (see
  [`docs/CHECK_ARCHITECTURE.md`](CHECK_ARCHITECTURE.md) for what the HTML
  report's globals pane shows today). `--graph-snapshot`
  emits a deterministic, DOT-free textual form of that graph (the regression
  corpus's structural oracle, see `tests/run.py`). `--html` writes a browsable
  result directory instead (see `docs/HTML_REPORT.md`).
- `--globals join|per-origin|warrow|warrow-per-origin` selects how the vendored
  solver merges a value side-effected into a global unknown: joined, joined per
  origin, warrowed, or warrowed per origin. Local unknowns are warrowed at
  widening points under every rule. The default is `warrow` for every domain,
  chosen in `cli/entry/voblint.ml`; Isabelle's `run_voblint` takes the rule as
  an argument and has no default. Every output mode renders the table the
  chosen rule solved, contextual graphs included.
- `--parse-only` parses and exits without running any analysis. A
  syntactically valid but ill-formed program still exits 0 here; the full run
  rejects it with exit 4.
- `--timeout SECONDS` bounds the analysis subprocess (default 10).

## Architecture

```text
FILE.vimp text
    |
    |  Vimp_lexer/Vimp_parser (cli/, generated from manifests/vimp-grammar.yaml by
    |  scripts/gen_vimp_menhir.py -- ocamllex + Menhir) via Vimp_frontend
    |  (hand-written glue); unverified adapter, not in the soundness scope
    v
imp_prog                              <- the same AST type the proved
    |                                     pipeline starts from
    v
Voblint_CLI.Generated.run_voblint domain globals context prog
    |                                  <- Isabelle-generated (Voblint_Codegen
    |                                     session's export_code), the CLI's
    |                                     only analysis entry point: it checks
    |                                     well-formedness and runs the
    |                                     configuration's registration
    v
Malformed_Program | Analysed res
    |
    v
res_contexts / res_states / res_routes / res_checks / res_globals / res_diagnostics
    -> text report, graph, DOT, snapshot and HTML built in cli/result/ and
       cli/render/, all sourced from the one solve that produced `res`
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
the join-based rules (`--globals join`, `per-origin`) have no termination
guarantee on it. Reproductions during development included process/backend
crashes, not just long-running computation, so the containment mechanism is a
killable subprocess (`run_contained` in `cli/entry/voblint.ml`), not an in-process
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
unsuspecting user actually hits the gap.

## Explicit non-goals

- Parsing arbitrary C or another external source language.
- Verifying the parser itself.
- Runtime generation of proof objects.
- Comparison against Goblint's own output.
