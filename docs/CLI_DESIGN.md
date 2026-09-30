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
  Parity x Congruence domain; `--int-refinement never|once|fixpoint` (default
  `fixpoint`, only valid with `int`) selects how its components refine each
  other. Each mode is a registered analysis of its own (`Int_Analysis`,
  `Int_Once_Analysis`, `Int_Never_Analysis`); all of them are `int` in reports.
  `parity` is the four-element Bot/Even/Odd/Top lattice; it decides equalities
  only by refuting them across differing parities. `congruence` is the residue-class domain, one
  value constrained to `x = r (mod m)`. A comma list runs the named domains
  together in one solve, under every output and context mode: a state shows
  each domain's part on its own, in list order, a point any of them proves unreachable is
  unreachable, and a check is decided by the meet of their answers. The list
  reaches `run_voblint` as given, and its `Invalid_Activation` answer rejects a
  domain named twice (exit 1).
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
  report's globals pane shows). `--graph-snapshot`
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

## Solver trace (`--trace`)

`--trace` writes the solver's steps to stderr, or to `--output FILE`. Standard
output is byte-identical with and without it. `--compact` (the default) tells
the interprocedural story per call; `--verbose` lists every step; `--format
jsonl` is the machine-readable form. Each of `--compact`, `--verbose`,
`--format` and `--output` implies `--trace`; none of these names is used by
another option.

```text
voblint --analysis interval --context entry-state --trace docs/readme-figures/contexts.vimp
```

The hooks are inserted at build time: `cli/trace/patch_generated.ml` copies
the generated `Voblint_CLI.ml` into the build with guarded calls into
`cli/trace/solver_trace_hook.ml`. Each patch names generated text that must
occur exactly once (a per-mode patch: once per context mode that uses it), so
a regeneration that moves one fails the build with the patch's name. Neither
the Isabelle sources nor the export change, and no hook changes a computed
value; the tracer is outside the proof like the rest of the CLI. With
`--trace` off every hook is one branch on a reference.

The solver is polymorphic in its unknowns, so events hold them untyped. The
patches also define, next to each generated global-unknown datatype
(`global_unknown`, and `call_string_gk` under call strings), a decoder that
matches its constructors, and install it where the context mode fixes the
type. The renderer tells an activation seed from the analysis global through
that decoder only.

`tests/solver-trace/` holds the whole compact, verbose and JSON Lines traces of
the command above; `pixi run solver-trace-check` compares them, and
`UPDATE_TRACE_EXPECT=1` rewrites them from a live run.

Events are recorded during the solve and rendered after `run_voblint`
returns, inside the contained child. A run killed by `--timeout` leaves no
trace.

The playground offers the same traces. `cli/entry/voblint_web.ml` takes a
seventh argument, `trace`, naming the form as the flags do: `"compact"`,
`"verbose"` or `"jsonl"` add a `trace` field holding the text
`Solver_trace.emit` writes in that form, and `"off"` leaves the answer as it
was before the tracer existed. The page shows the compact or the full
(verbose) text above the graph, lays out its first 400 lines until the reader
asks for all of them, and saves the whole text; its JSON Lines download solves
the shown run again in `"jsonl"` mode. Share links carry the form as
`trace=compact` or `trace=verbose`; `trace=1` still opens the compact one. The
browser module outlives a run, so the adapter sets the hook's switch on every
call and `Solver_trace_hook.recorded` empties the event list it hands over.
`pixi run browser-trace-check` runs the wasm build under Node and compares
each form's trace of the command above with its file in `tests/solver-trace/`,
whose program name it swaps for `browser.vimp`.

JSON Lines schema 1. The first line is the run header; every solver event
carries an increasing `step`; check records and an `end` record with counts
follow. No timestamps, so equal runs give equal traces.

```text
{"event":"run","schema":1,"analysis":[..],"context_policy":..,"update_rule":..,"program":..}
{"step":n,"event":"solve"|"resolve","unknown":L}
{"step":n,"event":"query_local","current":L,"target":L}
{"step":n,"event":"value_local","current":L,"target":L,"value":V}
{"step":n,"event":"query_global","current":L,"target":G,"value":V}
{"step":n,"event":"side","current":L,"target":G,"value":V}
{"step":n,"event":"update_global","unknown":G,"old":V,"new":V}
{"step":n,"event":"update_local","unknown":L,"old":V,"new":V}
{"step":n,"event":"answer","current":L,"value":V}
{"step":n,"event":"route","call":L,"entry":V,"context":C}
{"event":"check","point":..,"condition":..,"verdict":..}
{"event":"end","local_unknowns":n,"global_unknowns":n}

L = {"kind":"local","node":"pp3"|"entry_f"|"exit_f","context":C}
G = {"kind":"activation_seed","procedure":f,"context":C} | {"kind":"analysis_global"}
C = {"kind":"unit"} | {"kind":"entry_state","values":[..]} | {"kind":"call_string","sites":[..]}
V = the value as the text report prints it, "⊥" for bottom
```

`query_global` carries the value the solver held for the global when it was
read. `side` is the solver's `Side` step, which is where buffered
publications are flushed; the buffering itself happens in a tree
transformation that keeps no origin, so there is no separate buffer event.
`update_*` means the value changed and the unknown's readers were
destabilized; the reader set itself is not listed.

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
