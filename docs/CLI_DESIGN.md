# CLI: `voblint`

Status: **implemented** (`cli/entry/voblint.ml`, `cli/frontend/vimp_frontend.ml`). Source file
extension is `.vimp`; the grammar itself is documented in `manifests/vimp-grammar.yaml`,
not here.

## Shape

```text
voblint --analysis sign|interval|int|parity|congruence[,...]
        [--context none|entry-state|call-string] [--context-depth K]
        [--dot | --graph-snapshot | --html | --html-out DIR]
        [--globals join|per-origin|warrow|warrow-per-origin|bounded-narrowing]
        [--narrow-bound N]
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
- `--globals join|per-origin|warrow|warrow-per-origin|bounded-narrowing` selects
  how the vendored solver merges a value side-effected into a global unknown:
  joined, joined per origin, warrowed, warrowed per origin, or widened per
  origin with bounded narrowing (the vendored `update_global_bounded_narrowing`).
  That rule narrows an origin once each time it switches from widening to
  narrowing, and keeps narrowing within a phase only while the origin has
  switched fewer than `--narrow-bound N` times. `N` defaults to 5, the default
  of Goblint's `solvers.td3.narrow-globs.narrow-gas`; unlike Goblint's option,
  `0` does not disable narrowing, it only stops narrowing after the first step
  of each switch.
  `--narrow-bound` is rejected with any other rule. The playground offers the
  bound as a control from 0 to 100 while that rule is selected, and a link
  carries it as `narrow=N` when it is not 5. Local unknowns are warrowed at widening points
  under every rule. The default is `warrow` for every domain,
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
the interprocedural story per call; `--verbose` lists every step in a
Goblint-aligned tracing vocabulary (subsystems and messages of Goblint's
`--trace` output; the table below records every difference); `--trace-sys SYS[,...]` limits the verbose form to
those subsystems; `--format jsonl` is the machine-readable form. Each of
`--compact`, `--verbose`, `--trace-sys`, `--format` and `--output` implies
`--trace`; none of these names is used by another option.

```text
voblint --analysis interval --context entry-state --trace docs/readme-figures/contexts.vimp
```

### Where the events come from

Tracing is part of the exported code. `Voblint_Solver.Solver_Trace` defines
`trace_event :: String.literal => (unit => 'e) => unit` as `()` and gives the
exported solver alternative code equations with `trace_event` calls at its steps:
`solve` (start and stop of one solve), `solve_rec_c` (query, iterate, one
evaluation of the right-hand side, each strategy-tree instruction) and
`destab_opt`/`destab_iter_opt` (destabilization). `Voblint_CLI.Trace_Run` does
the same for the three routing policies and for `analysis_result`, which hands
the trace the run's readers for contexts, global unknowns and values before the
solve. Each equation is proved equal to the vendored or original equation it
replaces by unfolding `trace_event`, and the originals are removed from code
export with `[code del]`; the vendored definitions and proofs are untouched. The
code the CLI and the browser run is therefore the code of proved equations.

`Trace_Run` maps `trace_event` to `Solver_trace_hook.emit` with `code_printing`.
That mapping is the one trusted addition, of the same kind as the other
target-language mappings. It forces the suspended event only when tracing is on,
so an untraced run builds no event. There is no mapping for the Eval target, so
proofs by evaluation run the logical equation.

Three layers, with different standing:

1. The solver result is the exported computation of proved equations. Tracing
   adds nothing to it but calls whose logical value is `()`.
2. The trace is an unverified observation of that computation. It cannot feed
   back: `emit` returns `()`, swallows every exception its suspension raises,
   and only appends to its own event list; it never touches solver state. What
   it could get wrong is the trace, not the result.
3. The playground's replay and animation are an unverified visualization of the
   trace.

The solver is generic in its unknowns and values, so the hook keeps events as
`Obj.t` under their channel (`solver`, `route`, `run`). The one place that casts
them back is `read_back` in `cli/render/solver_trace.ml`: it types the `run`
event as `trace_printers` and each other event as `solver_event` or
`route_event` over `cfg_node * Obj.t` unknowns, and every `Obj.t` inside only
ever reaches a printer the same run installed. Cast values flow into strings for
the trace and nowhere else: the renderer runs after `run_voblint` has returned,
and nothing it computes reaches the solver or the result. A wrong cast can
therefore only produce wrong or missing trace output (or crash the renderer
after the result is complete). Route events outside the solve's start and stop
events are the result being read back and are dropped.

Fallback, should code generation ever drop a unit-valued `let` (checked by
`test_generated_module_carries_trace_calls`): a traced executable solver that
returns its result together with its event list, with a proved projection
`fst (traced_solve ...) = solve ...`, so the trace becomes a value instead of
an effect.

### Verbose form: a Goblint-aligned tracing vocabulary

The verbose form uses a Goblint-aligned tracing vocabulary: it is not
Goblint-compatible output, and the table below is the record of where it
differs. It writes one line per solver event as Goblint's tracing library
(`src/util/tracing/goblint_tracing.ml`) does: indentation, then
`%%% <subsystem>: <message>`; a message's continuation lines start at column 0.
Subsystems and messages follow Goblint's `td_simplified.ml`, the side-effecting
top-down solver whose `query`/`iterate`/`side`/`destabilize` structure matches the
vendored solver's `Q`/`I`/`E`/`destab_opt`; `td3.ml` contributes the `sol`
value report. Checked against the local Goblint checkout at `0dc12d355`
(`src/solver/td_simplified.ml`, `src/solver/td3.ml`); the registered revision
`5320a6b7` was not re-checked for these files.

A statement point is named after its source, as Goblint's `pretty_trace` names a
node by its statement and location (`src/common/framework/node.ml`,
`src/framework/analyses.ml`): `(pp2 "x = x + 1;" L4, ctx)`. A block statement
shows its head (`while (x < 10)`), a point on a closing brace only its line.
The compact form names points the same way; JSON Lines keeps the bare `pp2`.

| Voblint event (`solver_event`) | Line | `td_simplified.ml` | `td3.ml` (`sol2` unless noted) |
| --- | --- | --- | --- |
| `Ev_Start x` | `multivar: solving for x` | 174 | none |
| `Ev_Query y x st cl` | `solver_query: entering query for x from y; stable st; called cl` | 68 | 454 `eval %a ## %a` |
| `Ev_Query_Wpoint x w` | `wpoint: query adding wpoint x` (unless `w`) | 80 | 468 `eval adding wpoint` |
| `Ev_Iterate_From_Query x` | `iter: iterate called from query` | 76 | none |
| `Ev_Add_Infl y x` | `infl: add_infl y x` | 37 | 305 |
| `Ev_Answer y x d` | `answer: exiting query for x from y` / `answer: d` | 85 | 473 `eval %a ## %a -> %a` |
| `Ev_Query_Global x g` | `solver_query: entering query for g from x` | 68 | 454 |
| `Ev_Answer_Global x g d` | `answer: exiting query for g from x` / `answer: d` | 85 | 473 |
| `Ev_Iterate x cl st wp` | `iter: begin iterate x, called: cl, stable: st, wpoint: wp` | 111 | 351 `solve %a, phase ...` |
| `Ev_Eq x` | `eq: eq x` | 50 | 430 |
| `Ev_Still_Unstable x` | `iter: iterate still unstable x` | 137 | 412 |
| `Ev_Widen x wp` | `wpoint: widen x` (if `wp`) | 122 | none |
| `Ev_Sol x wp old eqd new` | `sol: Var: x (wp: wp)` / `Old value` / `Eqd` / `New value` | none | 396 (`sol`) |
| `Ev_Wpoint_Remove x wp` | `wpoint: iterate removing wpoint x` (if `wp`) | 141 | 423 |
| `Ev_Update x wpx bot old new` | `update: x (wpx: wpx)` / `Old value` / `New value` (unless old is ⊥) | 127 | 404 (`solchange`) |
| `Ev_Iterate_Changed x` | `iter: iterate changed x` | 131 | none |
| `Ev_Side x g d` | `side: side to g from x; value: d` | 89 | 476 |
| `Ev_Update_Global x g bot old new` | `update: side to g from x new: new` (unless old is ⊥) | 102 | 498 (`solside`) |
| `Ev_Destabilize y` | `destab: destabilize y` | 57 | 551 |
| `Ev_Stable_Remove x` | `destab: stable remove x` | 61 | 555 |
| `Ev_Stop` | no line | `stop_event`, not a trace | none |
| `Ev_Rhs x d` | `rhs: x = d` | Voblint only | Voblint only |
| `Ev_Route (u, c) d c'` | `route: call at (u, c): entry d -> context c'` | Voblint only | Voblint only |

Differences, each deliberate or forced by the vendored solver:

- Indentation. `td_simplified.ml` traces with plain `trace`, which never
  indents. Voblint indents as if entering a query were a `tracei` and its answer
  a `traceu`: the entering line is printed, then the level grows by two; the
  answer is printed at the inner level, then it shrinks. The level is the
  solver's query depth. As in Goblint, an unselected subsystem prints nothing and
  changes no indentation.
- Unknowns print as `(node, context)`, Goblint's `dbg.trace.context` form,
  without the `on <location>` suffix. A global prints as `Global` or
  `Seed(procedure, context)`.
- `update` prints `old -> new` where Goblint prints `pretty_diff`.
- A query of a global unknown prints no `stable`/`called` flags: the vendored
  solver keeps neither set for globals. `side` and the global `update` print no
  `wpx`: globals are merged by the chosen update rule and never become widening
  points.
- The vendored solver repeats a right-hand side whose unknown lost stability
  inside the evaluation (`R`) before comparing values, so `iterate still
  unstable` is followed by a new `eq`, not by a new `begin iterate`. An
  iteration entered for a stable unknown also clears its widening point, which
  `td_simplified.ml` does not; no line reports it.
- `--trace-sys` stands for Goblint's repeatable `--trace SYS`, which needs a
  Goblint built in the `trace` profile; `--tracevars` and `--tracelocs` have no
  counterpart.

Goblint traces with no counterpart here: `init` (the vendored solver's value map
is total, ⊥ by default), `side widen` and `side adding wpoint` (no widening
points for globals), and the `td3.ml`-only steps of features the vendored solver
does not have: widening gas (`widengas`), the narrowing phase (`solve switching
to narrow`, `eq reused`), widening-point restarts (`wpoint restart`), the side
and incremental destabilizations (`destabilize_vs`, `destabilize_with_side`,
`destabilize_leaf`, `Restarting to bot`), weak dependencies (`demand weak
dep`), the local cache (`cache`), start values (`set_start`), `stable add`,
the postsolver's `restored var`, and `td3UpdateRule.ml`'s divided side effects.

### Compact form, JSON Lines, playground

The compact form and JSON Lines are read off the same events. The compact form
keeps its per-call story. JSON Lines schema 2 keeps every schema 1 event and
field unchanged (`solve`/`resolve` is an iteration of an unstable unknown,
`query_local`/`value_local` a query and its answer, `query_global` a global's
answer, `answer` the `rhs` value) and adds the solver's internal steps:
`start`, `iterate`, `eq`, `stable_add`, `still_unstable`, `widen`, `add_infl`,
`wpoint_add`, `wpoint_remove`, `destabilize` and `stable_remove`, then one
`result` record per point and context of the returned result. The added events
shift the `step` numbers of the schema 1 events.

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
was before the tracer existed. The page runs every analysis in `"verbose"`
mode and shows the text in the **Generated core** panel beside the call's input
and output; its JSON Lines download solves the shown run again in `"jsonl"`
mode. Share links carry `trace=verbose` to open that panel; older forms still
open it. The browser module outlives a run, so the adapter sets the hook's
switch on every call and `Solver_trace_hook.recorded` empties the event list it
hands over.

A run may never finish, and the page cancels it by terminating its worker. In
`"verbose"` mode the adapter therefore installs `Solver_trace_hook.listener`,
which renders each kept event as it is recorded (`Solver_trace.live_verbose`)
and posts the text to the worker's `Voblint_trace_chunk` about every 100 ms;
before the solve it posts the call's input to `Voblint_run_input`. On cancel the
page shows that input, no output, and the chunks it received. The adapter stops
keeping events at 50,000 or once 8 MB of text are posted, whichever comes first:
states grow with the run, and so do the lines that print them. Later events are
counted, not kept, so a run that never finishes stops growing its trace, and a
finished run's text ends with `Trace truncated` instead of `Trace complete`. The listener runs inside
the hook's `try`, and the hook still returns `()`. The CLI sets neither.
The page's **Solve replay** section, when opened, solves the shown run again in
`"jsonl"` mode and steps through the events on its own drawing of the graph
(`pages/replay.js`). Every state it shows comes from one reducer,
`reduce(state, event)` in `pages/replay_state.js` (pure, no DOM): the animation,
the per-step text and the snapshot cache all fold events through it. The
CLI's compact form keeps no state beyond its per-call story and reads the same
events with the same meaning.

By default the replay shows values, the active unknown, the solve stack and the
current query edge. The stable set, the destabilization cascade, widening
points, influence edges, globals with their contributions, routes and counters
are overlays the reader turns on.

`pixi run browser-trace-check` runs the wasm build under Node and compares
each form's trace of the command above with its file in `tests/solver-trace/`,
whose program name it swaps for `browser.vimp`.

JSON Lines schema 2. The first line is the run header; every solver event
carries an increasing `step` and the `line` of the `--verbose` trace of the
same run that its solver event prints on (an event the verbose form leaves out
takes the line of the last one it printed); check records and an `end` record
with counts follow. No timestamps, so equal runs give equal traces. Each step
below also carries `"line":n` after its `event`.

```text
{"event":"run","schema":2,"analysis":[..],"context_policy":..,"update_rule":..,"program":..}
{"step":n,"event":"solve"|"resolve","unknown":L}
{"step":n,"event":"query_local","current":L,"target":L}
{"step":n,"event":"value_local","current":L,"target":L,"value":V}
{"step":n,"event":"query_global","current":L,"target":G,"value":V}
{"step":n,"event":"side","current":L,"target":G,"value":V}
{"step":n,"event":"update_global","unknown":G,"old":V,"new":V}
{"step":n,"event":"update_local","unknown":L,"old":V,"new":V}
{"step":n,"event":"answer","current":L,"value":V}
{"step":n,"event":"route","call":L,"entry":V,"context":C}
{"step":n,"event":"iterate","unknown":L,"called":B,"stable":B,"wpoint":B}
{"step":n,"event":"start"|"eq"|"stable_add"|"stable_remove"|"still_unstable"|"widen"|"wpoint_add"|"wpoint_remove","unknown":L}
{"step":n,"event":"add_infl","unknown":L|G,"reader":L}
{"step":n,"event":"destabilize","unknown":L|G}
{"event":"result","unknown":L,"value":V}
{"event":"check","point":..,"condition":..,"verdict":..}
{"event":"end","local_unknowns":n,"global_unknowns":n}

L = {"kind":"local","node":"pp3"|"entry_f"|"exit_f","context":C}
G = {"kind":"activation_seed","procedure":f,"context":C} | {"kind":"analysis_global"}
C = {"kind":"unit"} | {"kind":"entry_state","values":[..]} | {"kind":"call_string","sites":[..]}
V = the value as the text report prints it, "⊥" for bottom
B = true | false
```

What each event is, and what the reducer does with it:

| Event | Kind | Replay state |
| --- | --- | --- |
| `start` | scope enter | the root unknown opens the solve stack |
| `query_local` | scope enter | the queried unknown is pushed on the stack |
| `value_local` | scope leave, observation | the queried unknown is popped |
| `eq` | state transition | one right-hand-side evaluation of the unknown |
| `stable_add` | state transition | the unknown enters the stable set |
| `stable_remove` | state transition | the unknown leaves the stable set |
| `wpoint_add`, `wpoint_remove` | state transition | widening-point membership |
| `widen` | observation | widening is applied at this step |
| `add_infl` | relation add | reader -> read unknown |
| `destabilize` | relation remove | every reader of the unknown is dropped |
| `update_local`, `update_global` | state transition | the stored value |
| `iterate`, `solve`, `resolve`, `still_unstable` | observation | none |
| `query_global`, `side`, `answer`, `route` | observation | the global's read value, its contributions, routes |

The stack is balanced by construction. `query_local` is emitted when the
solver's `Q` case starts and `value_local` in the continuation `Option.bind`
runs after `Q`'s recursive call has returned, so every event of the query lies
between the two. `Q` returns in every branch: a query of an unknown already
being solved (a widening point, re-entry) returns its current value at once, and
destabilization never aborts a query. A run that does not terminate emits no
unmatched `value_local`; it never ends. The stable set changes only through
`stable_add` (the solver's `R` case inserts the unknown before evaluating it)
and `stable_remove` (`destab_iter_opt`); the widening points only through
`wpoint_add` (`Q` of an unknown being solved) and `wpoint_remove` (`I`, whether
the unknown was unchanged or already stable). `destabilize` is emitted where
`destab_opt` drops the unknown's influence set with `fmdrop`, so no stale
edge survives it.

Counters: evaluations(u) counts `eq` of u; updates(u) counts updates whose new
value differs from the old one; destabilizations(u) counts `stable_remove` of u
while u was stable.

Versioning: adding event kinds or fields is compatible and bumps nothing when
existing events keep their meaning. Changing what an existing event means is a
breaking change even when its JSON shape stays the same, and so is any change of
replay semantics: both bump `schema`.

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
