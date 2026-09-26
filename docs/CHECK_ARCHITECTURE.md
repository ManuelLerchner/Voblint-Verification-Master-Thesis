# Check-discharge architecture

> **Status:** partly stale. "Pipeline" (above the rendering branch), "Layer
> responsibilities" and "Why no automatic sublocale" name retired pieces:
> `check_true`/`check_false` are one `check_query`; the `derived_*` locales are
> `numeric_query_judgments` (`Numeric_Queries.thy`), interpreted for
> every `backward_domain` in `Backward_Numeric_Queries.thy`; `backward_domain`
> lives in `Backward_Domain.thy`; `abstract_domain` and `backward_domain_mono`
> no longer exist. The current inventory is the
> `Checks/` row of `src/Abstract_Interpreter/Framework/README.md`. The
> rendering sections describe the tree as it stands.

Overview of how a compiled `__voblint_check(...)` condition becomes both a
GraphViz-rendered proof status and a semantic soundness guarantee. This is
a map of responsibilities across layers, not a proof-status inventory —
proof status lives in the `.thy` files themselves (`docs/PROOF_PHASES.md`).

## Pipeline

`abstract_check_domain` produces two independent outputs from the same
node-indexed abstract environment: an *executable classification* that
`run_voblint` exports and the OCaml CLI renders, and a *logical discharge*
that `checks_proven` turns into a semantic guarantee. Rendering never
consumes `checks_proven` — it does not depend on proving anything.

```text
VIMP source
    |
    | compile_prog (VIMP_Proc_to_CFG)
    v
CFG + checks : (pp * bexp) set     -- zero or more compiled checks per node
    |
    | verified TD solver, per domain (generated <Domain>_Analyses)
    v
node-indexed analysis_result       -- <d>_rule.result r
                                   ::   (vname => bool) -> imp_prog
                                     -> (unit, 'a abs_state) analysis_result
    |
    | domain-specific sound_numeric_queries instance
    v
abstract_check_domain (Abstract_Checks.thy)
    |
    +--> classify_check                              [executable]
    |        |
    |        v
    |    Check_Proved / Check_Refuted / Check_Unknown
    |        |
    |        | run_voblint (Analysis_Run.thy): state_checks, res_checks
    |        v
    |    node status (cli/result/context_graph.ml)       [OCaml]
    |        |
    |        v
    |    rendered CFG, proof status as node color (cli/render/render_dot.ml)
    |
    +--> abstract_checks_proven                       [proposition]
             |
             | node-local collecting soundness
             v
         checks_proven (Checks.thy, domain-independent)
             |
             v
         concrete stores satisfy every selected check
```

The check-classification and discharge layers above the node-indexed
solver state are domain-generic; each domain supplies its own solver
frontend and `sound_numeric_queries` instance below that line.
`Sign_Classify.thy`, `Interval_Classify.thy`, `Parity_Classify.thy`,
`Congruence_Classify.thy` and `Int_Classify.thy` are thin instantiations of the
generic layers, not separate implementations of the pipeline. The per-node state
they classify is the registration's `analysis_result` table, which
`unit_dg_analysis` reads back through the generic `analysis_surface` locale
(`state_at`, `report`).

## Layer responsibilities

### `Abstract_Domain.thy` — lattice and backward refinement

Owns `numeric_domain`/`abstract_domain` (the type-class every domain value
type instantiates), `sound_intersection`, `backward_domain` (guard narrowing: `inv_less`,
`inv_eq`, `afilter`/`bfilter`), and `backward_domain_mono`. Nothing here
knows about checks. `derived_less_queries`/`derived_eq_true_from_less`/
`derived_eq_false_from_intersection` do **not** live here — see the next layer.

### `Numeric_Queries.thy` — atomic-value entailment/refutation

Owns the `sound_numeric_queries` locale (`less_true`, `less_false`,
`eq_true`, `eq_false` over one abstract value + four soundness
assumptions) and its generic derivation from any `backward_domain`
instance's own narrowing operators. The derivation locales are registered
as sublocales of the backward capability hierarchy, precisely:

```text
backward_domain -> derived_less_queries -> derived_eq_true_from_less
backward_domain -> derived_eq_false_from_intersection
```

(`derived_eq_true_from_less` sublocales under `derived_less_queries`, not
directly under `backward_domain`; `derived_eq_false_from_intersection`
sublocales under `backward_domain` directly, reusing its own
`intersect_sound` premise.)
A concrete `backward_domain` interpretation inherits all four query
functions with no extra proof obligation *once `Numeric_Queries.thy`
is in scope at the point that interpretation is processed* — `Sign_Backward.thy`
needed an explicit import added for exactly this reason (see below).

The derivation is a **sound default, not a mandatory implementation**.
`sublocale backward_domain \<subseteq> sound_numeric_queries` was deliberately
never added — see "Why no automatic sublocale" below.

### `Abstract_Checks.thy` — expression/check evaluation

Owns `abstract_check_domain` (the numeric queries plus a sound
`aval_abs` over a state concretization `γS`), the three-valued
`check_query` over `exp`, the three-way `classify_check`,
and `abstract_checks_proven`, the node-indexed bridge to
`Checks.thy`'s domain-independent `checks_proven`).

`Check_Proved`/`Check_Refuted` are universal claims over the abstract
value's whole concretization, not witness-based: `Check_Refuted` means
every concrete state the abstract state represents falsifies the
condition, not that one counterexample was found. `Check_Unknown` means
neither `check_true` nor `check_false` could be established — the
condition may in fact always hold, always fail, or vary; the classifier
makes no claim either way.

### Per-domain instances

`Sign_Classify.thy` and `Interval_Classify.thy` each do one
`global_interpretation abstract_check_domain ...`, `defines`-exporting
`<domain>_check_query`/`<domain>_classify_check`/`<domain>_checks_proven`.
Neither restates the Boolean recursion, the classification logic, or the
`checks_proven` bridge — that would be duplicating what `Abstract_Checks.thy`
already proves once.

They differ only in **which four query functions they feed in**:

| | Sign (`Sign_Classify.thy`) | Interval (`Interval_Classify.thy`) |
| --- | --- | --- |
| `less_true`/`less_false` | derived from `inv_less_sign` | specialized, compares interval bounds directly |
| `eq_true`/`eq_false` | derived from `sign_less_false` / semantic intersection (`meet_sign`) | specialized, compares interval bounds directly |
| Source | `Sign_Numeric_Queries.thy` | `Interval_Numeric_Queries.thy` |

### Solver frontends: the unit-context assembly

Each domain routes its own transfer functions and executable mirror through
the shared D/G generator, solves with the vendored `TD_side` solver, and
exposes the result as an `analysis_result` table indexed by `(node, context)`.

`Routed_DG_Analysis.thy` performs that assembly once, and `Unit_DG_Analysis.thy`
instantiates it at the unit context. `routed_dg_pipeline` is the construction
half — equation system, solve, covered keys, reader, result table, globals,
report — and carries no correctness assumptions; `routed_dg_analysis` adds the
domain and solver contracts, and `unit_dg_analysis` derives the published
context-free soundness theorems. A domain instantiates it by naming its
executable transfer, its callee entry, the state a run starts from, the solver,
the check classifier and the facts that make them sound. The generated
`Sign_Analyses.thy` holds `global_interpretation sign_rule: unit_dg_analysis ...
for r`, taking the global update rule as a parameter; a caller reads
`sign_rule.result`, `sign_rule.state_at` and `sign_rule.report` at a rule. Every
domain, Int included, carries the same registration beside `<d>_es_rule` and
`<d>_cs_rule` for the two contextual policies.

The node-soundness bridge is generic and proved once inside
`unit_dg_analysis`. `result_node_sound_closure` composes
`dg_analysis_adapter.analyse_result_node_sound` (`DG_Analysis_Adapter.thy`)
with the unit-context collapse `activation_collect_unit_eq_ltr_collect`
(`Routed_Context_Unit.thy`), so it connects the solved table back to
`ltr_collect` at *any* covered node — not only the solver's own query seed
(`cfg_exit`); `result_node_sound` is its corollary under `vars_cover`. A
domain inherits both from its interpretation rather than re-exporting the
adapter lemma under a spine prefix of its own. That is what lets a check be
discharged at its own CFG node without forwarding stores to the procedure
exit.

The computed table and transfer soundness are necessarily per-domain; the
bridge above them is not.

### `render_dot.ml` — rendering

Rendering lives entirely in OCaml, outside every soundness theorem.
`Context_graph.status_of` (`cli/result/context_graph.ml`) gives each node one
status from its `result_state`: `Unreachable` when `state_value` is `Bot`;
otherwise the strongest verdict among its `state_checks` and those
`state_diagnostics` that are not `Check_Proved`, ordered `Refuted`, `Unknown`,
`Proved`; no status when the node has neither. A proved division is not a
finding, so it never colours a node.

`Render_dot.node_attrs` (`cli/render/render_dot.ml`) is the single
status-to-style mapping: `Proved` dark green on pale green, `Refuted` firebrick
on misty rose, `Unknown` dark goldenrod on light goldenrod, `Unreachable` a
dashed gray box. It reads only the status and the node kind — nothing
domain-specific. A node without a status is styled by kind: a light-green box
for a statement point, an orange double circle on light yellow for every
procedure entry and exit, so a refuted check's red never collides with an
unrelated procedure-exit node.

## Why no automatic sublocale

The natural-looking generalization —
`sublocale backward_domain \<subseteq> sound_numeric_queries` — was tried and
reverted (`docs/history/CHECK_DISCHARGE_HANDOFF.md`, "Numeric-query theory split").
It answers two different questions, both against it:

1. **Should the derived queries be canonical for every backward domain?**
   No — they inherit the precision of that domain's backward operators, which
   need only be sound. A domain may expose sharper direct queries without
   making those queries part of backward filtering. Interval does this for
   bound comparisons, while its normalized `intersect_ivl` also makes the
   generic equality-refutation default precise on disjoint intervals. An
   automatic sublocale would still force one interface choice on every domain.
2. **Would a downstream `sublocale` declaration have worked anyway?**
   The specific experiment tried it in the wrong place and failed for a
   second, narrower reason: the relation was declared in a theory
   processed *after* Sign's own `backward_domain` interpretation, so
   Isabelle's sublocale-to-existing-interpretation composition never
   reached back into it. Even with correct theory placement (the
   `Numeric_Queries.thy` split now gives every future domain the
   option to import it *before* interpreting `backward_domain`), an
   unconditional sublocale would still be the wrong canonical
   architecture for reason 1 — reason 2 was a placement bug in one
   experiment, not the standing argument against the design.

Each domain instead interprets `sound_numeric_queries` explicitly and
chooses its own source for the four functions: Sign takes the generic
derivation because it is exact there; Interval keeps its specialized
tables because the generic derivation would be a real precision loss.

## Worked examples

`Example_Checks_Store_Only.thy` (Sign) and
`Example_Interval_Checks_Store_Only.thy` (Interval) compile a program,
run the verified solver, and discharge checks at each check's own node —
one proved, one refuted, one unknown, plus a `checks_proven` bridge
exercised on the singleton that is actually true.
`Example_Parity_Checks_Store_Only.thy` runs the same trio for Parity. The
Interval example additionally demonstrates a precision gain: a bound Interval proves
outright (`x < 11` after narrowing `x` to `[1,9]`) that Sign's `SPos`
alone cannot.

## Contextual result and GraphViz presentation

Every analysis produces one canonical, contextual `analysis_result`: a table
from `(pp, ctx)` to `Lifted abs_state | Bot`. A context-free run
(`--context none`) is not a special case -- its table has the single unit
context. `run_result_of` (`Analysis_Run.thy`) reads that one table, never the
raw solver map, and publishes it as a structured `run_result`; `run_voblint`
applies `string_of_abstract_value` to every abstract value in it through
`map_run_result`. Everything below that line is OCaml:

```text
                       verified solver
                             |
                             v
                      analysis_result
               (pp, ctx) -> Lifted abs_state | Bot
                             |
                             |  run_result_of, map_run_result   [Isabelle]
                             v
                   String.literal run_result
     res_cfg  res_contexts  res_states  res_routes
     res_checks  res_globals  res_diagnostics
                             |
                +------------+-------------+                   [OCaml]
                |                          |
                v                          v
     res_checks, res_diagnostics    Context_graph.build
     (joined over contexts)         one node per (pp, ctx),
                |                   states never joined
                |                          |
                |       +---------+--------+--------+----------+
                |       v         v                 v          |
                |   Render_dot  Render_snapshot   Report_dir / |
                |   (--dot)     (--graph-snapshot) Render_xml  |
                |                                  (--html)    |
                +------------------------------------------+   |
                                                           v   v
                                             Render_json (browser playground)
```

`Context_graph.build` (`cli/result/context_graph.ml`) reads only the result:

- **Nodes.** One per `res_states` entry, i.e. per `(point, context index)` the
  solve covered. The identifier is `<procedure>_<point>_ctx<n>`, where `n`
  numbers the context within its procedure in the order the states list it, so
  an identifier does not move when another procedure gains or loses a context.
- **Clusters.** One per `(procedure, context)`, labelled
  `<procedure> / <context>`; the context label comes from `res_contexts`
  (`unit`, the rendered entry values, or `call-string=...`).
- **Intra edges.** Each intra edge of `res_cfg`, drawn inside one context when
  both endpoints are covered in it.
- **Call edges.** At every covered caller node, `route_targets` of the matching
  `res_routes` entry names the callee context indices the call enters. Each
  target gets an `Enter` edge to the callee's entry and a `Combine` edge from
  the callee's `FunctionResult` back to the continuation in the caller's
  context; a `Call_to_return` edge joins caller and continuation in the caller's
  context. OCaml never re-derives a route. `route_targets` is `[]` when the
  caller state is `Bot` or entering yields a bottom frame (`entered_targets`),
  and a live call with no target gets a `call ... [not entered]` finding.

A node whose `state_value` is `Bot` carries `Unreachable` as its status, set
once in `Context_graph.status_of`. Renderers read that constructor
(`Render_dot.node_attrs`, the snapshot's `[unreachable]`, `Render_xml.is_dead`,
the JSON `status` field); they never infer deadness from label text. A node's
findings are `unreachable`, one `check <exp>` line per `state_checks` entry
(suffixed `[dead]` when that context's verdict is `Bot`), one message per
refuted or unknown division in `state_diagnostics`, and the unentered calls
above.

### What a node shows, and where globals go

A graph node's `bindings` are the enclosing procedure's formals, then the
locals it assigns, identically for `--context none`, `entry-state` and
`call-string`. Declared globals and the return slot `#ret` are **not** among
them: the node record keeps both apart (`globals`, `ret`), and only the browser
JSON emits them. `Render_dot` labels a node with its point and findings and
puts the full state in the tooltip; `Render_json` sends the browser the clusters
and edges with their roles, which the playground lays out and styles itself;
`Render_snapshot` lists status, bindings and findings; `Report_dir` writes the
same lines to `nodes/<id>.xml` through `Render_xml`, one `<analysis>` block per
`--analysis` domain.

`res_globals` lists the constraint system's global unknowns, the same set
Goblint's globals pane iterates: `Global_Shared`, the analysis-wide slot, then
for `main` and every procedure one `Global_Seed f (Some i)` per context index
`i` its entry was solved at, holding the state calls push into that entry. A
procedure no solved context enters is listed once as `Global_Seed f None` with
state `Bot`. Each registration's `result_with_globals` returns the table and
these unknowns off one solve. `Result_text.global_rows` names the rows
(`Global`, `enter f`, `enter f @ <context>`) for the HTML globals pane; the
browser JSON's `seeds` drops `Global_Shared` and links each seed to its entry
node.

### CLI contract

```text
--context none|entry-state|call-string   context sensitivity (analysis-level)
--context-depth N                        call-string bound
--globals join|per-origin|warrow|warrow-per-origin
                                         side-effect update rule
--dot | --graph-snapshot | --html        what to render from the one result
```

There is exactly one graph rendering. A check that is `Dead` in one context and
`Decided` in another -- or two live contexts that disagree on the same check --
stays visible as distinct nodes. See `tests/regression/11-graph-snapshot/`
(`04-expanded_three_contexts.vimp` through `09-expanded_dead_route.vimp`) for
worked examples.

## Known limitations (not yet addressed)

- The three checks compiled from `Example_Interval_Checks_Store_Only.thy`
  generate visible `nop` edges between them: the compiler gives each check
  its own node. The `checks` relation already permits multiple
  checks at one program point (`(pp * bexp) set`, not a function from
  `pp`); the compiler currently happens to allocate one node per check,
  but the data model does not require that.
- Every selectable domain has a check-discharge instance:
  `Sign_Classify`, `Interval_Classify`, `Parity_Classify`,
  `Congruence_Classify` and `Int_Classify`.
