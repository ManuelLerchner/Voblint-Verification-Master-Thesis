# Check-discharge architecture

Overview of how a compiled `__voblint_check(...)` condition becomes both a
GraphViz-rendered proof status and a semantic soundness guarantee. This is
a map of responsibilities across layers, not a proof-status inventory —
proof status lives in the `.thy` files themselves (`docs/PROOF_PHASES.md`).

## Pipeline

`abstract_check_domain` produces two independent outputs from the same
node-indexed abstract environment: an *executable classification* that
GraphViz renders directly, and a *logical discharge* that `checks_proven`
turns into a semantic guarantee. GraphViz never consumes `checks_proven`
— rendering does not depend on proving anything.

```text
VIMP source
    |
    | compile_prog (VIMP_Proc_to_CFG)
    v
CFG + checks : (pp * texp) set     -- zero or more compiled checks per node
    |
    | verified TD solver, per domain (<Domain>_Ctx_None_Sound)
    v
node-indexed analysis_result       -- analyse_<domain>_ctx_result_for
                                   ::   (vname => bool) -> pname -> imp_prog
                                     -> (unit, 'a abs_state) analysis_result
    |
    | domain-specific abstract_numeric_queries instance
    v
abstract_check_domain (Abstract_Checks.thy)
    |
    +--> classify_check                              [executable]
    |        |
    |        v
    |    Check_Proved / Check_Refuted / Check_Unknown
    |        |
    |        v
    |    check_result_annotation (Analysis_GraphViz.thy)
    |        |
    |        v
    |    rendered CFG, proof status as node color
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
frontend and `abstract_numeric_queries` instance below that line.
`Sign_Checks.thy`, `Interval_Checks.thy`, `Parity_Checks.thy` and
`Int_Checks.thy` are thin instantiations of the generic layers, not separate
implementations of the pipeline. Each reads its per-node state through
`analyse_<domain>_ctx_result_for`'s `analysis_result` table -- the routed
producer's own solved table at `prog_main_name` -- and interprets the generic
`analysis_surface` locale over it.

## Layer responsibilities

### `Abstract_Domain.thy` — lattice and backward refinement

Owns `sound_domain`/`abstract_domain` (the type-class every domain value
type instantiates), `semantic_intersection`, `backward_domain` (guard narrowing: `inv_less`,
`inv_eq`, `afilter`/`bfilter`), and `backward_domain_mono`. Nothing here
knows about checks. `derived_less_queries`/`derived_eq_true_from_less`/
`derived_eq_false_from_intersection` do **not** live here — see the next layer.

### `Abstract_Numeric_Queries.thy` — atomic-value entailment/refutation

Owns the `abstract_numeric_queries` locale (`less_true`, `less_false`,
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
functions with no extra proof obligation *once `Abstract_Numeric_Queries.thy`
is in scope at the point that interpretation is processed* — `Sign_Backward.thy`
needed an explicit import added for exactly this reason (see below).

The derivation is a **sound default, not a mandatory implementation**.
`sublocale backward_domain \<subseteq> abstract_numeric_queries` was deliberately
never added — see "Why no automatic sublocale" below.

### `Abstract_Checks.thy` — expression/check evaluation

Owns `abstract_expression_domain` (adds `gamma_state`/`aval_abs` on top of
the numeric queries) and `abstract_check_domain` (mutually recursive
`check_true`/`check_false` over `texp`, the three-way `classify_check`,
and `abstract_checks_proven`, the node-indexed bridge to
`Checks.thy`'s domain-independent `checks_proven`).

The check path carries no typing environment. A compiled `EA_Check` holds an
already-elaborated `texp`, so `checks_proven` states `truthy (teval c s)` and
each domain interpretation supplies its own `aval_<domain>_t` directly. The
soundness obligation is then that domain's own `aval_<domain>_t_sound` — the
same evaluator on both sides of the concretization, with no `default_tyenv` or
`I32` pinning anywhere in the path. The earlier arrangement stated the
obligation against the unbounded `aval` while the interpretations supplied a
wrapping evaluator, which is why `Interval_Classify`'s discharge was a `sorry`:
that statement is false in general, and it is no longer the statement being
made.

`Check_Proved`/`Check_Refuted` are universal claims over the abstract
value's whole concretization, not witness-based: `Check_Refuted` means
every concrete state the abstract state represents falsifies the
condition, not that one counterexample was found. `Check_Unknown` means
neither `check_true` nor `check_false` could be established — the
condition may in fact always hold, always fail, or vary; the classifier
makes no claim either way.

### Per-domain instances

`Sign_Checks.thy` and `Interval_Checks.thy` each do one
`global_interpretation abstract_check_domain ...`, `defines`-exporting
`<domain>_check_true`/`<domain>_classify_check`/`<domain>_checks_proven`.
Neither restates the Boolean recursion, the classification logic, or the
`checks_proven` bridge — that would be duplicating what `Abstract_Checks.thy`
already proves once.

They differ only in **which four query functions they feed in**:

| | Sign (`Sign_Checks.thy`) | Interval (`Interval_Checks.thy`) |
| --- | --- | --- |
| `less_true`/`less_false` | derived from `inv_less_sign` | specialized, compares interval bounds directly |
| `eq_true`/`eq_false` | derived from `sign_less_false` / semantic intersection (`meet_sign`) | specialized, compares interval bounds directly |
| Source | `Sign_Numeric_Queries.thy` | `Interval_Numeric_Queries.thy` |

### Solver frontends: `<Domain>_Ctx_None_Sound.thy`

Domain-specific, not domain-generic: each routes its own transfer functions
and executable mirror through the shared D/G generator, solves with the
vendored `TD_side` solver, and exposes the result as
`analyse_<domain>_ctx_result_for`, an `analysis_result` table indexed by
`(node, context)`.

The node-soundness bridge is generic and proved once:
`dg_analysis_adapter.analyse_result_node_sound` (`DG_Analysis_Adapter.thy`),
which each domain re-exports under its own spine prefix — e.g.
`lemmas sctx_result_node_sound = sctx_adapter.analyse_result_node_sound`
in `Sign_Checks.thy`. Composed with the unit-context collapse
`activation_collect_unit_eq_ltr_collect` (`Routed_Context_Unit.thy`), it
connects the solved table back to `ltr_collect` at *any* covered node — not
only the solver's own query seed (`cfg_exit`). That is what lets a check be
discharged at its own CFG node without forwarding stores to the procedure
exit.

The computed table and transfer soundness are necessarily per-domain; the
bridge above them is not.

### `Analysis_GraphViz.thy` — rendering

`check_result_annotation :: check_result -> texp -> graphviz_node_annotation`
is the single status-to-style mapping (`Check_Proved` dark green,
`Check_Refuted` red, `Check_Unknown` grey), shared by every domain's
worked example. It depends only on `check_result` and `texp` — nothing
Sign- or Interval-specific. The generic entry/exit/default node styling
(`analysis_node_attrs`) uses green/light-yellow for entry and neutral
gray for exit, so a refuted check's red never collides with an unrelated
procedure-exit node.

## Why no automatic sublocale

The natural-looking generalization —
`sublocale backward_domain \<subseteq> abstract_numeric_queries` — was tried and
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
   `Abstract_Numeric_Queries.thy` split now gives every future domain the
   option to import it *before* interpreting `backward_domain`), an
   unconditional sublocale would still be the wrong canonical
   architecture for reason 1 — reason 2 was a placement bug in one
   experiment, not the standing argument against the design.

Each domain instead interprets `abstract_numeric_queries` explicitly and
chooses its own source for the four functions: Sign takes the generic
derivation because it is exact there; Interval keeps its specialized
tables because the generic derivation would be a real precision loss.

## Worked examples

`Example_Checks_Store_Only.thy` (Sign) and
`Example_Interval_Checks_Store_Only.thy` (Interval) compile a program,
run the verified solver, and discharge checks at each check's own node —
one proved, one refuted, one unknown, plus a `checks_proven` bridge
exercised on the singleton that is actually true. The Interval example
additionally demonstrates a precision gain: a bound Interval proves
outright (`x < 11` after narrowing `x` to `[1,9]`) that Sign's `SPos`
alone cannot.

## Contextual result and GraphViz presentation (collapsed vs. expanded)

The pipeline above is per-node and context-independent. A context-sensitive
analysis (currently `--context entry-state`) produces a canonical,
contextual `analysis_result` instead, and everything downstream of the
solver -- checks, collapsed GraphViz, expanded GraphViz -- reads that one
table, never the raw solver map:

```text
                       verified solver
                             |
                             v
                      analysis_result
               (pp, ctx) -> Reachable abs_state | Unreachable
                             |
           +-----------------+-----------------+
           |                 |                 |
           v                 v                 v
     contextual        collapsed graph    expanded graph
       checks         (Analysis_GraphViz)  (Analysis_GraphViz)
  (analyse_ctx,      one node per pp,     one node per (pp, ctx),
   aggregate_         contextual states    states never joined
   verdicts)           joined for
                        rendering
           |                 |                 |
           +-----------------+-----------------+
                             |
                             v
                        CLI (voblint)
```

`lookup_context`/`contexts_at` are the only reads either graph mode
performs against the result. Collapsed and expanded are **the same
canonical `analysis_result`, rendered two ways** -- not two analyses, and
not two solves: `analysis_graph_config.route` (partial -- `None` on an
unreachable caller or an entered-bottom callee frame, never a real `'ctx`
value doubling as a sentinel) decides what edges to draw, `context_key`
decides presentation order, and `node_annotation` reads the context, but
none of that changes what the solver computed.

### CLI contract

```text
--context none|entry-state          context sensitivity (analysis-level)
--context-graph collapsed|expanded  rendering mode (presentation-level)
```

`--context-graph` only selects how an already-computed contextual result
is drawn under `--dot`/`--dot-full`/`--graph-snapshot`; it never affects
analysis precision, the solver, or which contexts get computed.
`collapsed` (the default) joins every context's state per CFG node for
rendering. `expanded` draws one node per `(pp, ctx)` pair instead, so a
check that is `Dead` in one context and `Decided` in another -- or two
live contexts that disagree on the same check's verdict -- stays visible
as distinct nodes rather than collapsing into one rendering. See
`tests/regression/11-graph-snapshot/06-collapsed_three_contexts.vimp`
through `09-expanded_dead_route.vimp` for worked collapsed/expanded pairs.
`--context-graph expanded` without `--context entry-state` is a CLI
error, not a silent fallback to collapsed.

## Known limitations (not yet addressed)

- The three checks compiled from `Example_Interval_Checks_Store_Only.thy`
  still generate visible `nop` edges between them — zero-width check
  compilation remains a possible, unstarted, later compiler milestone
  (`docs/NEXT_STEPS.md`). The `checks` relation already permits multiple
  checks at one program point (`(pp * texp) set`, not a function from
  `pp`); the compiler currently happens to allocate one node per check,
  but the data model does not require that.
- No domain besides Sign and Interval has a check-discharge instance.
  Parity is not wired up.
