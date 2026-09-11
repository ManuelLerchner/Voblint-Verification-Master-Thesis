# Next work

GitHub Project 8 contains scheduling and dependencies. The stable technical
directions are:

## Context abstractions

Entry-state and call-string contexts are done for all five domains, from the
collecting semantics to the CLI:

- **Semantics.** `call_context_rel` admits the contexts of one concrete call,
  `trace_context` threads them over traces, and `activation_collect` is indexed
  by them (`LTR_Activation_Context`). A functional policy embeds through
  `call_context_rel_of_fun`.
- **Routing.** `routed_context_base_hetero` (`Routed_Context`) discharges the call
  and combine obligations once for any context type `'c`;
  `Entry_State_Routed_Context` and `Call_String_Routed_Context`
  (`Voblint_Routing`) instantiate it. `'c` carries no `finite` sort constraint:
  termination is the per-run `solve_dom` premise, as for the flat analysis.
- **Endpoints.** `routed_dg_analysis.entry_state_activation_collect_sound` and
  `fun_route_activation_collect_sound` bound each bucket;
  `sound_table_of_activation` and `sound_table.source_sound` (`Analysis_Run_Sound`)
  reach a source run.
- **Checks and rendering.** `classify_checks_verdicts` joins verdicts over the
  contexts the solved table covers (`contexts_at`), with `Dead` kept apart from
  the three check results; `--context-graph expanded` draws one node per
  `(pp, ctx)` pair.
- **Regressions.** `tests/regression/03-procedures/precision/04-two_call_sites_entry_state.vimp`
  (precision), `tests/regression/03-procedures/soundness/01-entry_state_random_arg.vimp`
  (one wide context), `tests/regression/13-full-state-dot/02-entry_state_context_join.vimp`
  (the collapsed join).

Arbitrary `gs`/`--flow-insensitive` stays out of scope; `declared_global p` is
the classifier everywhere.

### Open: context bounding

- **Call strings have a bounded candidate space, which is less than bounded.**
  `cs_route k` truncates every context to length `<= k` (`cs_route_length`), a
  compiled program has finitely many nodes (`cfg_nodes_finite`), and with
  `finite_lists_length_le` the contexts a `k`-bounded routing over a compiled
  program could produce form a finite set --
  `compiled_call_strings_finite`/`compiled_call_string_vars_finite`/
  `compiled_call_string_gk_finite` (`Context_Space_Finite.thy`, `Voblint_Routing`).
  Containment of the node and context halves is a hypothesis of each of them,
  and truncation alone does not give the second. Nor do they bear on
  `solve_dom`: a finite key space does not make a solve terminate. Closing the
  gap means proving key closure under routing. Empirical companion:
  `tests/regression/17-call-string/known-imprecision/01-deep_recursion_bounded_context.vimp`
  (50 levels of recursion under `--context-depth 1`).
- **Entry-state contexts are unbounded.** An entry-state context is a domain
  value (`ivl list`, `sign list`, ...); for an infinite-height domain such as
  `ivl` the context space is unbounded, and the contract is the same `solve_dom`
  premise the flat analysis ships with. Bounding it needs a policy decision
  first -- a gas budget that widens overflow entries into one shared per-callee
  context, a loop-detecting variant, or something else -- and then that policy's
  `call_context_rel` instance. Erhard, Schinabeck, Schwarz, Seidl, "Context gas
  and friends: taming context-sensitivity on the fly" is the reference.

## D/G communication

Improve analysis-defined shared-state reads and publications where a concrete
precision example requires it. Preserve the generic separation between local
`D` facts and shared `G` facts.

## Placement-aware D/G generation (removed)

The hook-tree layer (`sound_dg_hooks`) and the placement examples built on it
were removed; `docs/GOBLINT_ALIGNMENT_REGISTER.md` records why. No further
action is planned.

## Domain composition

No generic reduced-product constructor is planned. `sound_dg_spec_core`'s carriers
are already opaque, and `Rel_Order_Domain.thy` demonstrates a non-`abs_state`
instance against the unmodified framework; see
`docs/RELATIONAL_DOMAIN_ARCHITECTURE_DECISION.md` (Option 4) for the settled
architecture. New heterogeneous or relational analyses are added directly
against `sound_dg_spec_core`, not through a shared product/reduction layer.

## Cross-analysis query composition

Not yet modeled: Goblint's MCP-style `EvalInt` query channel, where every
activated analysis can answer an expression query and a requester meets the
answers, recursively into subexpressions and callee-side `combine`. Voblint's
composite `int_dom` only reduces internally among its own scalar components.
Design investigation tracked in #70; alignment inventory and staging (Phase 3)
in #141.

## Numeric precision

Improve interval guards, loop invariants, and widening policies through concrete
examples. Keep precision engineering independent of the concrete semantic
reference model.

## Equality backward narrowing (done)

`inv_eq`, analogous to `inv_less`, is a `backward_domain` operator alongside
`inv_less`/`inv_plus`/`inv_minus`/`inv_times` (`Backward_Domain.thy`).
`bfilter`'s `Eq` case narrows through it on both branches, not only the true
branch. Sign has a real, monotone instance (`inv_eq_sign`,
`Sign_Backward.thy`); Interval keeps a sound identity fallback with the
precision gap documented in-theory (`Interval_Backward.thy`). This is
separate from the boolean `eq_true`/`eq_false` query interface used for check
classification (`Abstract_Numeric_Queries.thy`).

## Per-domain configuration duplication (done)

The per-domain `*_conf_*` families are no longer written out once per domain.
`assembly/analyses.yaml` drives `scripts/gen_analysis_assembly.py`, which
generates each domain's registrations of `unit_dg_analysis` and
`routed_dg_analysis` (`Voblint_Result`); the equation system, solve, reader,
result table, report and soundness endpoints come from those locales, and the
generated theories only name a domain's own facts.

## Deferred from the Framework and Analysis restructure

Each of these was found with evidence during the restructure and deliberately
not acted on, either because it needs a semantic decision or because it belongs
to a larger migration.

**Resolved variable identities.** `gs :: vname => bool` classifies a *textual
name*, so a state carrier keyed by `location = Local_Location vname |
Global_Location vname` admits entries at the tagging a name does not have.
`resolved_st_is_bot` is the one carrier operation that must consult `gs`, and it
does so only to filter those entries: the quotient's equality observes every
tagged location while the concretization reads back only the one `gs` selects.
`canonical_location` names that filter. The dependency disappears when
elaboration resolves each declaration to its own identity -- one declaration,
one cell, scope as metadata -- which also handles shadowing that a textual name
cannot. Do not split the carrier into local and global maps first: keyed by raw
`vname` they admit the same malformed states, and the migration would be done
twice.

**Names that still need a read before they are changed.** `State_Restriction`
holds only ownership projections, so `Ownership_Restriction` would be more
truthful. `DG_Ctx_Activation` abbreviates a
word its own directory already supplies.

**Refining the override list.** `resolved_st`'s association list is a candidate
for an AFP `rbt` map. Keep it independent of the identity migration above, and
benchmark the generated OCaml rather than Isabelle evaluation.

## Source extensions

Arrays and richer types require syntax, operational semantics, compiler,
transfer, and soundness extensions. Add them as explicit vertical slices.

## Release gate

Keep live comments timeless, maintain a zero `sorry` inventory, and run the
complete batch build before merging proof changes.
