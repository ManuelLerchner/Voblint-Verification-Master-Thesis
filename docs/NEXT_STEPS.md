# Next work

GitHub Project 8 contains scheduling and dependencies. The stable technical
directions are:

## Context abstractions

Define finite executable context domains with a proved abstraction relation to
concrete activations. Evaluate recursive and widening-heavy examples separately
from repeated-call examples.

Tracked in detail in #108 (references #66, #77); summary below, keep the
two in sync if either changes.

Post-#66, `routed_context` (`Routed_Context.thy`) is real Core-level
infrastructure, not example-level: it discharges the CALL/COMB obligations
once, generically in a `route`/`enterc` pair and context type `'c`. Four
interpretations already exist, including `Example_Interval_DG_Ctx_Flagship
.thy`'s `route_ivl`/`ivl_enterc` -- a genuinely value-derived context
(`'c = ivl`, not call-site history), with `contexts_distinct` proved `by
eval` for two calls with different argument values landing in separate,
un-joined contexts. So the CALL/COMB soundness machinery this feature needs
already exists and is reusable. What's still missing:

**Finiteness dependency resolved (2026-08-10).** `'c` carries no
`::finite` sort constraint anywhere in `routed_context`/`dg_ctx_activation`/
the TD solver -- `solve_dom` is a per-run computational-domain predicate,
not a type-class constraint, and `Interval_Exec_Sound.thy`'s
`ivl_exec_terminates_via_solve_c` already discharges it empirically for the
flat analysis, with soundness proved unconditionally from there. So #77
("Context-bounding lifters") is not a termination blocker for G1: unbounded
entry-state contexts can ship on the same "if the solver returns, the
result is sound" contract the flat analysis already relies on.

**Exactness boundary found while grounding G1 (2026-08-10).**
`route_enterc_agree` (`Routed_Context.thy:101-107`) is a literal equality
required across every concretization of the caller's entered abstract
state. Since `enterc` decodes a concrete value to an exact point, the
equality only holds when the caller's abstract value at each
context-forming formal is itself exact -- true of the flagship's
literal-constant calls, not guaranteed generally. #77 resurfaces here for a
different reason than termination: making the equality hold for non-exact
callers needs `'c` to carry an order with the solver monotone in it --
structurally #77's "Context Widening", reached from the routing-soundness
side rather than the termination side. #108's G1-G5 plan (in the issue):

1. **G1 -- generic exact-entry context construction (infrastructure, not
   yet a general CLI feature). Done, batch-green (2026-08-10).**
   `route_ivl`/`ivl_enterc` were hardcoded to one formal name (`"p"`), built
   for that one flagship program. Replaced with `formals_context`/
   `formals_route`/`formals_route_gen`/`formals_at_call_site`/
   `formals_enterc` (`Routed_Context.thy`, domain-generic, no `Ivl`
   reference), reusing `CallEdge`'s own `pars` field -- no separate
   `formals(Pi(q))` lookup needed -- and discharged via a `routed_context`
   interpretation across `Example_Interval_DG_Ctx_Flagship.thy`,
   `_Ctx_Sound.thy`, `_Ctx_Collect.thy`, and `Example_Interval_Source_Ctx.thy`
   (the last caught only by the batch build, not interactive I/Q, since it
   was never opened during development). No procedure identity folded into
   `'c`: `vars`/`seed_key` already pair `'c` with `pp`, which disambiguates
   by callee. Proved at exact call sites (matching the flagship); the
   exactness precondition above is not lifted -- that's G2.
2. **G2 -- abstract context coverage semantics (research item).** Traced
   deeper than `routed_context`: `activation_collect`'s own membership
   condition (`CFG_Local_Trace.thy`'s `key`, consumed by
   `activation_collect_sound` in `Activation_Backbone.thy`) partitions
   concrete traces by *exact* match on the computed context, not coverage.
   A relation `ctx_rep :: 'c_concrete => 'c_abstract => bool` (with
   `ctx_rep c a == c <= a` the natural instance on a shared ordered
   carrier -- today's exact match is the `ctx_rep = (=)` special case)
   needs `activation_collect` redefined against it and
   `valid_ltr_ctx_sound`'s `CALL` case re-derived -- `CFG_Local_Trace.thy`
   + `Activation_Local_Sound.thy` + `Activation_Backbone.thy`, not just
   `Routed_Context.thy`. Likely converges with #77's "Context Widening".
   Acceptance case: `x := random(); p(x);` analyzable under `--context
   entry-state` without a statically proven singleton argument. Only after
   this does `--context entry-state` become a claim about arbitrary
   programs rather than exact-argument call sites.
3. **G3 -- executable context-sensitive Interval endpoint,** analogous to
   `analyse_interval_td_raw` but keyed on `(pp x ctx)`, same `solve_dom`/
   `solve_c` convention, `export_code`'d.
4. **G4 -- context-aware checks/reporting,** aggregating conservatively
   across reachable contexts (all Proved -> PROVED, all Refuted -> REFUTED,
   otherwise UNKNOWN) without joining abstract states first.
5. **G5 -- CLI exposure + precision witness.** `--context none` (current,
   default) / `--context entry-state`; regression: two calls at distinct
   exact argument values, `--context none` -> `UNKNOWN`, `--context
   entry-state` -> `PROVED`. Open question: whether G3-G5 ship on G1's
   exact-entry contract with a runtime-checked exactness precondition
   (the same idiom `solve_dom` uses for termination), or wait for G2.

Arbitrary `gs`/`--flow-insensitive` stays explicitly out of scope -- see
#66's M4 / `docs/SEIDL_CONTEXT_LIFECYCLE_MIGRATION.md`; `declared_global p`
stays invariant across whatever this lands as.

## D/G communication

Improve analysis-defined shared-state reads and publications where a concrete
precision example requires it. Preserve the generic separation between local
`D` facts and shared `G` facts.

## Placement-aware D/G generation (settled, no further action planned)

`sound_dg_spec` is a proved `sublocale` of `sound_dg_hooks`
(`DG_Soundness.thy`, `DG_LTR_Sound.thy`): one implementation, two abstraction
levels. `sound_dg_spec` is the concise adapter every ordinary analysis
interprets (one locale interpretation, no per-CFG-node proof burden);
`sound_dg_hooks` is the framework-construction API for analyses whose D/G
structure needs arbitrary hook trees, such as owner-sensitive placement.
Sign, Interval, Parity, Mixed, CallString, and Ctx all stay on
`sound_dg_spec`/`dg_ctx_activation`/`routed_context`; two examples,
`Example_Interval_Placement.thy` and `Example_Sign_Placement.thy`, exercise
`sound_dg_hooks` directly as framework validation, not as templates.

This closes a prior migration attempt: two flagships
(`Exec_Sign_DG_Run.thy`, `Example_Parity_DG_Flagship.thy`) were migrated onto
`sound_dg_hooks` directly on the mistaken premise that `sound_dg_spec` was a
duplicate implementation. Both grew 5-6x for no closed soundness/drift risk
(`docs/reviews/M4_SPINE_BOUNDARY_AUDIT.md`) and were reverted. No further
example migration to `sound_dg_hooks` is planned; do not propose one without
new evidence that a specific analysis's D/G structure genuinely needs the
hook-tree level `sound_dg_spec` cannot express.

## Domain composition

No generic reduced-product constructor is planned. `sound_dg_spec`'s carriers
are already opaque, and `Rel_Order_Domain.thy` demonstrates a non-`abs_state`
instance against the unmodified framework; see
`docs/RELATIONAL_DOMAIN_ARCHITECTURE_DECISION.md` (Option 4) for the settled
architecture. New heterogeneous or relational analyses are added directly
against `sound_dg_spec`, not through a shared product/reduction layer.

## Numeric precision

Improve interval guards, loop invariants, and widening policies through concrete
examples. Keep precision engineering independent of the concrete semantic
reference model.

## Equality backward narrowing (done)

`inv_eq`, analogous to `inv_less`, is a `backward_domain` operator alongside
`inv_less`/`inv_plus`/`inv_minus`/`inv_times` (`Abstract_Domain.thy`).
`bfilter`'s `Eq` case narrows through it on both branches, not only the true
branch. Sign has a real, monotone instance (`inv_eq_sign`,
`Sign_Backward.thy`); Interval keeps a sound identity fallback with the
precision gap documented in-theory (`Interval_Backward.thy`). This is
separate from the boolean `eq_true`/`eq_false` query interface used for check
classification (`Abstract_Numeric_Queries.thy`).

## Source extensions

Arrays and richer types require syntax, operational semantics, compiler,
transfer, and soundness extensions. Add them as explicit vertical slices.

## Release gate

Keep live comments timeless, maintain a zero `sorry` inventory, and run the
complete batch build before merging proof changes.
