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

1. **Context key.** All formals, or their abstract values; whether locals
   beyond formals ever belong in the key; whether the procedure name is
   necessarily part of it.
2. **Generic entry abstraction.** `route_ivl`/`ivl_enterc` are hardcoded to
   one formal name (`"p"`), built for that one flagship program. Replace
   with `context(p, entry_state) = ` a projection of `entry_state` onto
   `formals(p)`, working for any procedure.
3. **Finite termination -- the central risk.** No finiteness guarantee for
   a value-derived `'c` beyond the ambient `'c::finite` + solver
   `solve_dom` hypothesis discharged per-instantiation (a call-string
   truncated to length `k` is finite by construction; a raw interval
   context is not). Same gap #77 ("Context-bounding lifters") tracks
   generally -- reuse whatever lands there rather than inventing a
   one-off bounding policy here.
4. **Executable/export API.** (2), instantiated through `routed_context`,
   `export_code`'d.
5. **CLI exposure.** `--context none` (current, default) /
   `--context entry-state`, plus report semantics.
6. **Acceptance regression.** A program with two calls to the same procedure
   at distinct argument values: `--context none` -> `UNKNOWN`,
   `--context entry-state` -> `PROVED`.

Do not start by generalizing `"p"` to a list of variable names in isolation
-- that resolves the syntactic hardcoding (item 2) while leaving item 3
(unbounded context creation) untouched, the actual blocker to this being a
general feature rather than a second bespoke example. Arbitrary `gs`/
`--flow-insensitive` is explicitly out of scope here -- see #66's M4 /
`docs/SEIDL_CONTEXT_LIFECYCLE_MIGRATION.md`; `declared_global p` stays
invariant across whatever this lands as.

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
