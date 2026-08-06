# Next work

GitHub Project 8 contains scheduling and dependencies. The stable technical
directions are:

## Context abstractions

Define finite executable context domains with a proved abstraction relation to
concrete activations. Evaluate recursive and widening-heavy examples separately
from repeated-call examples.

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

## Equality backward narrowing

Investigate equality backward narrowing. Current `bfilter` handles `Eq` only
on the true branch; disequality guards do not refine the abstract state. A
future `inv_eq` operator, analogous to `inv_less`, could support both
equality and disequality narrowing. This is separate from the boolean
`eq_true`/`eq_false` query interface used for check classification.

## Source extensions

Arrays and richer types require syntax, operational semantics, compiler,
transfer, and soundness extensions. Add them as explicit vertical slices.

## Release gate

Keep live comments timeless, maintain a zero `sorry` inventory, and run the
complete batch build before merging proof changes.
