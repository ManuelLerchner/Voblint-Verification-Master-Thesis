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

## Placement-aware D/G generation

The generic (hook-parametric) D/G generation and soundness route
(`sound_dg_hooks`), and the classifier-parametric interval transfer/readback
it uses, are proved sound end-to-end for `Example_Interval_Placement.thy`,
`Example_Sign_Placement.thy`, and two migrated flagships
(`Exec_Sign_DG_Run.thy`, `Example_Parity_DG_Flagship.thy`).

Further migration is **cancelled**, not deferred. A boundary audit
(`docs/reviews/M4_SPINE_BOUNDARY_AUDIT.md`) found that `sound_dg_spec` — the
classic route's own locale — is already classifier-generic and not a
duplicate implementation of anything; the migrated flagships grew 5-6x in
size for no soundness or drift risk that existed before migration. Interval,
Mixed, CallString, and Ctx examples stay on `sound_dg_spec`/
`dg_ctx_activation`/`routed_context` permanently; `sound_dg_hooks` is the
low-level framework-construction API for analyses that genuinely need
custom placement/hooks, not the default route for ordinary domains. The one
open item is unifying `sound_dg_spec` and `sound_dg_hooks` internally (one
`sublocale`/`interpretation`, reduction lemmas already exist in
`DG_Ctx_Activation.thy`) so the framework has a single proof of the
edge/enter/combine soundness obligation instead of two — with zero change to
any example's API. See the audit's Section 4 for the scoping note.

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

## Source extensions

Arrays and richer types require syntax, operational semantics, compiler,
transfer, and soundness extensions. Add them as explicit vertical slices.

## Release gate

Keep live comments timeless, maintain a zero `sorry` inventory, and run the
complete batch build before merging proof changes.
