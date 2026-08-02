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
