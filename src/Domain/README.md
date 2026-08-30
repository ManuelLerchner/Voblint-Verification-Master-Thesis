# Domain

What an abstract value and an abstract state are. The counterpart of
Goblint's `goblint.domain` library (`Lattice.S` and its functors), plus the
one thing Goblint has no need for: a concretization `gamma` and the
soundness obligations stated against it.

Depends on `Voblint_VIMP` (stores, expressions) and the vendored `TD`
session (the `widening`/`narrowing`/`warrowing` classes). Nothing here
mentions a graph, an equation, or a solver run.

| File | Role |
| --- | --- |
| `Abstract_Domain.thy` | `sound_domain`/`abstract_domain` classes; `'a abs_state = vname => 'a`; the `'a lifted` dead-code lift (Goblint's `Lift`/`Dom`) with witness-bottom and canonical-bottom reasoning; the bounded widening/narrowing/warrowing classes |
| `Backward_Domain.thy` | `backward_domain` and `backward_domain_refined`: inverse operators and the derived `afilter`/`bfilter` guard refinement, the counterpart of Goblint's `BaseInvariant` |
| `Split_State.thy` | Locals and globals as two components with independent value types, isomorphic to the plain state at the homogeneous instance |
| `Abstract_Numeric_Queries.thy` | The `less`/equality queries a `backward_domain` answers for free, and the `abstract_numeric_queries` interface the check layer consumes |
