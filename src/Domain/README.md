# Domain

What an abstract value is, how reachability is lifted over a carrier, and how
the non-relational analyses represent stores. The counterpart of Goblint's
`goblint.domain` lattice constructors and framework reachability lift, plus
the concretizations and soundness obligations required by Isabelle.

Depends on `Voblint_VIMP` (stores, expressions) and the vendored `TD`
session (the `widening`/`narrowing`/`warrowing` classes). Nothing here
mentions a graph, an equation, or a solver run.

| File | Role |
| --- | --- |
| `Abstract_Domain.thy` | Executable and sound abstract-value classes, concretization bounds, widening, and the TD warrowing carrier constraint |
| `Reachability_Lift.thy` | Generic `Bot`/`Lifted` reachability carrier, lattice and solver-update instances, concretization, mapping, and normalized transfer combinators |
| `Nonrelational_State.thy` | Pointwise `'a abs_state = vname => 'a`, product concretization, and witness-bottom detection |
| `Nonrelational_Reachability.thy` | Composition of pointwise stores with the generic reachability lift: `gamma_state_lift` and `is_bot_state_lift` |
| `Backward_Domain.thy` | `backward_domain` and `backward_domain_refined`: inverse operators and the derived `afilter`/`bfilter` guard refinement, the counterpart of Goblint's `BaseInvariant` |
| `Abstract_Numeric_Queries.thy` | The `less`/equality queries a `backward_domain` answers for free, and the `abstract_numeric_queries` interface the check layer consumes |
