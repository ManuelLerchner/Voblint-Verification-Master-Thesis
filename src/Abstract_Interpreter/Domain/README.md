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
| `Nonrelational_Reachability.thy` | Composition of pointwise stores with the generic reachability lift: `gamma_state_lift` and `is_empty_state_lift` |
| `Backward_Domain.thy` | `backward_domain`: inverse operators and the derived `afilter`/`bfilter` guard refinement, the counterpart of Goblint's `BaseInvariant` |
| `Backward_Domain_Refined.thy` | `backward_domain_reductive` and `backward_domain_refined`: reductive and monotone inverse operators, and the filtering facts they buy |
| `Abstract_Numeric_Queries.thy` | The `abstract_numeric_queries` interface the check layer consumes, and `numeric_query_judgments`, which builds an instance from four yes/no judgments |
| `Backward_Numeric_Queries.thy` | The four judgments every `backward_domain` answers for free, read off its own narrowing operators |
