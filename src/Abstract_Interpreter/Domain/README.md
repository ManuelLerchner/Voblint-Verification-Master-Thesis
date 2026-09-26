# Domain

What an abstract value is, how reachability is lifted over a carrier, how
the non-relational analyses represent stores, and the integer value domains
query answers are expressed in. The counterpart of Goblint's
`goblint.domain` lattice constructors, framework reachability lift and
`cdomain/value/cdomains/int`, plus the concretizations and soundness
obligations required by Isabelle.

Depends on `Voblint_VIMP` (stores, expressions) and the vendored `TD`
session (the `widening`/`narrowing`/`warrowing` classes). Nothing here
mentions a graph, an equation, or a solver run.

## `Lattice/`

| File | Role |
| --- | --- |
| `Abstract_Domain.thy` | Executable and sound abstract-value classes, concretization bounds, widening, and the TD warrowing carrier constraint |
| `Reachability_Lift.thy` | Generic `Bot`/`Lifted` reachability carrier, lattice and solver-update instances, concretization, mapping, and normalized transfer combinators |
| `Three_Valued.thy` | The three-valued combinators `and_opt`/`or_opt` shared by expression evaluation and check classification |
| `Query_Lift.thy` | `'a query_lift`, Goblint's `Lattice.Lift`: a fresh bottom `QBot` and top `QTop` around a domain, the lattice query answers live in, with its meet and concretization |

## `State/`

| File | Role |
| --- | --- |
| `Nonrelational_State.thy` | Pointwise `'a abs_state = vname => 'a`, product concretization, and witness-bottom detection |
| `Nonrelational_Reachability.thy` | Composition of pointwise stores with the generic reachability lift: `gamma_state_lift` and `is_empty_state_lift` |

## `Eval/`

| File | Role |
| --- | --- |
| `Forward_Domain.thy` | Forward expression evaluation over a numeric domain: `sound_evaluator` and `sound_truth_test` |
| `Backward_Domain.thy` | `backward_ops`: the inverse operators on abstract values; `backward_domain`: their use on pointwise states, the derived `afilter`/`bfilter` guard refinement, the counterpart of Goblint's `BaseInvariant` |
| `Backward_Domain_Mono.thy` | `backward_domain_reductive` and `backward_domain_mono`: reductive and monotone inverse operators, and the filtering facts they buy |
| `Numeric_Queries.thy` | The `sound_numeric_queries` interface the check layer consumes, and `numeric_query_judgments`, which builds an instance from four yes/no judgments |
| `Backward_Numeric_Queries.thy` | The four judgments every `backward_ops` instance answers for free, read off its own inverse operators |

## `Int/`

| File | Role |
| --- | --- |
| `Interval_Lattice.thy` | Extended integer bounds `eint`, the interval lattice `ivl`, and the normalized intersection `intersect_ivl` |
| `Sign_Lattice.thy` | The sign lattice and its exact meet |
| `Parity_Lattice.thy` | The parity lattice and its exact meet |
| `Congruence_Lattice.thy` | Normalized residue classes `congruence`, their order, and the exact meet (the Chinese remainder intersection) |
| `Int_Lattice.thy` | The product `int_dom` of the four, with the reductions between components |
