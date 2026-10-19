# Parity domain

Session `Voblint_Analysis_Parity`, parented on `Voblint_Nonrelational`. The analysis
is the kind-aware non-relational pipeline of `src/Analyses/Nonrelational/` run at
`parity`; `run_voblint` activates it as `Parity`.

| File | Role |
| --- | --- |
| `Parity_Warrowing.thy` | widening (join), narrowing (left argument), and the domain instance |
| `Parity_Domain.thy` | parity arithmetic and comparison queries, with their soundness and monotonicity |
| `Parity_Kind.thy` | parity at a machine kind: the `ik_domain` and `kind_int_domain` instances. Normalizing to a kind changes a value by a multiple of `2 ^ w`, which is even. |
