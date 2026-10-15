# Interval domain

Session `Voblint_Analysis_Interval`, parented on `Voblint_Nonrelational`. The lattice
is `Voblint_Domain.Interval_Lattice`. Interval is a selectable analysis (`Interval`
in `run_voblint`'s activation) and the first component of Int's reduced product.

| File | Role |
| --- | --- |
| `Interval_Warrowing.thy` | widening and narrowing, and the numeric-domain instance |
| `Interval_Arithmetic.thy` | interval addition, subtraction, multiplication, division and remainder |
| `Interval_Numeric_Queries.thy` | the Interval interpretation of the generic numeric-query interface `sound_numeric_queries` |
| `Interval_Kind.thy` | intervals at a machine kind: the kind-indexed operations of Goblint's `IntervalFunctor`, kind-indexed widening and narrowing, and the `ik_domain` and `kind_int_domain` instances |
| `Interval_Regression.thy` | the Interval analysis run on elaborated programs inside Isabelle, pinning published values |
