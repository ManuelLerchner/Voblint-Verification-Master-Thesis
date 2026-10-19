# Congruence domain

Session `Voblint_Analysis_Congruence`, parented on `Voblint_Nonrelational`. The
lattice is `Voblint_Domain.Congruence_Lattice`. Congruence is a selectable analysis
(`Congruence` in `run_voblint`'s activation) and the second component of Int's
reduced product.

| File | Role |
| --- | --- |
| `Congruence_Warrowing.thy` | type-class widening and narrowing for the vendored solver |
| `Congruence_Arithmetic.thy` | arithmetic after the unbounded-integer fragment of Goblint's congruence domain, on the normalized carrier |
| `Congruence_Kind.thy` | congruences at a machine kind: normalization modulo the kind's width with Goblint's conversions, and the `ik_domain` and `kind_int_domain` instances |
| `Congruence_Regression.thy` | the Congruence analysis run on elaborated programs inside Isabelle, pinning published values |
