# Sign domain — 7-element sign lattice

Session `Voblint_Analysis_Sign`, parented on `Voblint_Nonrelational`. The lattice
itself is `Voblint_Domain.Sign_Lattice`. The analysis is the kind-aware
non-relational pipeline of `src/Analyses/Nonrelational/` run at `sign`; `run_voblint`
activates it as `Sign`.

| File | Role |
| --- | --- |
| `Sign_Warrowing.thy` | widening (join), narrowing (left argument), and the `numeric_domain` instance |
| `Sign_Arithmetic.thy` | abstract arithmetic over signs |
| `Sign_Backward.thy` | inverse operators, with their soundness and monotonicity |
| `Sign_Kind.thy` | signs at a machine kind: the `ik_domain` and `kind_int_domain` instances. A sign carries no magnitude, so normalizing a nonzero sign to a kind answers the kind's top. |
