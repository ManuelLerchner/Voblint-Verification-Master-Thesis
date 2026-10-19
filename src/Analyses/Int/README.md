# Int domain

Session `Voblint_Analysis_Int`, parented on `Voblint_Nonrelational` and listing the
Sign, Interval, Parity and Congruence sessions. It holds two products.

The value-level `int_dom` record (`Voblint_Domain.Int_Lattice`) is a reduced product
of Sign, Interval, Parity and Congruence. Its refinement exchange and how often to
run it (`refine_mode`: `Refine_Never`, `Refine_Once`, `Refine_Fixpoint`) are proved
here. `int_dom` is also the carrier of query answers between analyses.

The analysis `run_voblint` activates as `Ana_Int m` is `int_tuple`, the reduced
product of Interval and Congruence at machine kinds, after Goblint's `IntDomTuple`.
Its type parameter (`int_never`, `int_once`, `int_fixpoint`) selects the refinement
mode, so each mode is an analysis of its own.

| File | Role |
| --- | --- |
| `Int_Warrowing.thy` | componentwise widening and narrowing of `int_dom` |
| `Int_Refinement.thy` | the refinement exchange between `int_dom`'s components and its soundness |
| `Int_Refinement_Control.thy` | `refine_mode`, one refinement round, and the fixpoint loop; every mode is reductive and concretization-preserving, only the first two are monotone |
| `Int_Tuple_Kind.thy` | `int_tuple`, its lattice, refinement and `kind_int_domain` instance |
| `Int_Regression.thy` | the Interval-Congruence product run on elaborated programs inside Isabelle |
