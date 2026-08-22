# Examples / Relational

Order carriers that are not pointwise abstract states, run through the same
generic D/G pipeline and solver as every other domain. The point is that the
pipeline never assumed `abs_state`: a carrier whose elements are relations
between variables instantiates it unchanged.

| File | Role | What |
| --- | --- | --- |
| `Example_Relational_DG_Demo.thy` | canonical spine + witness | `relc`, a relational (non-`abs_state`) order carrier (`Analysis/Instances/Relational/Rel_Order_Domain.thy`), run end to end through `dg_gen_of` and the vendored solver on `if (x < y) { z := 1 } else { z := 0 }` with `x`/`y` unconstrained at entry — the case where Interval learns nothing from the guard but `relc` records the `(x,y)` pair directly |
