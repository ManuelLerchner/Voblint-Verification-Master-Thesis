# Examples / Mixed

Non-`abs_state` domain instances that reuse the same generic D/G pipeline and
solver as Sign/Interval, run against the same CFG shape.

| File | Role | What |
| --- | --- | --- |
| `Example_Relational_DG_Demo.thy` | canonical spine + witness | `relc`, a relational (non-`abs_state`) order carrier (`Analysis/Instances/Mixed/Rel_Order_Domain.thy`), run end to end through `dg_gen_of` and the vendored solver on `if (x < y) { z := 1 } else { z := 0 }` with `x`/`y` unconstrained at entry — the case where Interval learns nothing from the guard but `relc` records the `(x,y)` pair directly |

Role vocabulary: repository `README.md`.
