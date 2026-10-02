# Examples / Int

The Sign x Interval x Parity x Congruence product domain, run against the same
generic D/G pipeline, solver and CFG shape as the single-domain instances. What
these witness is the reduced product itself: which refinement mode recovers
what, and where componentwise widening and narrowing stop being enough.

| File | Role | What |
| --- | --- | --- |
| `Exec_Int_DG_Run.thy` | canonical spine + witness | A compiled `if (y + 1 == 3) { x := 1 } else { x := 0 }` run through the vendored TD solver on the composite domain. One projected `solve_c` result for each non-CLI mode shows that `Never` narrows only Congruence while `Once` reaches the exact singleton; the CLI regression covers its fixed `Fixpoint` mode |

Role vocabulary: repository `README.md`.
