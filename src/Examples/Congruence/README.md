# Examples / Congruence

The end-to-end D/G run of the standalone normalized Congruence domain. Its
arithmetic and backward filtering are pinned by `tests/regression/22-congruence/`.

| File | Role | What |
| --- | --- | --- |
| `Example_Congruence_DG_Run.thy` | D/G pipeline regression | VIMP compilation, equation generation, verified solving, live exit reachability, and exact Congruence facts |
| `Congruence_Regression.thy` | regression | build-checked assertions moved out of core: lattice operations on small values, rendering, and the check classifier on fixed states |
