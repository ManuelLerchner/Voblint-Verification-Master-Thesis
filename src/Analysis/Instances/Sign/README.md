# Sign domain — 7-element sign lattice

The concrete sign domain threaded through the roles of the assembly map in
`Instances/README.md`. Executable witnesses live under `src/Examples/Sign/`;
they demonstrate the domain, they are not part of the reusable instance.

| File | Role |
| --- | --- |
| `Sign_Lattice.thy` | 7-element sign lattice and order operations |
| `Sign_Arithmetic.thy` | abstract arithmetic over signs |
| `Sign_Backward.thy` | backward guard/filter operators; names the sign `afilter_sign_st`/`bfilter_sign_st` executable mirror via `Exec_Backward` |
| `Sign_Special.thy` | `sign_min`/`sign_max`, the abstract implementation of the `Min`/`Max` special calls |
| `Sign_Numeric_Queries.thy` | Sign's instance of `abstract_numeric_queries` |
| `Sign_Transfer.thy` | edge transfer record and transfer soundness |
| `Sign_Domain.thy` | `abstract_domain` instantiation; `backward_domain_mono` interpretation (`afilter`/`bfilter` monotonicity) |
| `Sign_Exec.thy` | executable transfer mirror + `tf_st_commute` commutation |
| `Sign_Sound.thy` | the `dg_spec` Sign supplies, its concretization, and `sound_dg_spec_core` — no context, no solver |
| `Sign_Analyses.thy` | the same `unit_routed_eqs` system derived a second time, through the routed spine's generic locales |
| `Sign_Classify.thy` | Sign instance of the generic check-discharge interface |
| `Sign_Checks.thy` | result tables and check reports off one solved context-insensitive run |

Sign's production endpoint is `Voblint_CLI.Sign_Entry`: unlike Interval and
Int, Sign has no `_Exec_Sound` theory of its own, and the executable
whole-program API the CLI dispatches to is assembled there.
