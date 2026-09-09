# Sign domain — 7-element sign lattice

The concrete sign domain uses the shared routing, result, and non-relational
interfaces described in [`../Shared/README.md`](../Shared/README.md).
Executable witnesses live under `src/Examples/Sign/`;
they demonstrate the domain, they are not part of the reusable instance.

| File | Role |
| --- | --- |
| `Sign_Lattice.thy` | 7-element sign lattice, order operations, concretization, and `sound_domain` instance |
| `Sign_Arithmetic.thy` | abstract arithmetic over signs |
| `Sign_Backward.thy` | backward guard/filter operators; names the sign `afilter_sign_st`/`bfilter_sign_st` executable mirror via `Exec_Backward` |
| `Sign_Special.thy` | `sign_min`/`sign_max`, the abstract implementation of the `Min`/`Max` special calls |
| `Sign_Numeric_Queries.thy` | Sign's instance of `abstract_numeric_queries` |
| `Sign_Transfer.thy` | edge transfer record and transfer soundness |
| `Sign_Exec.thy` | executable transfer mirror + `tf_st_commute` commutation |
| `Sign_Sound.thy` | the `dg_spec` Sign supplies, its concretization, and `sound_dg_spec_core` — no context, no solver |
| `Sign_Classify.thy` | Sign instance of the generic check-discharge interface |
| `Sign_Assembly.thy` | one `global_interpretation` of the shared `unit_dg_analysis`: Sign's transfer, entry state, always-join solver and classifier go in; the equation system, the solve, the reader, the result table, the report and every soundness endpoint come out |
| `Sign_Analyses.thy` | the call-string and entry-state routed configurations — the two the assembly does not cover, because each routes calls to more than one context |
| `Sign_Checks.thy` | the public runtime API: bindings onto the assembly, plus the per-origin solver sibling |
| `Sign_Entry.thy` | the production endpoint: `analyse_sign_report` over an arbitrary `imp_prog`, and its soundness theorems — `run_source_sound`/`collect_sound` (`Voblint_Soundness`) applied at Sign |

`Sign_Entry` is what `analyse` dispatches to, and it lives here rather than in
`Voblint_CLI` because nothing in it needs to see another domain: it depends on
Sign and on `Voblint_Soundness`, both of which this session already has. The
dispatcher restates its theorems over `analyse`; it does not prove them.
