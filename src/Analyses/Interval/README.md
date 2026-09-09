# Interval domain (`ivl`)

The interval domain uses the shared routing, result, and non-relational
interfaces described in [`../Shared/README.md`](../Shared/README.md).
Executable witnesses live under
`src/Examples/Interval/`.

| File | Role |
| --- | --- |
| `Interval_Bounds.thy` | extended integer bounds and bound operations |
| `Interval_Lattice.thy` | interval order, lattice, concretization, and `sound_domain` instance |
| `Interval_Warrowing.thy` | widening/narrowing operators and laws |
| `Interval_Arithmetic.thy` | abstract arithmetic over intervals |
| `Interval_Backward.thy` | backward guard/filter operators; names the interval `afilter_ivl_st`/`bfilter_ivl_st` executable mirror via `Exec_Backward` |
| `Interval_Transfer.thy` | edge transfer record and transfer soundness |
| `Interval_Domain.thy` | aggregate import façade and small domain demonstrations |
| `Interval_Exec.thy` | executable transfer mirror + commutation |
| `Interval_Special.thy` | the abstract implementation of the `Min`/`Max` special calls |
| `Interval_Numeric_Queries.thy` | Interval's instance of `abstract_numeric_queries` |
| `Interval_Point_Digest.thy` | the point abstraction: a slot is a point when it is a singleton interval |
| `Interval_Sound.thy` | the `dg_spec` Interval supplies, its concretization, and `sound_dg_spec_core` — no context, no solver |
| `Interval_Exec_Sound.thy` | raw unbuffered computation for an arbitrary VIMP program; no production soundness |
| `Interval_Assembly.thy` | the context-insensitive route, as four interpretations of the shared `unit_dg_analysis` — one per update rule, with the lemmas proving all four solve the same system |
| `Interval_Analyses.thy` | the call-string and entry-state routed configurations, at the always-join solver |
| `Interval_Solver_Analyses.thy` | those two contextual configurations at the PerOrigin, Apinis-warrowing and warrowing-per-origin disciplines |
| `Interval_Classify.thy` | Interval instance of the generic check-discharge interface |
| `Interval_Checks.thy` | the public result tables and check reports, bound to the assembly's four instances |
| `Interval_Entry.thy` | the production endpoint: `analyse_interval_td_report` over an arbitrary `imp_prog`, and its soundness theorems — `run_source_sound`/`collect_sound` (`Voblint_Soundness`) applied at Interval |
