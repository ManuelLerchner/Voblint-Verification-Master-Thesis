# Interval domain (`ivl`)

The interval domain threaded through the roles of the assembly map in
[`../Base/README.md`](../Base/README.md). Executable witnesses live under
`src/Examples/Interval/`.

| File | Role |
| --- | --- |
| `Interval_Bounds.thy` | extended integer bounds and bound operations |
| `Interval_Lattice.thy` | interval order, lattice, and bot/top structure |
| `Interval_Warrowing.thy` | widening/narrowing operators and laws |
| `Interval_Arithmetic.thy` | abstract arithmetic over intervals |
| `Interval_Backward.thy` | backward guard/filter operators; names the interval `afilter_ivl_st`/`bfilter_ivl_st` executable mirror via `Exec_Backward` |
| `Interval_Transfer.thy` | edge transfer record and transfer soundness |
| `Interval_Domain.thy` | `abstract_domain` instantiation; `backward_domain_mono` interpretation |
| `Interval_Exec.thy` | executable transfer mirror + commutation |
| `Interval_Special.thy` | the abstract implementation of the `Min`/`Max` special calls |
| `Interval_Numeric_Queries.thy` | Interval's instance of `abstract_numeric_queries` |
| `Interval_Point_Digest.thy` | the point abstraction: a slot is a point when it is a singleton interval |
| `Interval_Sound.thy` | the `dg_spec` Interval supplies, its concretization, and `sound_dg_spec_core` — no context, no solver |
| `Interval_Exec_Sound.thy` | the production endpoint: an arbitrary VIMP program solved executably, with soundness |
| `Interval_Analyses.thy` | the same equation system derived a second time, through the routed spine's generic locales |
| `Interval_Solver_Analyses.thy` | the same equations again under the PerOrigin update rule instead of always-join |
| `Interval_Classify.thy` | Interval instance of the generic check-discharge interface |
| `Interval_Checks.thy` | result tables and check reports off one solved run |
