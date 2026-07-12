# Interval domain (`ivl`)

The interval domain threaded through the four layers of the
`Instances/README.md` recipe. Executable witnesses live under
`src/Formalization/Examples/Executable/Interval/`.

| File | Role |
| --- | --- |
| `Interval_Bounds.thy` | extended integer bounds and bound operations |
| `Interval_Lattice.thy` | interval order, lattice, and bot/top structure |
| `Interval_Warrowing.thy` | widening/narrowing operators and laws |
| `Interval_Arithmetic.thy` | abstract arithmetic over intervals |
| `Interval_Backward.thy` | backward guard/filter operators |
| `Interval_Transfer.thy` | edge transfer record and transfer soundness |
| `Interval_Print.thy` | display support for examples and DOT output |
| `Interval_Domain.thy` | `abstract_domain` instantiation; `backward_domain_mono` interpretation |
| `Ivl_Exec.thy` | executable transfer mirror + commutation |
| `Interval_Side_Soundness.thy` | effectful transfer instance; end-to-end `side_ivl_analysis_sound` |
