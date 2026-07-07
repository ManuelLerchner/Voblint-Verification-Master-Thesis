# Interval domain (`ivl`)

The interval domain threaded through the four layers of the
`Instances/README.md` recipe. Executable witnesses live in `Runs/`.

| File | Role |
| --- | --- |
| `Interval_Domain.thy` | interval lattice + `abstract_domain` instantiation; `backward_domain_mono` interpretation |
| `Ivl_Exec.thy` | executable transfer mirror + commutation |
| `Interval_Side_Soundness.thy` | effectful transfer instance; end-to-end `side_ivl_analysis_sound` |
