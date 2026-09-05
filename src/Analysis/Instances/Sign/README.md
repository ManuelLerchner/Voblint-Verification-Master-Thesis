# Sign domain — 7-element sign lattice

The concrete sign domain threaded through the four layers of the
`Instances/README.md` recipe: type-class instances, `abstract_domain` /
`sound_transfer` interpretations, executable bridge, and end-to-end effectful
soundness. Executable witnesses live under
`src/Examples/Sign/`; they demonstrate the domain, they
are not part of the reusable instance.

| File | Role |
| --- | --- |
| `Sign_Lattice.thy` | 7-element sign lattice and order operations |
| `Sign_Arithmetic.thy` | abstract arithmetic over signs |
| `Sign_Backward.thy` | backward guard/filter operators; names the sign `afilter_sign_st`/`bfilter_sign_st` executable mirror via `Exec_Backward` |
| `Sign_Print.thy` | display support for examples and DOT output |
| `Sign_Transfer.thy` | edge transfer record and transfer soundness |
| `Sign_Domain.thy` | `abstract_domain` instantiation; `backward_domain_mono` interpretation (`afilter`/`bfilter` monotonicity) |
| `Sign_Exec.thy` | executable transfer mirror + `tf_st_commute` commutation |
| `Sign_Exec_Sound.thy` | the computed sign result and its certified soundness |
| `Sign_DG.thy` | `sound_dg_spec_core` interpretation (`ownership_split_dg_spec` diagonal); `sign_dg_post_solution_collect_sound` |
