# Sign domain — 7-element sign lattice

The concrete sign domain threaded through the four layers of the
`Instances/README.md` recipe: type-class instances, `abstract_domain` /
`sound_transfer` interpretations, executable bridge, and end-to-end effectful
soundness. Executable witnesses live under
`src/Formalization/Examples/Executable/Sign/`; they demonstrate the domain, they
are not part of the reusable instance.

| File | Role |
| --- | --- |
| `Sign_Domain.thy` | lattice + `abstract_domain` instantiation; `backward_domain_mono` interpretation (`afilter`/`bfilter` monotonicity) |
| `Sign_Exec.thy` | executable transfer mirror + `tf_st_commute` commutation |
| `Sign_Exec_Sound.thy` | the computed sign result and its certified soundness |
| `Sign_Side_Soundness.thy` | effectful transfer instance; `side_sign_analysis_sound` |
| `Value_Digest_Read.thy` | sign instance of the value-carried digest reader (`Value_Digest_Reader`) |
