# Examples / Executable / Sign / SeededClean

Sign **seeded-clean (D/G/C R_read)** runs, including the intentional unsoundness
counterexample that motivates the R_read boundary.

| File | Role | What |
| --- | --- | --- |
| `Exec_Sign_Cmp_RRead_Split.thy` | **regression / counterexample** | `clean_transfer_unsound` — proves the naive clean transfer is *not* sound (`¬ sound_effectful_transfer sign_etf_clean`); the guardrail that justifies the read split |
| `Exec_Sign_Cmp_Seed_Sound.thy` | required support | sign instantiates the generic seeded-clean R_read spine (`seeded_clean_seed_bound`) |
| `Exec_Sign_Cmp_Seed_Enter.thy` | required support | native DG seeded enter: seed the callee-entry local from the context; `twfr` witness `seed_wit_sound` |

Witness calculus: repository `README.md` § Architecture; `Activation_Witness_From.thy`.
