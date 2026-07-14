# Examples / Executable / Sign / Keyed

Sign **keyed-global / combine-read** runs. The keyed generator has a proved
(exact-fixpoint conditional) soundness endpoint; the DG witness is the current
precision baseline, and the retain variant stays as the negative regression.

| File | Role | What |
| --- | --- | --- |
| `Exec_Sign_Cmp_Keyed_Gen_Run.thy` | required support | keyed-global generator; `kgen_retain_keyed_generator_sound_if_exact_fixpoint` |
| `Exec_Sign_Cmp_Keyed_DG_Run.thy` | current baseline | DG-spine keyed witness; keyed slots as a `dg_state` solution read through `sound_dg_spec.dg_gamma_c`; meaning provably equal to the keyed read shape; combine via the DG locale's `combine_sound` |
| `Exec_Sign_Cmp_Keyed_Retain_Run.thy` | comparative | retain-path generator run (conservative baseline) |
| `Exec_Sign_Cmp_Keyed_Retain_EnterMono.thy` | regression (negative) | why `ENTER_MONO` fails for value-keyed retain routing (`enter_mono_read_not_point`) |
| `Exec_Sign_Mode_Value_Run.thy` | precision comparison | value-carried mode digest; the solver is the source of truth |

Proved keyed/combine endpoint: `TD_Side_Eff_Cmp_Sound.post_fixpoint_sound_at_ctx_semantic_cmp_final`.
Role vocabulary: repository `README.md` § Architecture.
