# Examples / Executable / Interval / SeededClean

Interval **seeded-clean (D/G/C R_read)** runs on the `twf`/`twfr` witness spine —
the executable layer feeding the recursive interval flagship.

| File | Role | What |
| --- | --- | --- |
| `Ivl_Twfr_Common.thy` | required support | reusable interval seeded-clean `twfr` plumbing (routing correspondence, combine-tree dependency set, `q_caller` / `q_callee`, combine bound; generic in graph + post-fixpoint) |
| `Exec_Ivl_Cmp_Seed_Sound.thy` | required support | interval instantiates the generic seeded-clean R_read spine (`apply_etf_ivl_etf_clean`) |
| `Exec_Ivl_Cmp_Seed_Clean_Run.thy` | required support | two-call program; `twfr` witnesses (`iseed_wit_{lo,hi}_sound`) |
| `Exec_Ivl_Cmp_Keyed_DG_Run.thy` | DG witness | DG-native keyed-slot separation over interval contexts |
| `Exec_Ivl_Cmp_Seed_Clean_Derived_Run.thy` | required support | derived global `GH := G + 1` kept context-separated; `dseed_wit_{lo,hi}_sound` |
| `Exec_Ivl_Cmp_Seed_Rehydrate_Run.thy` | required support | return rehydration on the R_read spine; readback crosses a combine (`rhyd_wit_readback_sound`) |
| `Exec_Ivl_Seed_EnterMono.thy` | required support | interval `ENTER_MONO`: the seeded-clean run instantiates point-digest routing |

Witness calculus: repository `README.md` § Architecture; `Activation_Witness_From.thy`.
Recursive flagship: `../../../Digest/Example_Rdiv_Twfr_Sound.thy`.
