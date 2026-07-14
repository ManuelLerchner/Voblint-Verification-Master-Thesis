# Examples / Executable / Interval / SeededClean

Interval seeded-clean is the last legacy executable cone.
The DG-native keyed interval witness is current; the `_st` seeded-clean files below remain historical/pending migration until the bridge is removed.

| File | Role | What |
| --- | --- | --- |
| `Ivl_Twfr_Common.thy` | deleted | reusable interval seeded-clean `twfr` plumbing (routing correspondence, combine-tree dependency set, `q_caller` / `q_callee`, combine bound; generic in graph + post-fixpoint) |
| `Exec_Ivl_Cmp_Seed_Sound.thy` | retained proof spine | interval instantiates the generic seeded-clean R_read spine (`apply_etf_ivl_etf_clean`) |
| `Exec_Ivl_Cmp_Shared.thy` | shared support | executable clean transfer, context selector, and R_read combine used by the seeded-clean cone |
| `Exec_Ivl_Cmp_Seed_Enter.thy` | current DG probe | native DG seeded-enter witness on the interval program |
| `Exec_Ivl_Cmp_Seed_Clean_Run.thy` | deleted | retired base run; replaced by the DG-native seeded-enter probe and shared support |
| `Exec_Ivl_Cmp_Keyed_DG_Run.thy` | current DG witness | DG-native keyed-slot separation over interval contexts |
| `Exec_Ivl_Cmp_Seed_Rehydrate_Run.thy` | deleted | return rehydration on the R_read spine; readback crosses a combine (`rhyd_wit_readback_sound`) |

The recursive interval flagships and the legacy `_st` executable path they
used have been retired.
