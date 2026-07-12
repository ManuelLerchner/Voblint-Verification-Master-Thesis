# Examples / Digest

Context-sensitivity, value/mode digests, and the **recursive interval flagship**
tower. Digest examples partition a global by a per-point key so distinct writes
stay separated; the recursion trio is the canonical `twfr` recursive story.

| File | Role | What |
| --- | --- | --- |
| `Example_Sign_Mode_Digest.thy` | **canonical spine** | Sign value-derived digest; `mode_collect_sound_witness` — a *separate proved spine* on `Trace_Analysis_Sound.context_collect_sound` |
| `Example_Interval_Mode_Digest.thy` | canonical spine | interval sibling with a while loop; proven-sound widening (`wide_abstracts`) |
| `Example_Interval_Recursion_Convergence.thy` | required support | **flagship 1/3**: seeded-clean solve on `rdiv` terminates; context-sensitive |
| `Example_Interval_Recursion_Rehydrate.thy` | required support | **flagship 2/3**: rehydrating combine returns the recursive global to `main` (`rdiv_rehyd_main_return_sound`) |
| `Example_Rdiv_Twfr_Sound.thy` | **canonical (recursive)** | **flagship 3/3**: executable soundness via a bottom-up `twfr` witness (`rdiv_witness_G_over_approximated`) |
| `Example_Interval_Recursion_Digest.thy` | design evidence | depth digest; the monovariant precision wall (`rec_warrowing_widens_to_top`) that motivates the witness spine — proves no soundness itself |
| `Example_Trace_Digest_Precision.thy` | regression | digest strictly tighter than flat collecting (`digest_beats_flat`) |
| `Example_Trace_Digest_Combine.thy` | regression | combine-side digest filtering at the return junction |
| `Example_Trace_Digest_ReachingCompat.thy` | regression | reader-side `reaching_compat` filters a global read |
| `Example_Entry_Store_Context_Precision.thy` | regression | entry-store context precision witness |
| `Example_Global_Ctx_Read_Precision.thy` | regression | `cmp`-filtered globals separate two call contexts |
| `Example_Finite_Sign_Context_Analysis.thy` | canonical spine | finite sign-derived contexts; `fctx_seed_clean_strictly_sharper` |
| `Example_Digest_Pipeline_Showcase.thy` | showcase | end-to-end: source → CFG → equations → solver → digest → GraphViz → soundness |
| `Example_Mode_Value_Digest_Showcase.thy` | showcase | guided reading of the value-carried digest run |

Role vocabulary: repository `README.md` § Architecture. Per-file prose: `../README.md`.
