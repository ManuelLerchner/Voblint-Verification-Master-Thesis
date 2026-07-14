# Examples / Digest

Read regressions and digest precision.
Digest examples partition a global by a per-point key so distinct writes stay
separated.

| File | Role | What |
| --- | --- | --- |
| `Example_Trace_Digest_Precision.thy` | regression | digest strictly tighter than flat collecting (`digest_beats_flat`) |
| `Example_Trace_Digest_Combine.thy` | regression | combine-side digest filtering at the return junction |
| `Example_Trace_Digest_ReachingCompat.thy` | regression | reader-side `reaching_compat` filters a global read |
| `Example_Entry_Store_Context_Precision.thy` | regression | entry-store context precision witness |
| `Example_Global_Ctx_Read_Precision.thy` | regression | `cmp`-filtered globals separate two call contexts |

Role vocabulary: repository `README.md` § Architecture. Per-file prose: `../README.md`.
