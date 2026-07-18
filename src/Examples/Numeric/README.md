# Examples / Numeric

Interval / backward numeric analyses with certified trace soundness.

| File | Role | What |
| --- | --- | --- |
| `Example_Interval_Loop_Coverage.thy` | canonical spine | bounded loop; backward `assume_ivl` refines the body to `[0,19]`; certified trace soundness `[0,20]` at the loop head (`loop_head_x_bounded`) |
| `Example_Guard_Refinement.thy` | regression | backward guard refinement strictly tighter than identity assume (`backward_analysis_strictly_tighter`) — a precision negative result |
| `Example_IMP2_Coverage.thy` | canonical spine | non-terminating loop; sign coverage via trace soundness (`loop_head_x_pos`) |

Backward-analysis arc: `Example_Guard_Refinement` (one guard) → `Example_Interval_Loop_Coverage`
(full CFG + trace soundness). Role vocabulary: repository `README.md` § Architecture.
