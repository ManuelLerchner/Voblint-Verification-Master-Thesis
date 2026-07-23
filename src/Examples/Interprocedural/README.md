# Examples / Interprocedural

Procedure-call soundness witnesses. Each defines its program locally and proves an
end-to-end soundness theorem tying the concrete run to the abstract result.

| File | Role | What |
| --- | --- | --- |
| `Example_Inc_Proc.thy` | required support | the shared global-increment procedure + its run-to-collecting witness lemmas |
| `Example_Side_Execute.thy` | canonical spine | minimal certified sign IP run on `x := 1` (`x1_certified_sound`) |
| `Example_Side_Proc_Global.thy` | canonical spine | sign IP on a global increment call; `inc_certified_sound` + executable + annotated DOT |
| `Example_Interval_Side_Proc_Global.thy` | canonical spine | interval IP on the same call (`proc_global_side_ivl_analysis`) |
| `Example_Proc_Call.thy` | canonical spine | two procedures (`inc` / `sqr`) via a global; `main_prog_interval_analysis` + CFG combine structure |
| `Example_Side_Branch_Calls.thy` | canonical spine | branching procedure called twice; flow-sensitive locals (`ec_certified_sound_store`) |
| `Example_Mixed_Flow_Sign.thy` | canonical spine | `mixed_flow_analysis_sound` / `_optimal` applied to sign |
| `Example_Proc_Recursion_CFG.thy` | regression | recursive procedure CFG layout regression (`proc_layout_regression_blocks`) |

Role vocabulary: repository `README.md` § Architecture.
