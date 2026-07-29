# Examples / Sign

Sign-domain witnesses: codegen probes and procedure-call soundness spines.
Each `Example_*` defines its program locally and proves an end-to-end
soundness theorem tying the concrete run to the abstract result.

| File | Role | What |
| --- | --- | --- |
| `Exec_Sign_Run.thy` | required support | codegen probe — does the executable sign `st` state evaluate through generated code? Underpins the sign executable examples |
| `Exec_Sign_DG_Run.thy` | required support | D/G-side codegen probe for sign |
| `Example_Side_Execute.thy` | canonical spine | minimal certified sign IP run on `x := 1` (`x1_certified_sound`) |
| `Example_Side_Proc_Global.thy` | canonical spine | sign IP on a global increment call (`Example_Inc_Proc`, see `../CFG/`); `inc_certified_sound` + executable + annotated DOT |
| `Example_Side_Branch_Calls.thy` | canonical spine | branching procedure called twice; flow-sensitive locals (`ec_certified_sound_store`) |
| `Example_Mixed_Flow_Sign.thy` | canonical spine | `mixed_flow_analysis_sound` / `_optimal` applied to sign |

Role vocabulary: repository `README.md`.
