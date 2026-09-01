# Examples / Sign

Sign-domain witnesses. Each `Example_*` defines its program locally; the
canonical spines additionally prove an end-to-end soundness theorem tying a
concrete run to the abstract result.

| File | Role | What |
| --- | --- | --- |
| `Exec_Sign_DG_Run.thy` | required support | end-to-end certified run on the Base-style D/G equation system, registered through `base_dg_exec_analysis` as `sign_ex_reg` |
| `Example_Sign_Codegen_Exec_Consistency.thy` | regression | `Exec_Sign_DG_Run`'s `gEx`/`dgEx_eqs`/`dgEx_sol` really are the instance of `Sign_Codegen`'s arbitrary-program chain, not a parallel definition |
| `Example_Side_Execute.thy` | canonical spine | the smallest certified sign IP run, on `x := 1` (`x1_certified_sound`, `x1_explicit_completed_run_covered`) |
| `Example_Side_Proc_Global.thy` | canonical spine | sign IP on a global increment call (`inc_program`, see `../CFG/`); `inc_certified_sound` |
| `Example_Side_Branch_Calls.thy` | canonical spine | a branching procedure called twice; flow-sensitive locals against flow-insensitive globals |
| `Example_Checks_Store_Only.thy` | acceptance | `__voblint_check(...)` discharged node-locally against a computed post-solution: one proved, one refuted, one unknown |
| `Example_Random_Sign_Showcase.thy` | canonical spine | `x := __voblint_nondet_int()` closed end to end — the branches rejoin at `SNonNeg` rather than `STop`, with a source-level non-vacuity witness |
| `Example_Sign_DG_Custom_Combine.thy` | canonical spine | an analysis-supplied call-return environment merge that is *not* the stock one, carried through the same D/G generator and solver |
| `Example_Sign_DG_EntryState_Result_Regression.thy` | regression | `analyse_sign_entry_state_result` separates two call sites into `[SPos]` and `[SNeg]` contexts |

## `CallString/` — context routed by call site

| File | Role | What |
| --- | --- | --- |
| `Example_Sign_DG_CallString_K1.thy` | canonical spine | the `nest` program at `k = 1`, solved by the plain-join solver: Sign is finite, so the computed solution is exact and `g`'s two activations collapse to `STop` |
| `Example_Sign_DG_CallString_K2.thy` | canonical spine | the same at `k = 2`, keeping them apart at `SPos` and `SNeg`. Exactness makes a genuine strict-precision comparison possible here (`sign_k2_strictly_more_precise_than_k1_at_g`) that the Interval pair cannot state |

Role vocabulary: repository `README.md`.
