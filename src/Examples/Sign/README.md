# Examples / Sign

Sign-domain witnesses. Each `Example_*` defines its program locally; the
canonical spines additionally prove an end-to-end soundness theorem tying a
concrete run to the abstract result.

| File | Role | What |
| --- | --- | --- |
| `Exec_Sign_DG_Run.thy` | required support | end-to-end certified run on the Base-style D/G equation system, registered through `local_state_dg_exec_analysis` as `sign_ex_reg` |
| `Example_Sign_DG_Custom_Combine.thy` | canonical spine | an analysis-supplied call-return environment merge that is *not* the stock one, carried through the same D/G generator and solver |

## `CallString/` — context routed by call site

| File | Role | What |
| --- | --- | --- |
| `Example_Sign_DG_CallString_K1.thy` | canonical spine | the `nest` program at `k = 1`, solved by the plain-join solver: Sign is finite, so the computed solution is exact and `g`'s two activations collapse to `STop` |
| `Example_Sign_DG_CallString_K2.thy` | canonical spine | the same at `k = 2`, keeping them apart at `SPos` and `SNeg`. Exactness makes a genuine strict-precision comparison possible here (`sign_k2_strictly_more_precise_than_k1_at_g`) that the Interval pair cannot state |

Sign's two entry-point witnesses -- the smallest certified IP run and the
store-only check trio -- import `Voblint_CLI.Sign_Entry` and so live in `CLI/`,
which is where anything reaching the CLI layer goes.

Role vocabulary: repository `README.md`.
