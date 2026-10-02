# Examples / Sign

Sign-domain witnesses. Each `Example_*` defines its program locally; the
canonical spines additionally prove an end-to-end soundness theorem tying a
concrete run to the abstract result.

| File | Role | What |
| --- | --- | --- |
| `Exec_Sign_DG_Run.thy` | required support | end-to-end certified run on the Base-style D/G equation system, through Sign's unit-context registration at the always-join rule, with no example-local registration |
| `Example_Sign_DG_Overlapping_Enter.thy` | canonical spine + witness | one concrete call represented under two contexts at once: `dgs_enter` answers two overlapping (continuation, callee entry) alternatives, and both the solved table and the relational admitted-context relation keep them apart |
| `Sign_Regression.thy` | regression | build-checked assertions moved out of core: equality narrowing in `inv_eq_sign`, end-to-end `bfilter` narrowing, and the check classifier on fixed states |

`Exec_Sign_DG_Run.thy`'s `gEx` and `dgEx_eqs` are the `gs = sign_ex_gs`,
`p = sign_ex_prog` instance of the arbitrary-classifier, arbitrary-program chain
`Sign_Analyses` registers, not a separate parallel definition.

## Vocabulary

| word | meaning |
| --- | --- |
| **storage classifier** | the `gs :: vname => bool` saying which names are global. Every definition here is parametric in one; `sign_ex_gs`, `bf_prog_gs` and `ov_gs` are each *this* program's own classifier, not a fixed choice. |
| **ownership split** | the carrier that keeps a local half and a global half of the abstract state apart, joined back only where the transfer contract says so. `ownership_split_dg_spec_st_for` is the stock executable specification built over it. |
| **routed unit context** | context-insensitivity spelled as the degenerate routing policy: unknowns are keyed by `(node, ())`, so `compiled_routed_eqs_for` at `route_unit` is the same routed generator the call-string instances use, at the one-element context type. |
| **overlapping enter** | `dgs_enter` answering a *list* of (continuation, callee entry) alternatives whose entries and continuations both cover the same concrete call, so the route materializes two contexts for one call site. |
| **statement index** | `Statement n` numbering: source order, callee procedures before `main`, one index per command plus one epilogue index per procedure. |

## `CallString/` — context routed by call site

| File | Role | What |
| --- | --- | --- |
| `Example_Sign_DG_CallString_K1.thy` | canonical spine | the `nest` program at `k = 1`, solved by the plain-join solver: Sign is finite, so the computed solution is exact and `g`'s two activations collapse to `STop` |
| `Example_Sign_DG_CallString_K2.thy` | canonical spine | the same at `k = 2`, keeping them apart at `SPos` and `SNeg`. Exactness makes the strict-precision comparison (`sign_k2_strictly_more_precise_than_k1_at_g`) a statement about exact solutions |

Sign's verdicts on whole programs are pinned by the regression corpus under
`tests/regression/07-sign-precision/`.

Role vocabulary: repository `README.md`.
