# Examples / Parity

Parity-domain witness: the second-domain validation of the domain-registration API.

| File | Role | What |
| --- | --- | --- |
| `Example_Parity_DG_Flagship.thy` | canonical spine | parity analysis of an even-step loop, executed and certified on the D/G spine; registers through `ownership_split_dg_exec_analysis` (`parity_reg` in `DG_Domain_Registration`) with no copied `Hstep`/`Hcomb` proofs |

| `Example_Parity_Checks_Store_Only.thy` | acceptance | `__voblint_check(...)` discharged node-locally against a computed parity post-solution — one proved, one refuted, one unknown; the Parity member of the store-only check trio alongside Sign's and Interval's |

Role vocabulary: repository `README.md`.
