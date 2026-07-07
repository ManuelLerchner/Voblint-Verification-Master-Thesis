# Interval executable witnesses and runs

Executable demonstrations of the interval analysis, running the vendored `TD_side`
solver via the code generator. Demonstrations, not part of the domain definition
(which lives one level up in `Instances/Interval/`).

- `Exec_Ivl_Run` — codegen probe + solver run; also the update-rule menu (`run_menu`)
  comparison (`loop_head_across_update_rules`).
- `Exec_Ivl_Ctx_Run` / `Exec_Ivl_Ctx_Gen_Run` — earlier context-sensitive runs (fixed
  contexts). Largely superseded by the interval **flagship**, kept as smaller witnesses.

The interval value-derived digest **flagship** moved to the Formalization session as
`Voblint_Formalization.Example_Interval_Mode_Digest`
(`src/Formalization/Examples/Digest/`), alongside the sign flagship
`Example_Sign_Mode_Digest`.
