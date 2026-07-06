# Sign executable witnesses and runs

Executable demonstrations of the sign analysis: each runs the vendored `TD_side`
solver via the code generator (`value` / `by eval`) or exhibits a sound keyed
post-solution by hand. They witness that the analysis executes and separates
contexts / modes; they are demonstrations, not part of the domain
definition (which lives one level up in `Instances/Sign/`).

- `Exec_Sign_Run` — codegen probe + two-point solver run.
- `Exec_Sign_Ctx_Run` / `Exec_Sign_Ctx_Seeded_Run` / `Exec_Sign_Ctx_Gen_Run` — context-sensitive runs.
- `Exec_Sign_Cmp_Keyed_{Run,Solve,Gen_Run,Retain_Run}` — cmp-filtered keyed-global witnesses/runs.
- `Exec_Sign_Mode_{Value,Compiled}_Run` — value-derived (mode) digest runs.
