# Examples / Executable / Interval / Core

Basic executable interval run through generated code.

| File | Role | What |
| --- | --- | --- |
| `Exec_Ivl_Run.thy` | precision comparison | bounded loop under every update rule (`join` / `per_origin` / `warrow`) at once; interval narrowing + backward guard filter recover `[0,20]`. `eval`-only — the proved trace-soundness counterpart is `Example_Interval_Loop_Coverage` (`../../../Numeric/`) |

Role vocabulary: repository `README.md` § Architecture.
