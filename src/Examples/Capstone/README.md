# Examples / Capstone

The final integration session, `Voblint_Examples`, parented on
`Voblint_Examples_CLI`.

| File | Role | What |
| --- | --- | --- |
| `Example_Non_Vacuity.thy` | non-vacuity and falsification | Satisfies the premises of `run_voblint_source_sound` and `run_voblint_check_sound` for a concrete program whose checks are `Check_Proved` (`nv_source_certified`, `nv_check_proved_sound`), shows a point with no reaching store for a program with a `Dead` check (`nv_dead_unreached`), and shows by counterexample that five conditions are load-bearing |

Non-vacuity is a property of the premises. It says nothing about whether `pstep`
models the intended language.

Role vocabulary: repository `README.md`.
