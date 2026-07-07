# Voblint_Formalization — end-to-end session

Top session in the DAG (`Voblint_IMP2` -> `Voblint_CFG` -> `Voblint_Analysis` ->
`Voblint_Formalization`). Assembles the layers below into the headline result and
its executable demonstrations.

| Entry | Role |
| --- | --- |
| `Voblint.thy` | narrative capstone tying the pieces together; cites the headline results (`mixed_flow_analysis_sound`, `mixed_flow_analysis_optimal`) via `@{thm}` |
| `Pipeline/` | end-to-end soundness composition (`Pipeline/README.md`) |
| `Examples/` | executable demos and witnesses (`Examples/README.md`) |
