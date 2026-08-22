# Voblint_Formalization — end-to-end soundness session

Fourth session in the DAG (`Voblint_VIMP` -> `Voblint_CFG` -> `Voblint_Analysis`
-> `Voblint_Formalization`). Composes the layers below into the headline
soundness results. Holds theorems only — executable demonstrations and the
`Voblint` capstone live in the leaf session `Voblint_Examples` (`src/Examples/`),
so this session builds without the slow codegen/`value` runs.

| Entry | Role |
| --- | --- |
| `Pipeline/Run_Analysis_Sound.thy` | the registered analysis endpoints: `run_source_sound` and `collect_sound` from one executable D/G solve |
| `Pipeline/Source_Activation_Sound.thy` | source-adequacy bridge into activation-indexed collecting semantics |
| `Pipeline/*_Ctx_Sound.thy` | per-domain routed instances at the entry-state and call-string contexts |
