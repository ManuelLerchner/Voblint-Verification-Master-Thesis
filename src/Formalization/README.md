# Voblint_Formalization — end-to-end soundness session

Fourth session in the DAG (`Voblint_IMP2` -> `Voblint_CFG` -> `Voblint_Analysis`
-> `Voblint_Formalization`). Composes the layers below into the headline
soundness results. Holds theorems only — executable demonstrations and the
`Voblint` capstone live in the leaf session `Voblint_Examples` (`src/Examples/`),
so this session builds without the slow codegen/`value` runs.

| Entry | Role |
| --- | --- |
| `Pipeline/Mixed_Flow_Sound.thy` | mixed flow-sensitive soundness and optimality |
| `Pipeline/Compiler_Correctness.thy` | source-to-CFG compiler simulation lifting collecting soundness to IMP2 source runs |
| `Pipeline/Source_Activation_Sound.thy` | recursive source-adequacy bridge into `cfg_collect_ctx_act` |
