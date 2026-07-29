# Voblint_Formalization — end-to-end soundness session

Fourth session in the DAG (`Voblint_VIMP` -> `Voblint_CFG` -> `Voblint_Analysis`
-> `Voblint_Formalization`). Composes the layers below into the headline
soundness results. Holds theorems only — executable demonstrations and the
`Voblint` capstone live in the leaf session `Voblint_Examples` (`src/Examples/`),
so this session builds without the slow codegen/`value` runs.

| Entry | Role |
| --- | --- |
| `Pipeline/Mixed_Flow_Sound.thy` | mixed flow-sensitive soundness and optimality |
| `Pipeline/Compiler_Correctness.thy` | source-to-CFG compiler simulation lifting collecting soundness to VIMP source runs |
| `Pipeline/Source_Activation_Sound.thy` | source-adequacy bridge into activation-indexed collecting semantics |
