# Voblint_Soundness — the end-to-end soundness endpoints

Sits directly above `Voblint_Analysis` and holds only the two theorems that
close the chain. Everything domain-specific -- including each domain's routed
instances at every context policy -- lives with its domain under
`src/Analysis/Instances/<Domain>/Ctx/`, so this session says what is proved
about the pipeline rather than how each analysis reaches it.

Theorems only. Executable demonstrations and the `Voblint` capstone live in the
leaf session `Voblint_Examples` (`src/Examples/`), so this session builds
without the slow codegen and `value` runs.

| Entry | Role |
| --- | --- |
| `Run_Analysis_Sound.thy` | the registered analysis endpoints: `run_source_sound` and `collect_sound` from one executable D/G solve |
| `Source_Activation_Sound.thy` | source-adequacy bridge into activation-indexed collecting semantics |
