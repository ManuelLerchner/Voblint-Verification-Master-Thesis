# Voblint_Soundness — the end-to-end soundness endpoints

Parented on `Voblint_Exec`, below the analysis family: `Voblint_Routing` is
parented on this session, so every domain inherits these endpoints from an
ancestor heap. It holds only the two theorems that close the chain. Everything
domain-specific -- each domain's routed instances at every context policy and
its `<Domain>_Entry` instantiation of these endpoints -- lives with its domain,
so this session says what is proved about the pipeline rather than how each
analysis reaches it.

Theorems only. Executable demonstrations and the `Voblint` capstone live in the
leaf `Voblint_Examples_*` sessions (`src/Examples/`), so this session builds
without the slow codegen and `value` runs.

The input to these is `Voblint_Framework`'s own question -- why a *solved
equation system* covers the collecting semantics of an arbitrary CFG -- which
is answered across `Framework/Constraints/` and `Framework/Context/`. This
session is the step after: why a *source program's* run is covered, end to end,
by a registered analysis.

| Entry | Role |
| --- | --- |
| `Run_Analysis_Sound.thy` | the registered analysis endpoints: `run_source_sound` and `collect_sound` from one executable D/G solve |
| `Source_Activation_Sound.thy` | source-adequacy bridge into activation-indexed collecting semantics |
