# Goblint

Goblint-facing formalizations and interfaces, split by concern.

This split follows the upstream Goblint `Spec` surface in
[`src/framework/analyses.ml`](https://github.com/goblint/analyzer/blob/master/src/framework/analyses.ml):
`Read/` models the `global` / `sideg` read side and its context/digest projections,
`Routing/` models `context`, `enter`, `combine_env`, and `combine_assign`, and `DG/`
models the `D/G/C/V` framework shape used by heterogeneous analyses. The `Support/`
subfolders hold proof scaffolding; they do not introduce separate Goblint-facing
interfaces.

## `Read/`

Keyed-global generator scaffolding. The relational digest/compatibility read
layer was retired (see `docs/DIGEST_SPINE_REMOVAL_PLAN.md`); analyses read their
own per-context slot directly on the DG spine.

### `Read/Support/`

| File | Role |
| --- | --- |
| `TD_Side_Eff_Ctx_Shared.thy` | shared context-pull helpers |
| `TD_Side_Eff_Keyed_Gen.thy` | functional keyed-global generator (routes global writes by context) |

## `Routing/`

Context-routing proof support for the seeded generator (see `Routing/README.md`).
The call/routing contract is the heterogeneous DG spine in `DG/`; analyses interpret
`sound_dg_spec` directly.

### `Routing/Support/Activation/`

Activation-indexed collecting soundness backbone.

| File | Role |
| --- | --- |
| `Activation_Backbone.thy` | generic `activation_collect_sound` over `valid_ltr` |
| `Activation_Local_Sound.thy` | local-trace activation soundness |

## `DG/`

D/G framework, context-sensitive soundness, and retain analysis.

| File | Role |
| --- | --- |
| `DG_Framework.thy` | heterogeneous DG framework core + seeded keyed generator |
| `DG_Soundness.thy` | heterogeneous DG soundness |
| `DG_Context_Soundness.thy` | per-context (keyed-slot) DG collecting soundness |
| `DG_Ctx_Activation.thy` | DG-native discharge of the activation obligations |
| `Retain_Analysis.thy` | retain analysis on the DG interface |
