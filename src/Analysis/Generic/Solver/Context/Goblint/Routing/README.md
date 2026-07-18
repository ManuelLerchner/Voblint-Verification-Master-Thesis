# Routing

Context-routing proof support for the seeded keyed generator. The call/routing
contract itself is the heterogeneous DG spine (`DG/`); analyses interpret
`sound_dg_spec` directly, so no separate homogeneous call-spec wrapper lives here.

### `Routing/Support/Activation/`

Activation-indexed collecting soundness backbone.

| File | Role |
| --- | --- |
| `Activation_Backbone.thy` | generic `activation_collect_sound` over `valid_ltr` |
| `Activation_Local_Sound.thy` | local-trace activation soundness |
