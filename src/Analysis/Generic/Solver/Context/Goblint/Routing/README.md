# Routing

Context-routing proof support for the seeded CMP generator. The call/routing
contract itself is the heterogeneous DG spine (`DG/`); analyses interpret
`sound_dg_spec` directly, so no separate homogeneous call-spec wrapper lives here.

### `Routing/Support/`

Proof support for routing bridges.

| File | Role |
| --- | --- |
| `Seed_EnterMono_Lift.thy` | point-digest `ENTER_MONO` lifting helper |
| `Seeded_Clean_Ctx_Collect.thy` | seeded-clean entry-side reduction |
| `Activation/Activation_Witness_From.thy` | from-node-tracking witness calculus |
| `Activation/Seeded_Activation_Sound.thy` | activation collecting soundness |
| `Activation/Seeded_Activation_Reach.thy` | activation reachability |
