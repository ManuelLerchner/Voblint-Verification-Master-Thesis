# Routing

Call and context-routing contract layers.

| File | Role |
| --- | --- |
| `Call_Spec.thy` | Goblint-inspired call/routing contract |
| `Call_Spec_Generator.thy` | generator wiring for the call spec |
| `Call_Spec_Sound.thy` | collecting soundness from the generated spec |

### `Routing/Support/`

Proof support for routing bridges.

| File | Role |
| --- | --- |
| `Seed_EnterMono_Lift.thy` | point-digest `ENTER_MONO` lifting helper |
| `Seeded_Clean_Ctx_Collect.thy` | seeded-clean entry-side reduction |
| `Activation/Activation_Witness_From.thy` | from-node-tracking witness calculus |
| `Activation/Seeded_Activation_Sound.thy` | activation collecting soundness |
| `Activation/Seeded_Activation_Reach.thy` | activation reachability |
