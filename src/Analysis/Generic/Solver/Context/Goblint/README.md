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

Global-read and digest-refinement infrastructure.

| File | Role |
| --- | --- |
| `Global_Cmp_Read.thy` | context-filtered global read |
| `Context_Domain.thy` | context domain and routing base |
| `Digest_Global_Read.thy` | digest-refined global read kernel |
| `TD_Side_Eff_Ctx_Sound.thy` | context-indexed pullback soundness |
| `Clean_RRead_Sound.thy` | clean read-side soundness |

### `Read/Support/`

Generic digest bridges and writer scaffolding.

| File | Role |
| --- | --- |
| `TD_Side_Eff_Cmp_Sound.thy` | cmp combine layer and soundness |
| `TD_Side_Eff_Cmp_Pull.thy` | cmp pullback discharge |
| `TD_Side_Eff_Cmp_Gen.thy` | keyed generator bridge |
| `Value_Digest_Reader.thy` | generic value-projected reader |
| `Digest_Keyed_Writer.thy` | keyed writer |
| `Digest_Keyed_Writer_Sound.thy` | keyed writer soundness |

## `Routing/`

Context-routing proof support for the seeded CMP generator (see `Routing/README.md`).
The call/routing contract is the heterogeneous DG spine in `DG/`; analyses interpret
`sound_dg_spec` directly.

### `Routing/Support/`

Proof support for routing bridges.

| File | Role |
| --- | --- |
| `Seed_EnterMono_Lift.thy` | point-digest `ENTER_MONO` lifting helper |
| `Seeded_Clean_Ctx_Collect.thy` | seeded-clean entry-side reduction |

#### `Routing/Support/Activation/`

Witness calculus for the seeded-clean routing story.

| File | Role |
| --- | --- |
| `Seeded_Activation_Sound.thy` | activation collecting soundness |
| `Seeded_Activation_Reach.thy` | activation reachability |
| `Activation_Witness_From.thy` | from-node-tracking witness calculus |

## `DG/`

D/G framework and retain analysis.

| File | Role |
| --- | --- |
| `DG_Framework.thy` | heterogeneous DG framework core |
| `DG_Soundness.thy` | heterogeneous DG soundness |
| `Retain_Analysis.thy` | retain analysis on the DG interface |
