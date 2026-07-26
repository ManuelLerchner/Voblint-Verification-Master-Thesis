# D/G framework

The D/G framework separates flow-sensitive local facts (`D`) from information
published through global side effects (`G`). Analyses choose both carriers,
their transfer and communication operations, and an optional activation
context.

| File | Role |
| --- | --- |
| `DG_Framework.thy` | D/G specification, equation trees, and keyed generator |
| `DG_Soundness.thy` | Post-solution and collecting-semantics soundness |
| `DG_LTR_Sound.thy` | Local-trace collecting soundness |
| `DG_Context_Soundness.thy` | Context-indexed readers and keyed collecting soundness |
| `DG_Ctx_Activation.thy` | D/G discharge of activation-collecting obligations |

This is the supported modular-analysis interface. Homogeneous analyses use the
same carrier for `D` and `G`; mixed analyses use independent carriers.

Retain is intentionally absent. Its routing discipline differed from this
interface. Native D/G analyses cover the intended modular-analysis role without
claiming semantic equivalence to Retain.
