# Core

The D/G analysis framework: what an analysis must supply, how its equations
are generated from a CFG, and why a solved system covers the collecting
semantics. The counterpart of Goblint's `Analyses.Spec`,
`Constraints.FromSpec`, `Control` and `AnalysisResult`. Domain-generic
throughout, and compiler-free: every endpoint is stated for an arbitrary
`Voblint_CFG` graph, and the session boundary is what keeps it that way.

Parents: `Voblint_CFG` (the graph and its collecting semantics),
`Voblint_Domain` (abstract states), `Voblint_Solver` (strategy trees).

## The spine

Six interfaces, each adding one thing to the one before it. Everything else
in the session derives from, transports, or instantiates one of them.

| Interface | Adds | Where |
| --- | --- | --- |
| `dg_spec` | the analysis: transfer per edge action, `enter`, `combine_env`/`combine_assign`, `caller_cont` -- Goblint's `Spec` | `DG/DG_Framework.thy` |
| `sound_dg_spec` | a joint concretization `gammaDG d g` each field over-approximates | `DG/DG_Soundness.thy` |
| `dg_ctx_activation_base` | a solved system: `part_post_solution`, the covered keys, a reader; derives EDGE and COMB | `DG/DG_Ctx_Activation.thy` |
| `routed_context_base_hetero` | a routing policy `route`/`enterc`/`seed_key`/`resolve` at any carrier and concretization; fixes the call trees and derives CALL, COMB and activation-collect soundness | `DG/Routed_Context.thy` |
| `dg_analysis_adapter` | the published result table and check report, with their soundness | `Result/DG_Analysis_Adapter.thy` |

## Folders

| Folder | Question it answers | Theories |
| --- | --- | --- |
| `Equations/` | What must a per-edge transfer satisfy, and how does the solver see the graph? | `Transfer_Interface` (the non-relational Base transfer record, `apply_tf`, and `sound_transfer_for`), `CFG_Enumeration` (predecessors, call sites and returns as lists), and `State_Restriction` (local/global projections derived from the generic `combine_env` selector) |
| `DG/` | What is a sound analysis, and why does a post-solution cover `ltr_collect`? | `DG_Framework` (the carrier-agnostic core: `dg_state`, `dg_edge_tree`/`dg_combine_tree`, the `dg_spec` record), `DG_Unit_Spec` (the homogeneous `D = G` instantiation), `DG_Keyed_Generator` (the keyed equation generators and their buffered-generator correspondence), `DG_Soundness`, `DG_LTR_Sound`, `DG_Ctx_Activation`, `DG_Transfer_Combinators`, `Routed_Context`, `Routed_Context_Unit` (the context-insensitive instance), `DG_Base` (the whole-state Base-style spec), `Activation_Local_Sound` and `Activation_Backbone` (from `ltr_coverage` to `activation_collect`) |
| `Context/` | What is a bounded call string, and what does a coarser bound see? | `Call_String_Context` (the data and its two projections), `Call_String_Collecting_Refinement`, `Call_String_Solver_Projection` |
| `Result/` | What does a solved table publish, and how are checks discharged against it? | `Analysis_Result`, `Checks`, `Abstract_Checks`, `DG_Analysis_Adapter` |

The routing policies that need a compiled program (`Call_String_Routed_Context`,
`Entry_State_Routed_Context`, `Call_String_Context_Finite`) live in
`Voblint_Analysis`; the executable carrier and its transport live in
`Voblint_Exec`.
