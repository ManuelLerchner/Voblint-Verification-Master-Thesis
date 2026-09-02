# Framework

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
| `dg_spec` | the analysis: one manager-native transfer per edge action, `enter`, `combine_env`/`combine_assign`, `caller_cont` -- Goblint's `Spec` | `DG/DG_Spec.thy` |
| `sound_dg_spec` | a joint concretization `gammaDG d g` the compiled trees' observations over-approximate | `DG/DG_Spec_Sound.thy` |
| `dg_ctx_activation_base` | a solved system: `part_post_solution`, the covered keys, a reader; derives EDGE and COMB | `DG/DG_Ctx_Activation.thy` |
| `routed_context_base_hetero` | a routing policy `route`/`enterc`/`seed_key`/`resolve` at any carrier and concretization; fixes the call trees and derives CALL, COMB and activation-collect soundness | `DG/Routed_Context.thy` |
| `dg_analysis_adapter` | the published result table and check report, with their soundness | `Result/DG_Analysis_Adapter.thy` |

## Folders

| Folder | Question it answers | Theories |
| --- | --- | --- |
| `Equations/` | What must a per-edge transfer satisfy, and how does the solver see the graph? | `Transfer_Interface` (the non-relational Base transfer record, `apply_tf`, and `sound_transfer_for`), `CFG_Enumeration` (predecessors, call sites and returns as lists), and `State_Restriction` (local/global projections derived from the generic `combine_env` selector) |
| `DG/` | What is a sound analysis, and why does a post-solution cover `ltr_collect`? | `DG_Constraint_Trees` (the carrier-agnostic core: `dg_state`, `dg_edge_tree`/`dg_combine_tree`, the `dg_spec` record), `DG_Manager` (a single Goblint-`man`-shaped record -- `man_local` a value, `man_global`/`man_sideg` effectful capabilities closing over the current routed global key via `mk_dg_man`, plus `man_with_local` for running a second transfer stage from where the first reached; one manager type serves edge and combine transfers, with combine's callee-exit value an ordinary extra argument the way Goblint's `combine_env` takes the same `man` plus a `D.t`; `dg_edge_tree_man`/`dg_combine_tree_man` compile manager-mediated transfers through `Strategy_Tree_Program`, with compatibility theorems showing the old `step`/`comb` shapes reproduce `dg_edge_tree_at`'s/`dg_combine_tree_at`'s exact trees, and `mk_dg_man` the sole point interpreting those capabilities against the packed carrier -- a Base-style spec calls neither, so its equations carry no `QueryG` and no `Side`), `DG_Spec` (the manager-native analysis interface: every `dg_spec` field is a `man_transfer` returning the successor local value, global reads and publications are explicit `man_global`/`man_sideg` effects rather than a threaded `'dg` argument, combine is `combine_env` then `combine_assign` sequenced monadically via `man_with_local`, and `local_transfer` is the Base-style shape whose compiled tree provably has no `QueryG`, no `Side`, and dependency set exactly the source unknown), `DG_Spec_Sound` (the effect-native `sound_dg_spec` locale: assumptions stated against the compiled trees' own `traverse_rhs`/`sides_of_rhs` observations, never a reconstructed `'dg × 'dl` pair; `sound_local_dg_spec` is the Base collapse, whose `local_spec_sound` theorem discharges every global obligation vacuously and reduces each field to its plain pure-transfer inclusion -- downstream consumers not yet migrated), `DG_Ownership_Split_Spec` (the homogeneous `D = G` instantiation), `DG_Keyed_Generator` (the keyed equation generators and their buffered-generator correspondence -- spec-free: every equation is folded from supplied edge/combine/extra tree hooks, and the `TD_side_mono` discharge asks each hook only for traverse/sides monotonicity and `env_indep_deps`, never a dependency shape), `DG_Soundness` (the family-independent layer: fold bounds, `gamma_dg`, `vars_cover`, and the hook-parametric post-solution spine, all closure-shaped), `DG_LTR_Sound`, `DG_Ctx_Activation`, `Routed_Context` (the canonical routed seed publication and return combine: the spec's own compiled enter and composed combine run over the caller value, `entered` names the routing observation, and the only global effects left are the seed write and read -- `gk0` is never read-and-republished), `Routed_Context_Unit` (the context-insensitive instance), `DG_Local_State_Spec` (the whole-state Base-style spec as two `local_dg_spec` instances -- raw and reachability-lifted -- provably local-only, with soundness collapsing through `sound_local_dg_spec` plus three `transfer_lift` transport lemmas, no dead-code functor chain), `Activation_Local_Sound` and `Activation_Backbone` (from `ltr_coverage` to `activation_collect`) |
| `Context/` | What is a bounded call string, and what does a coarser bound see? | `Call_String_Context` (the data and its two projections), `Call_String_Collecting_Refinement` |
| `Result/` | What does a solved table publish, and how are checks discharged against it? | `Analysis_Result`, `Checks`, `Abstract_Checks`, `DG_Analysis_Adapter` |

The routing policies that need a compiled program (`Call_String_Routed_Context`,
`Entry_State_Routed_Context`, `Call_String_Context_Finite`) live in
`Voblint_Analysis`; the executable carrier and its transport live in
`Voblint_Exec`.
