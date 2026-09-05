# Framework

The D/G analysis framework: what an analysis must supply, how its equations
are generated from a CFG, and why a solved system covers the collecting
semantics. The counterpart of Goblint's `Analyses.Spec`,
`Constraints.FromSpec`, `Control` and `AnalysisResult`. Domain-generic
throughout, and compiler-free: every endpoint is stated for an arbitrary
`Voblint_CFG` graph, and the session boundary is what keeps it that way.

Parents: `Voblint_CFG` (the graph and its collecting semantics),
`Voblint_Domain` (abstract states), `Voblint_Solver` (strategy trees).

## Vocabulary

| Word | Means | Defined in |
| --- | --- | --- |
| `D` | the analysis's flow-sensitive fact, one per program point | opaque; carried in `dg_state`'s `locals` |
| `G` | the analysis's flow-insensitive shared fact | opaque; carried in `dg_state`'s `globs` |
| `dg_state` | the single solver value ordering `D` and `G` componentwise | `Spec/DG_State.thy` |
| manager | what a transfer is handed: the current `D`, plus capabilities to read and publish `G` without naming a solver key | `Spec/DG_Manager.thy` |
| transfer | manager to `strategy_program`; an edge transfer answers the successor `D` | `Spec/DG_Manager.thy` |
| alternative | one `(continuation, callee entry)` pair; a call answers a list of them | `Spec/DG_Manager.thy` |
| former | a transfer compiled to a solver right-hand side, addressed at one unknown | `Spec/DG_Spec.thy` |
| routed | keyed by `(program point, context)`, with callee activations seeded through a global slot | `Context/Routed_Context.thy` |
| whole-state | the Base-style shape where `D` is one `abs_state` and no global is touched | `Spec/DG_Local_State_Spec.thy` |

## One generator, six layers

Only the last of these builds an equation system. Several constructors before
it are named like generators and are not; the layer a name belongs to is what
says whether an analysis author may call it.

| Layer | What it produces | Examples |
| --- | --- | --- |
| transfer | a manager-native `strategy_program` -- what an analysis writes | `local_transfer`, an analysis's own `do`-block |
| program runner | reads the source unknowns, builds the manager, runs a transfer | `dg_edge_tree_man`, `dg_combine_tree_man` |
| tree compiler | compiles one manager program into one solver right-hand side | `transfer_tree`, `combine_transfer_tree`, `dg_spec_edge_tree` |
| protocol builder | the call lifecycle for one alternative, callee or call site | `routed_cmb_g_alt`, `routed_cmb_g_at`, `routed_cmb_g`, `routed_extra_g` |
| fold | joins several right-hand sides for one unknown | `side_rhs_fold_dg`, `fold_rhs_contributions` |
| generator | builds the equation system for a whole graph | `side_cfg_T_eff_keyed_seed_dg`, and its unit-context specialization `unit_routed_eqs` |

Three audiences follow from that table. An analysis writes `man_local`,
`man_global`, `man_sideg`, `sp_return`, the `local_*` adapters, and `dg_spec`
fields. The framework owns everything from the program runners through the
protocol builders. `QueryL`, `QueryG`, `Side`, `Answer` and `sp_compile` are
the solver's, and appear in a specification only by mistake.

## The spine

Five interfaces, each adding one thing to the one before it. Everything else
in the session derives from, transports, or instantiates one of them.

| Interface | Adds | Where |
| --- | --- | --- |
| `dg_spec` | the analysis: one manager-native transfer per edge action, `enter`, `combine_env`/`combine_assign` -- Goblint's `Spec` | `Spec/DG_Spec.thy` |
| `sound_dg_spec_core` | a joint concretization `gammaDG d g` the compiled trees' observations over-approximate | `Spec/DG_Spec_Sound.thy` |
| `dg_ctx_activation_base` | a solved system: `part_post_solution`, the covered keys, a reader; derives EDGE and COMB | `Activation/DG_Ctx_Activation.thy` |
| `routed_context_base_hetero` | a routing policy `route`/`enterc`/`seed_key`/`resolve` at any carrier and concretization; fixes the call trees and derives CALL, COMB and activation-collect soundness | `Context/Routed_Context.thy` |
| `dg_analysis_adapter` | the published result table and check report, with their soundness | `Result/DG_Analysis_Adapter.thy` |

Entry is deliberately absent from `sound_dg_spec_core`. A call answers a *list* of
alternatives, which is not an equation's answer, so what makes it sound is a
property of the tree the consuming generator builds from that list -- and the
monovariant and routed generators build different trees. Each states its own
entry obligation, both through the shared `entry_pairs_cover`.

## Folders

| Folder | Question it answers | Theories |
| --- | --- | --- |
| `Spec/` | What does an analysis supply, and when is it sound? | `DG_State` (the value a D/G unknown carries, and its lattice), `DG_Manager` (the Goblint-`man`-shaped record: `man_local` a value, `man_global`/`man_sideg` effectful capabilities that `mk_dg_man` closes the current routed global key into, with the projection rules that keep a built manager folded), `DG_Spec` (the record itself, the edge-action dispatch, the tree formers, and the local-only shapes whose compiled trees provably carry no `QueryG` and no `Side`), `DG_Spec_Sound` (`sound_dg_spec_core` stated against the compiled trees' own `traverse_rhs`/`sides_of_rhs` observations, never a reconstructed `'dg × 'dl` pair, plus `enter_runs`/`enter_deps`, which name what an entry program hands its continuation under a fixed solution), `DG_Local_State_Spec` (`sound_transfer_for`, and the two whole-state constructions built from it -- raw and reachability-lifted), `DG_Ownership_Split_Spec` (the `Spec2Spec` lifter that puts a whole-state analysis's global names on the shared channel) |
| `State/` | What algebra does a whole-state transfer compute in? | `Transfer_Algebra` (the `abs_state` operations a Base-style transfer is assembled from -- entry frame reset and formal binding, the structural return combine -- with their soundness and monotonicity against `gamma_state`), `State_Restriction` (the local/global projections derived from the generic `combine_env` selector) |
| `Constraints/` | What is a right-hand side, and how does the solver see the graph? | `CFG_Enumeration` (predecessors, call sites and returns as lists), `DG_Constraint_Trees` (edge formers over a solver address, and the fold that turns several right-hand sides for one unknown into one), `DG_Keyed_Generator` (the keyed equation generators and their buffered-generator correspondence -- spec-free: every equation is folded from supplied tree hooks, and the `TD_side_mono` discharge asks each hook only for traverse/sides monotonicity and `env_indep_deps`) |
| `Soundness/` | Why does a post-solution cover the collecting semantics? | `DG_Soundness` (the family-independent layer: fold bounds, `vars_cover`, and the hook-parametric post-solution spine, all closure-shaped), `DG_LTR_Sound` (the monovariant endpoint over `ltr_collect`), `Routed_Analysis_Sound` (a solved routed system composed with a context policy, once) |
| `Activation/` | What does one activation see? | `Activation_Local_Sound` and `Activation_Backbone` (from `ltr_coverage` to `activation_collect`), `DG_Ctx_Activation` (the D/G-native discharge of that backbone's obligations from a post-solution) |
| `Context/` | Which contexts exist, and what does a coarser one lose? | `Routed_Context` (the canonical routed seed publication and return combine), `Routed_Context_Unit` (the context-insensitive instance), `Call_String_Context` (the data and its two projections), `Call_String_Collecting_Refinement` |
| `Result/` | What does a solved table publish? | `Analysis_Result`, `DG_Analysis_Adapter` |
| `Checks/` | How is a `__goblint_assert` discharged against that table? | `Check_Result` (the flat three-valued verdict), `Checks`, `Abstract_Checks`, `Check_Report`, `Contextual_Check_Report` |

## Layering

```text
State/Transfer_Algebra   State/State_Restriction
        |                        |
        +----------+-------------+
                   v
Spec/DG_State -> Spec/DG_Manager -> Spec/DG_Spec -> Spec/DG_Spec_Sound
     |                                                    |
     v                                                    v
Constraints/DG_Constraint_Trees -> Constraints/DG_Keyed_Generator
     |                                                    |
     +--------------------> Soundness/DG_Soundness <------+
                                     |
              +----------------------+----------------------+
              v                                             v
     Soundness/DG_LTR_Sound                    Activation/DG_Ctx_Activation
                                                            |
                                                            v
                                                  Context/Routed_Context
                                                            |
                                                            v
                                                Result/DG_Analysis_Adapter
```

`DG_State` imports only the type classes its lattice instances need; every
other dependency in the session is stated where it is used. That is what keeps
`Constraints/` free of any domain and `Spec/` free of any CFG generator.

The routing policies that need a compiled program (`Call_String_Routed_Context`,
`Entry_State_Routed_Context`, `Call_String_Context_Finite`) live in
`Voblint_Analysis`; the executable carrier and its transport live in
`Voblint_Exec`.
