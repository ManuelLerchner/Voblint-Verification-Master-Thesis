# Glossary

The source theories are authoritative. File references identify the defining
layer without embedding line numbers that drift.

## Source language

| Term | Meaning | Source |
| --- | --- | --- |
| `com` | Procedural command language: structured commands, calls, explicit returns, and internal restoration commands. | `src/VIMP/VIMP_Proc.thy` |
| `proc_decl` | Procedure declaration containing formal parameters and a body. | `src/VIMP/VIMP_Proc.thy` |
| `proc_table` | Partial map from procedure names to declarations. | `src/VIMP/VIMP_Proc.thy` |
| `frame` | Saved caller store and optional return destination. | `src/VIMP/VIMP_Proc.thy` |
| `pstep` / `psteps` | Small-step execution over a command, store, and activation-frame stack. | `src/VIMP/VIMP_Proc.thy` |
| `pcompletes` | Terminating source execution with an empty frame stack. | `src/VIMP/VIMP_Proc.thy` |
| `source_com` | Syntactic source-command restriction excluding runtime-only commands. | `src/VIMP/VIMP_Proc.thy` |
| `wf_source_com` | Whole-program-aware command check for declared calls, arity, and reserved-variable exclusion. | `src/VIMP/VIMP_Proc.thy` |
| `value_providing` | Conservative syntactic predicate: no fall-through or void return and at least one value return. | `src/VIMP/VIMP_Proc.thy` |
| `wf_source_program` | Source contract for declarations, calls, returns, reserved variables, and a fall-through-only main. | `src/VIMP/VIMP_Proc.thy` |
| `ret_var` | Reserved internal channel carrying an explicit return value during unwinding. | `src/VIMP/VIMP_Proc.thy` |
| `enter_state` | Callee store with caller globals and fresh local variables. | `src/VIMP/VIMP_Globals.thy` |
| `combine_states` | Restored caller locals combined with callee globals. | `src/VIMP/VIMP_Globals.thy` |

## Procedure-aware CFG

| Term | Meaning | Source |
| --- | --- | --- |
| `cfg_node` | `Statement n`, `FunctionEntry p`, or `FunctionResult p`. | `src/CFG/CFG_Def.thy` |
| `edge_action` | Local CFG transfer, including assignments, assumptions, no-op flow, and matching procedure returns. | `src/CFG/CFG_Def.thy` |
| `intra` | Ordinary procedure-local CFG edges. | `src/CFG/CFG_Def.thy` |
| `calls` | Call-site relation containing the call action, callee entry, and continuation. | `src/CFG/CFG_Def.thy` |
| `wf_cfg` | Generic structural well-formedness conditions for a CFG. | `src/CFG/CFG_Def.thy` |
| `compile` | Compiles one source command into local edges and calls over a node interval. | `src/CFG/VIMP_Proc_to_CFG.thy` |
| `compile_proc` | Adds a procedure entry, result boundary, and fall-through return to a compiled body. | `src/CFG/VIMP_Proc_to_CFG.thy` |
| `compile_prog` | Compiles the procedure table and distinguished main command into one CFG. | `src/CFG/VIMP_Proc_to_CFG.thy` |
| `compile_cert` | Compiler certificate exposing generated layout and ownership facts. | `src/CFG/Compiler/Compile_Certificate.thy` |
| `wf_compile_input` | Canonical static contract for accepted source programs. | `src/CFG/Compiler/Compile_Invariants.thy` |

## Activation-local semantics

| Term | Meaning | Source |
| --- | --- | --- |
| `ltr` | Activation-local trace: root, called activation, or resumed caller. | `src/CFG/Collecting/CFG_Local_Trace.thy` |
| `valid_ltr` | Inductive concrete semantics over activation-local traces. | `src/CFG/Collecting/CFG_Local_Trace.thy` |
| `caller_of` | Immediate caller stored structurally in a called or resumed trace. | `src/CFG/Collecting/CFG_Local_Trace.thy` |
| `ltr_collect` | Reachable sink stores at each CFG node, forgetting trace structure. | `src/CFG/Collecting/LTR_Collect.thy` |
| `activation_collect` | Reachable sink stores indexed by activation context (the key-grouped view of `ltr_collect`). | `src/CFG/Collecting/CFG_Local_Trace.thy` |
| `ltr_gamma` | Concretization interface relating abstract states to local-trace collecting semantics. | `src/CFG/Collecting/LTR_Abstract.thy` |

## Abstract interpretation

| Term | Meaning | Source |
| --- | --- | --- |
| `abs_state` | Pointwise abstract variable environment. | `src/Analysis/Generic/Equations/Constraint_System.thy` |
| `sound_domain` | Abstract carrier, order, and concretization obligations. | `src/Analysis/Generic/Domain/Abstract_Domain.thy` |
| `domain_transfer` | Pure abstract transfers for CFG actions, entry, and return combination. | `src/Analysis/Generic/Equations/Constraint_System.thy` |
| `effectful_domain_transfer` | Strategy-tree-producing transfers used by the side-effecting solver. | `src/Analysis/Generic/Equations/Constraint_System.thy` |
| `rhs` | Equation right-hand side built from local-edge, entry, and return-combine contributions. | `src/Analysis/Generic/Equations/Constraint_System.thy` |
| `is_post_fixpoint` | Abstract environment closed under every equation contribution. | `src/Analysis/Generic/Equations/Constraint_System.thy` |
| `TD_side` | Vendored verified side-effecting top-down solver used by executable analyses. | `vendor/td-verification` |

## D/G framework

| Term | Meaning | Source |
| --- | --- | --- |
| `D` | Analysis-chosen flow-sensitive fact associated with a local unknown. | `src/Analysis/Generic/Solver/Context/DG/DG_Framework.thy` |
| `G` | Analysis-chosen shared fact routed through global side effects. | `src/Analysis/Generic/Solver/Context/DG/DG_Framework.thy` |
| `dg_spec` | D/G transfer, entry, combine, read, and publication interface. | `src/Analysis/Generic/Solver/Context/DG/DG_Framework.thy` |
| `sound_dg_spec` | Concrete-soundness obligations for a D/G instance. | `src/Analysis/Generic/Solver/Context/DG/DG_Framework.thy` |
| `dg_gen_of` | Executable D/G equation generator. | `src/Analysis/Generic/Solver/Exec/Exec_DG_Bridge.thy` |
| `dg_postfix` | Mathematical post-solution property for D/G equations. | `src/Analysis/Generic/Solver/Context/DG/DG_Soundness.thy` |

## Strategy-tree equation combinators

Named, zero-cost (`abbreviation`) readings of the verified solver's four
`strategy_tree` constructors (`QueryL`, `QueryG`, `Side`, `Answer`,
`vendor/td-verification/Basics_side.thy`). Full design and rationale in
`docs/DG_COMBINATOR_MIGRATION.md`.

| Term | Meaning | Source |
| --- | --- | --- |
| `read_local` | Read a local unknown, continue with its value. | `src/Analysis/Generic/Solver/Core/Strategy_Tree_Combinators.thy` |
| `read_global` | Read a global unknown, continue with its value. | `src/Analysis/Generic/Solver/Core/Strategy_Tree_Combinators.thy` |
| `depend_on` | Publish a side value under a global key, continue. | `src/Analysis/Generic/Solver/Core/Strategy_Tree_Combinators.thy` |
| `answer` | Yield the equation's local result. | `src/Analysis/Generic/Solver/Core/Strategy_Tree_Combinators.thy` |
| `enter_global` / `enter_local` | The global side effect / local answer half of `dgs_enter`. | `src/Analysis/Generic/Solver/Context/DG/DG_Transfer_Combinators.thy` |
| `combine_global` / `combine_local` | The global side effect / local answer half of `dgs_combine`. | `src/Analysis/Generic/Solver/Context/DG/DG_Transfer_Combinators.thy` |
| `publish_global` | `depend_on` to the one shared global slot, wrapping the payload as `DG bot x`. | `src/Analysis/Generic/Solver/Context/DG/DG_Transfer_Combinators.thy` |
| `publish_seed` | `depend_on` to a routed per-context seed slot -- same primitive as `publish_global`, named for the role. | `src/Analysis/Generic/Solver/Context/DG/DG_Transfer_Combinators.thy` |
| `return_local` | Yield the equation's own local contribution, wrapping it as `DG x bot`. | `src/Analysis/Generic/Solver/Context/DG/DG_Transfer_Combinators.thy` |
| `with_call` | Destructure a `call_action`'s single constructor once per call site instead of once per `dgs_enter`/`dgs_combine` call. | `src/Analysis/Generic/Solver/Context/DG/DG_Transfer_Combinators.thy` |

## Source-facing endpoints

| Term | Meaning | Source |
| --- | --- | --- |
| `source_activation_sound` | Compiler and activation-collecting bridge for accepted source executions. | `src/Formalization/Pipeline/Source_Activation_Sound.thy` |
| `dg_exec_run_source_sound` | Reusable bundle connecting a computed D/G solver result to source execution. | `src/Formalization/Pipeline/Run_Analysis_Sound.thy` |
| `mixed_flow_analysis_sound` | Mixed local/global analysis soundness. | `src/Formalization/Pipeline/Mixed_Flow_Sound.thy` |
