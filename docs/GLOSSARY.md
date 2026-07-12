# Glossary

Project-specific terms, grounded in the `.thy` sources. Each entry names where
the term is defined so it can be checked against the code, not memory.

## Pipeline shape

`IMP AST -> CFG -> equation system -> TD solver -> sound abstract result -> mapped back`.
The analyzer rides only on the side-effecting solver (`TD.TD_side`); soundness is
stated against interprocedural CFG collecting semantics at every program point.

## Languages and stores

| Term                                           | Meaning                                                                                                                                                 | Source                |
| ---------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------- |
| `com`                                          | The procedural IMP language used throughout: `SKIP`, `Assign`, `Seq`, `If`, `While`, `Scope`, `Call`, `Restore`. Not the intra-only datatype (retired). | `IMP2_Proc.thy:20`    |
| `Scope`                                        | Local scope: save locals, restore on exit.                                                                                                              | `IMP2_Proc.thy`       |
| `Call`                                         | Call a parameterless procedure from the table.                                                                                                          | `IMP2_Proc.thy`       |
| `Restore`                                      | Runtime-only frame pop, restoring caller locals.                                                                                                        | `IMP2_Proc.thy`       |
| `proc_table`                                   | `pname => com option` — procedure names to bodies.                                                                                                      | `IMP2_Proc.thy:31`    |
| `frame`                                        | A caller's `store`, whose locals are restored on return.                                                                                                | `IMP2_Proc.thy:34`    |
| `store`                                        | `vname => int` — concrete program state.                                                                                                                | `IMP2_Syntax.thy:26`  |
| `pname`                                        | `string` — procedure name.                                                                                                                              | `IMP2_Globals.thy:17` |
| `is_global` / `combine_states` / `enter_state` | Global-variable handling: globals survive scope entry; locals are reset.                                                                                | `IMP2_Globals.thy`    |
| `pcompletes`                                     | Procedural completion: `proc_table => com => store => store => bool`; reaches `pfinal`. See `pcompletes_iff_small_termination`. | `IMP2_Proc.thy` |
| `aval` / `bval`                                | Concrete arithmetic / boolean expression evaluation.                                                                                                    | `IMP2_Expr.thy`       |

## CFG layer

| Term                                    | Meaning                                                                                               | Source                                 |
| --------------------------------------- | ----------------------------------------------------------------------------------------------------- | -------------------------------------- |
| `pp`                                    | Program point, `= nat`.                                                                               | `CFG_Def.thy:26`                       |
| `cfg`                                   | A `(pp, edge_action) graph` record plus entry/exit and procedure wiring.                              | `CFG_Def.thy:67`                       |
| `edge_action`                           | Edge label: `EA_Nop`, `EA_Assign`, `EA_Assume`, `EA_AssumeNot`, `EA_Enter`.                           | `CFG_Def.thy:38`                       |
| `EA_Enter`                              | Call/scope entry: reset locals, keep globals.                                                         | `CFG_Def.thy`                          |
| `mk_cfg` / `mk_cfg`                  | CFG constructors (intra / interprocedural).                                                           | `CFG_Def.thy:74,85`                    |
| `offset_edges k`                        | Shift sub-command edges to offset `k > 0` when compiling compound CFGs; invisible to `edges_collect`. | `CFG_Def.thy:99`                       |
| `predecessors` / `combine_predecessors` | Incoming edges / call-combine predecessors of a point.                                                | `CFG_Def.thy:117,130`                  |
| `compile_prog`                          | Compile a program + procedure table into a `cfg`.                                                     | `IMP2_Proc_to_CFG.thy`                 |
| `cfg_path`                              | Inductive predicate carrying actions along a path (needed for transfer-fn composition).               | `CFG_Path.thy:20`                      |
| `cfg_prune`                             | Prune the CFG (exit reachability).                                                                    | `CFG_Prune.thy`                        |
| `to_graphviz`                           | Emit DOT for a CFG (clusters per procedure region).                                                   | `CFG_GraphViz.thy:169`                 |

## Collecting semantics

| Term                                  | Meaning                                                                                   | Source                        |
| ------------------------------------- | ----------------------------------------------------------------------------------------- | ----------------------------- |
| `cenv`                                | Collecting environment: program point to reachable store set.                             | `CFG_Collect_*`               |
| `edges_collect`                       | Fold edge actions over a store set along a path.                                          | `CFG_Collect.thy`             |
| `cfg_collect_F`                       | One-step collecting functional over ordinary edges and combine triples.                    | `CFG_Collect.thy`             |
| `cfg_collect`                         | Interprocedural collecting semantics — the soundness target at every point.                | `CFG_Collect.thy`             |
| `cfg_collect_trace`                | Trace-level IP collecting: covers partial and non-terminating behaviour, no final store.  | `CFG_Collect_Trace.thy:63` |
| `cfg_runs_to`                         | Terminating IP runs correspond to exit reachability. Import `CFG_Collect_Runs` for it. | `CFG_Collect_Runs.thy`     |

## Abstract domains

| Term                              | Meaning                                                                              | Source                                             |
| --------------------------------- | ------------------------------------------------------------------------------------ | -------------------------------------------------- |
| `abs_state`                       | Abstract program state: `vname => 'a` (pointwise order).                             | `Constraint_System.thy`                            |
| `sound_domain` / `sound_transfer` | Semantic gamma-axioms a domain must satisfy; transfer-function soundness locale.     | `Abstract_Domain.thy`, `Constraint_System.thy:528` |
| `sign`                            | Sign domain (`STop` concretizes both positive and negative).                         | `Sign_Domain.thy`                                  |
| `ivl` / `eint`                    | Interval domain; extended integers `MinInf`/`Fin`/`PlusInf`.                         | `Interval_Domain.thy:21,50`                        |
| `gamma_ivl`                       | Concretization of an interval to an `int set`.                                       | `Interval_Domain.thy:93`                           |
| `widen` / `narrow`                | Widening / narrowing operators (termination of the fixpoint).                        | `Exec_St.thy:314,326`, `Interval_Domain.thy:195`   |
| `domain_transfer` / `apply_tf`    | Record of transfer functions per edge action; its application.                       | `Constraint_System.thy:36,44`                      |
| `st` / `st_rep`                   | Executable abstract-state representation (default + assoc list) for code generation. | `Exec_St.thy:31`                                   |

## Equation system and solver

| Term                                       | Meaning                                                                                 | Source                                            |
| ------------------------------------------ | --------------------------------------------------------------------------------------- | ------------------------------------------------- |
| `rhs` / `combine_abs`                      | Interprocedural RHS and the call-combine of abstract states.                            | `Constraint_System.thy`                           |
| `is_post_fixpoint`                         | Soundness target: a post-fixpoint over-approximates the collecting semantics.           | `Constraint_System.thy`                           |
| `TD` / `TD_side`                           | Vendored verified top-down solver; only the side-effecting variant is used.             | `vendor/td-verification`                          |
| `effectful_domain_transfer` / `apply_etf`  | Native transfer record for TD_side: strategy-tree producers for edges and combines.     | `Constraint_System.thy`                           |
| `side_env` / `side_analyse_eff`            | Side-solver environment and the effectful analysis entry point.                         | `TD_Side_CFG.thy`, `TD_Side_Eff_Interface.thy`    |
| `glob_env_cmp` / `side_env_cmp`            | Context-compatible global read: join only the global slots compatible with the current context. | `Global_Cmp_Read.thy`                    |
| `sound_effectful_transfer_framed`          | Strengthening of effectful transfer soundness with an enter upper bound by a fresh frame plus globals. | `Constraint_System.thy`, `Sign_Side_Soundness.thy` |
| `side_cfg_T_eff_cmp` / `_st`               | Abstract / executable keyed-global equation-system generator.                           | `TD_Side_Eff_Cmp_Gen.thy`, `Exec_Cmp_Bridge.thy` |
| `td_cfg_side_solver_eff`                   | Locale wrapping the effectful side solver for CFG use.                                  | `TD_Side_Eff_Interface.thy`                       |
| `restrict_local` / `restrict_global`       | Split an abstract state into local / global parts across a call.                        | `TD_Side_CFG.thy:25,29`                           |

## Headline soundness theorems

| Theorem                                                      | Claim                                                          | Source                                                             |
| ------------------------------------------------------------ | -------------------------------------------------------------- | ------------------------------------------------------------------ |
| `post_fixpoint_sound`                                     | A post-fixpoint soundly over-approximates `cfg_collect`.    | `Constraint_System_Sound.thy:208`                               |
| `side_collect_sound_at_eff`                                  | The effectful side solver's result is sound at every program point. | `TD_Side_Eff_Pipeline.thy`                                 |
| `side_collect_sound_exit_pruned_eff`                         | Soundness at the exit of the pruned CFG.                       | `TD_Side_Eff_Soundness.thy`                                     |
| `side_sign_analysis_sound` / `side_ivl_analysis_sound`       | End-to-end soundness instantiated at sign / interval.          | `Sign_Side_Soundness.thy`, `Interval_Side_Soundness.thy` |
| `trace_analysis_sound`                                    | Trace-level soundness covering partial / non-terminating runs. | `Trace_Analysis_Sound.thy:28`                                   |
| `mixed_flow_analysis_sound` / `mixed_flow_analysis_optimal` | Trace-level mixed-flow soundness and TD_side least-partial-post-solution optimality. | `Mixed_Flow_Sound.thy` |
