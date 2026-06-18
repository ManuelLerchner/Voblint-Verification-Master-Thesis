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
| `pruns_to`                                     | Procedural big-step: `proc_table => com => store => store => bool`.                                                                                     | `IMP2_Proc.thy:141`   |
| `aval` / `bval`                                | Concrete arithmetic / boolean expression evaluation.                                                                                                    | `IMP2_Expr.thy`       |

## CFG layer

| Term                                    | Meaning                                                                                               | Source                                 |
| --------------------------------------- | ----------------------------------------------------------------------------------------------------- | -------------------------------------- |
| `pp`                                    | Program point, `= nat`.                                                                               | `CFG_Def.thy:26`                       |
| `cfg`                                   | A `(pp, edge_action) graph` record plus entry/exit and procedure wiring.                              | `CFG_Def.thy:67`                       |
| `edge_action`                           | Edge label: `EA_Nop`, `EA_Assign`, `EA_Assume`, `EA_AssumeNot`, `EA_Enter`.                           | `CFG_Def.thy:38`                       |
| `EA_Enter`                              | Call/scope entry: reset locals, keep globals.                                                         | `CFG_Def.thy`                          |
| `mk_cfg` / `mk_ip_cfg`                  | CFG constructors (intra / interprocedural).                                                           | `CFG_Def.thy:74,85`                    |
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
| `edges_collect`                       | Fold edge actions over a store set along a path.                                          | `CFG_Collect_Edges.thy:33`    |
| `cfg_collect_paths`                   | Intra collecting semantics (substrate; not the soundness target).                         | `CFG_Collect_Core.thy:8`      |
| `cfg_collect_ip`                      | Interprocedural collecting semantics — the soundness target at every point.               | `CFG_Collect_IP.thy:29`       |
| `cfg_collect_trace_ip`                | Trace-level IP collecting: covers partial and non-terminating behaviour, no final store.  | `CFG_Collect_Trace_IP.thy:63` |
| `pruns_to_ip`                         | Terminating IP runs correspond to exit reachability. Import `CFG_Collect_IP_Adeq` for it. | `CFG_Collect_IP_Adeq.thy:15`  |
| `collecting` locale / `collect` / `F` | The unified collecting locale and its fixpoint functional.                                | `CFG_Collect_Unified.thy:18`  |

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
| `rhs`                                      | Equation right-hand side: `pp => (pp => abs_state) => abs_state`. The solver interface. | `Constraint_System.thy:70`                        |
| `rhs_ip` / `combine_abs`                   | Interprocedural RHS and the call-combine of abstract states.                            | `Constraint_System.thy:401,404`                   |
| `is_post_fixpoint` / `is_post_fixpoint_ip` | Soundness target: a post-fixpoint over-approximates the collecting semantics.           | `Constraint_System.thy:102,424`                   |
| `TD` / `TD_side`                           | Vendored verified top-down solver; only the side-effecting variant is used.             | `vendor/td-verification`                          |
| `side_env` / `side_analyse_ip_eff`         | Side-solver environment and the effectful IP analysis entry point.                      | `TD_Side_CFG.thy`, `TD_Side_IP_Eff_Interface.thy` |
| `td_cfg_side_ip_solver_eff`                | Locale wrapping the effectful side solver for CFG/IP use.                               | `TD_Side_IP_Eff_Interface.thy`                    |
| `restrict_local` / `restrict_global`       | Split an abstract state into local / global parts across a call.                        | `TD_Side_CFG.thy:25,29`                           |

## Headline soundness theorems

| Theorem                                                      | Claim                                                          | Source                                                             |
| ------------------------------------------------------------ | -------------------------------------------------------------- | ------------------------------------------------------------------ |
| `post_fixpoint_sound_ip`                                     | A post-fixpoint soundly over-approximates `cfg_collect_ip`.    | `Constraint_System_IP_Sound.thy:208`                               |
| `side_collect_sound_ip_at_eff`                               | The effectful side solver's result is sound at every program point. | `TD_Side_IP_Eff_Pipeline.thy`                                 |
| `side_collect_sound_ip_exit_pruned_eff`                      | Soundness at the exit of the pruned CFG.                       | `TD_Side_IP_Eff_Soundness.thy`                                     |
| `side_ip_sign_analysis_sound` / `side_ip_ivl_analysis_sound` | End-to-end soundness instantiated at sign / interval.          | `Sign_Side_IP_Soundness.thy:9`, `Interval_Side_IP_Soundness.thy:9` |
| `trace_ip_analysis_sound`                                    | Trace-level soundness covering partial / non-terminating runs. | `Trace_IP_Analysis_Sound.thy:28`                                   |
| `unified_post_fixpoint_sound_ip`                             | The unified soundness engine over the collecting locale.       | `Analysis_Sound.thy:32`                                            |
