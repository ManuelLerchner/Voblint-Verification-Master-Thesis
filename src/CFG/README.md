# CFG

This session defines procedure-aware control-flow graphs, compiles VIMP source
programs, and connects compiled executions to activation-local collecting
semantics.

## Core

| File | Role |
| --- | --- |
| `CFG_Def.thy` | CFG nodes, local edge actions, call relation, graph well-formedness |
| `CFG_Transfer.thy` | Concrete edge, call-entry, and caller/callee combination operations |
| `VIMP_Proc_to_CFG.thy` | Command, procedure, and whole-program compilation |
| `CFG_Prune.thy` | Reachability and graph pruning |

`intra` contains local edges. `calls` records a call site, call action, callee
entry, and continuation. `FunctionEntry p` and `FunctionResult p` are explicit
procedure boundaries.

## Compiler proofs

| File | Role |
| --- | --- |
| `Compiler/Compile_Certificate.thy` | Reusable facts extracted from one successful compiler run |
| `Compiler/Compile_Locality.thy` | Procedure ownership, node ranges, and separation |
| `Compiler/Compile_Invariants.thy` | Static compiler-input contract and generated-CFG invariants |
| `Compiler/Located_Exec.thy` | Source configurations located at CFG nodes |
| `Compiler/Control_Residual.thy` | Source residuals associated with compiled nodes |
| `Compiler/Control_Emit.thy` | Compiled edges of located residuals and the intra-step simulation |
| `Compiler/Control_Simulation.thy` | Forward simulation from source steps to located CFG execution |

## Collecting semantics

| File | Role |
| --- | --- |
| `Collecting/CFG_Local_Trace.thy` | `valid_ltr`, activation structure, contexts, and `activation_collect` |
| `Collecting/LTR_Collect.thy` | `ltr_collect`, keyed projection, and least-fixpoint characterization |
| `Collecting/LTR_Abstract.thy` | Abstract coverage interface for local-trace collecting semantics |

Core theories contain generic semantics and reusable lemmas. Concrete CFGs and
trace witnesses live in the `Voblint_Examples` session.
