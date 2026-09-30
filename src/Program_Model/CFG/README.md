# CFG

This session defines procedure-aware control-flow graphs and gives them their
concrete interprocedural semantics. It is what a soundness claim is stated
*about*: nothing here mentions the compiler, so the D/G soundness endpoints
hold for an arbitrary CFG rather than only for compiled ones. The VIMP-to-CFG
compiler lives in `Voblint_Compile`.

## Graph model

| File | Role |
| --- | --- |
| `CFG_Def.thy` | CFG nodes, local edge actions, call relation, graph well-formedness |
| `CFG_Transfer.thy` | Concrete edge, call-entry, and caller/callee combination operations |
| `CFG_Prune.thy` | The structural successor relation and reachability over it |
| `CFG_Exec.thy` | `cstep`, small-step execution of an arbitrary CFG over a frame stack |

`intra` contains local edges. `calls` records a call site, call action, callee
entry, and continuation. `FunctionEntry p` and `FunctionResult p` are explicit
procedure boundaries.

`cfg_succ_rel` is the derived dependency graph the analysis runs on, not the
concrete execution relation: it adds the two combine edges (call site to
continuation, callee result to continuation) that execution never takes.

## Collecting semantics

| File | Role |
| --- | --- |
| `Collecting/Activation_Trace_Def.thy` | `activation_trace`, `valid_activation_trace`, caller and ancestor structure |
| `Collecting/Activation_Trace_Context.thy` | `key`, the context entry invariant, and `activation_collect` |
| `Collecting/Activation_Trace_Collect.thy` | `node_collect`, introduction rules, and least-fixpoint characterization |
| `Collecting/Activation_Trace_Abstract.thy` | The `activation_coverage` locale and its generic postfix soundness theorem |

Concrete CFGs and trace witnesses live in the `Voblint_Examples_CFG` session.
