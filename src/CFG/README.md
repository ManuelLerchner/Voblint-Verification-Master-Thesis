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
| `CFG_Prune.thy` | The structural successor relation, reachability, and the dependency cone |

`intra` contains local edges. `calls` records a call site, call action, callee
entry, and continuation. `FunctionEntry p` and `FunctionResult p` are explicit
procedure boundaries.

`cfg_succ_rel` is the derived dependency graph the analysis runs on, not the
concrete execution relation: it adds the two combine edges (call site to
continuation, callee result to continuation) that execution never takes.

## Collecting semantics

| File | Role |
| --- | --- |
| `Collecting/CFG_Local_Trace.thy` | `ltr`, `valid_ltr`, caller and ancestor structure |
| `Collecting/Activation_Context.thy` | `key`, the context entry invariant, and `activation_collect` |
| `Collecting/LTR_Collect.thy` | `ltr_collect`, introduction rules, and least-fixpoint characterization |
| `Collecting/LTR_Abstract.thy` | The `ltr_coverage` locale and its generic postfix soundness theorem |

Concrete CFGs and trace witnesses live in the `Voblint_Examples` session.
