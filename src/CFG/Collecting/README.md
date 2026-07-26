# Activation-local collecting semantics

The CFG collecting layer uses call-structured local traces as its concrete
interprocedural semantics.

| File | Role |
| --- | --- |
| `CFG_Local_Trace.thy` | `ltr`, `valid_ltr`, caller structure, context keys, and `activation_collect` |
| `LTR_Collect.thy` | `ltr_collect`, `ltr_collect_keyed`, introduction rules, and least-fixpoint characterization |
| `LTR_Abstract.thy` | `ltr_gamma` and the generic abstract postfix soundness theorem |

`valid_ltr` has root, call, and resume constructors. Each trace contains one
activation-local path and links called activations to their immediate caller.
Nested and recursive returns therefore resume structurally without encoding an
unbounded call stack in CFG nodes.

`ltr_collect` forgets activation structure and collects reachable sink stores
at each node. `activation_collect` retains an analysis-defined activation key.
These sets are the concrete targets of equation-system and D/G soundness.

Concrete witness graphs and executable regressions live in
`src/Examples/Interprocedural/Example_LTR_Collect_Regression.thy`.
