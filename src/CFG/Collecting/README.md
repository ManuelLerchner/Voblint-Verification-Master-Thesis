# Activation-local collecting semantics

The CFG collecting layer uses call-structured local traces as its concrete
interprocedural semantics. The shape adapts the thread-modular local-trace
semantics of Schwarz and Erhard, *Data Race Detection by Digest-Driven
Abstract Interpretation* ([arXiv:2511.11055](https://arxiv.org/abs/2511.11055)),
itself built on Schwarz et al., *Improving Thread-Modular Abstract
Interpretation* (SAS 2021): a local trace is one procedure activation instead
of one thread.

| File | Role |
| --- | --- |
| `CFG_Local_Trace.thy` | `ltr`, `valid_ltr`, caller and ancestor structure |
| `Activation_Context.thy` | `key`, the context entry invariant, and `activation_collect` |
| `LTR_Collect.thy` | `ltr_collect`, introduction rules, and least-fixpoint characterization |
| `LTR_Abstract.thy` | The `ltr_coverage` locale and its generic postfix soundness theorem |

`valid_ltr` has root, call, and resume constructors. Each trace contains one
activation-local path and links called activations to their immediate caller.
Nested and recursive returns therefore resume structurally without encoding an
unbounded call stack in CFG nodes.

`ltr_collect` forgets activation structure and collects reachable sink stores
at each node. `activation_collect` retains an analysis-defined activation key.
These sets are the concrete targets of equation-system and D/G soundness.

Nothing here mentions the compiler: `valid_ltr` is the semantics of an
arbitrary CFG, which is what lets the analysis soundness statements be about
any graph rather than only about compiled ones.

Concrete witness graphs and executable regressions live in
`src/Examples/Regression/Example_LTR_Collect_Regression.thy`.
