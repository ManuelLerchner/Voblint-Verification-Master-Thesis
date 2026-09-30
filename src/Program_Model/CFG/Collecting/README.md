# Activation-trace collecting semantics

The CFG collecting layer uses call-structured activation traces as its concrete
interprocedural semantics. An activation trace is one procedure activation of a
sequential run. The shape is adapted from the local traces of Schwarz and
Erhard, *Data Race Detection by Digest-Driven Abstract Interpretation*
([arXiv:2511.11055](https://arxiv.org/abs/2511.11055)), built on Schwarz et
al., *Improving Thread-Modular Abstract Interpretation* (SAS 2021). Their local
traces belong to a multithreaded semantics in which operations of different
threads are only partially ordered, so this layer does not reuse the name.

| File | Role |
| --- | --- |
| `Activation_Trace_Def.thy` | `activation_trace`, `valid_activation_trace`, caller and ancestor structure |
| `Activation_Trace_Context.thy` | `key`, the context entry invariant, and `activation_collect` |
| `Activation_Trace_Collect.thy` | `node_collect`, introduction rules, and least-fixpoint characterization |
| `Activation_Trace_Abstract.thy` | The `activation_coverage` locale and its generic postfix soundness theorem |

`activation_trace` has root, call, and resume constructors. Each trace contains its own
activation path and links called activations to their immediate caller. Nested and recursive returns therefore resume structurally without encoding an
unbounded call stack in CFG nodes.

`node_collect` forgets activation structure and collects reachable sink stores
at each node. `activation_collect` retains an analysis-defined activation key.
These sets are the concrete targets of equation-system and D/G soundness.

Nothing here mentions the compiler: `valid_activation_trace` is the semantics of an
arbitrary CFG, which is what lets the analysis soundness statements be about
any graph rather than only about compiled ones.

Concrete witness graphs and executable regressions live in
`src/Examples/CFG/Example_Activation_Trace_Collect_Regression.thy`.
