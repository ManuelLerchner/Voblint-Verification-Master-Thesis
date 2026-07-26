# Equation systems

This layer turns a procedure-aware CFG and abstract transfer interface into an
equation system, then proves that every post-solution covers activation-local
collecting semantics.

| File | Role |
| --- | --- |
| `Constraint_System.thy` | Abstract transfers, `rhs_edge_sources`, `rhs_entry_sources`, `rhs_combine_sources`, their union `rhs_sources`, executable `rhs`, and post-fixpoints |
| `Constraint_System_Sound.thy` | Per-contribution soundness and mathematical RHS characterization |
| `LTR_Analysis_Sound.thy` | Post-fixpoint soundness against `ltr_collect` |
| `CFG_Enumeration.thy` | Executable finite enumeration of graph predecessors |

Each node equation joins three kinds of contribution:

1. an ordinary local predecessor transformed by its edge action;
2. a callee-entry state constructed from a call site;
3. a resumed caller state built from the caller and completed callee.

Executable equations and their soundness characterization share the same
contribution-family definitions. Solver layers consume those definitions
without introducing another concrete semantics.
