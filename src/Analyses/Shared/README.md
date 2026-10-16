# Analyses / Shared

Two sessions sit here, and neither is an analysis. They are what every
concrete domain would otherwise each rewrite: how routed equations are built for a compiled program,
and what a solved system publishes. No lattice, no transfer function, no soundness theorem
about any particular abstraction.

`Shared/` is a directory, not a session. It exists to keep one fact visible in
the tree: these two sit *below* `Nonrelational/`, `Sign/`, `Interval/`, `Parity/`,
`Congruence/`, `Int/` and `Order/` rather than beside them. A reader
scanning `src/Analyses/` should not have to open a ROOT to tell a domain from
the floor under it.

| Session | Directory | Holds |
| --- | --- | --- |
| `Voblint_Routing` | `Routing/` | compiled routed-equation construction and key-space finiteness arguments for call-string and monovariant key sets |
| `Voblint_Result` | `Result/` | the domain-free bridge from a source run to a collecting-semantics bound (`Source_Activation_Sound`); what a solved routed system publishes (`DG_Result_Construction`) and the surface a caller reads it through (`Analysis_Surface`); `DG_Analysis` assembles one whole analysis --- at any context policy --- from a domain's choices, and `DG_Live_Unknowns` states its endpoints from termination alone |

## Vocabulary

| Term | Meaning |
| --- | --- |
| non-relational | a domain whose state is one abstract value per variable, independently --- in `Voblint_Nonrelational` a state of type `var_id ⇒ 'a kd` |
| context policy | how a call site maps to a context: a call string of bound `k` (`k = 0` is context-insensitive) or the entered abstract state |
| context space | the candidate contexts a context policy may choose. Its finiteness is separate from the solver's finite stabilized key set. |
| analysis surface | the published shape of a finished analysis --- the report a caller reads --- independent of which domain produced it |

## Worked example: how an analysis uses these

`Routing/Compiled_Routed_Equations` assembles the executable equation system from
the chosen keys, route, specification, graph and initial state.
`Result/DG_Result_Construction` turns the solved system into a published table, and
`Result/Analysis_Surface` is what every instance reads it back through, at a given
context.

Above those, `Result/DG_Analysis`'s locale `dg_analysis` owns the equation system,
the solve, the covered keys, the reader, the result table, the contextual report and
the activation-indexed soundness endpoints, so a context policy costs an
interpretation rather than a pipeline. `Voblint_Nonrelational` interprets it once per
policy for one domain (`nonrel`, `nonrel_es`); `Voblint_CLI` interprets it for the
combined state of the activated analyses (`mcp_cs`, `mcp_es`, and with
flow-insensitive program globals `mcp_split`, `mcp_split_es`). Every instance takes
the global update rule as a parameter. The analysis contributes its lattice and
transfer; every other piece is from here.

## Why two sessions and not one

The groups own distinct responsibilities: routing over compiled programs and
publication of solved results. One import edge crosses them: `DG_Analysis`
imports `Compiled_Routed_Equations` from `Routing/`. Keeping those names explicit prevents shared code from becoming an
undifferentiated analysis base; CLI-only dispatch and `run_voblint` stay beside
their consumers in `Voblint_CLI`.

## Why they are chained

`Voblint_Routing` is parented on `Voblint_Exec`, and `Voblint_Result` on
`Voblint_Routing`, because `Result` needs `Routing`. The domain sessions are
parented on `Voblint_Nonrelational`, itself parented on `Voblint_Result`, so they
read both from one inherited heap instead
of re-elaborating them.

## Why none of this is in a core session

`Voblint_Framework` is `Voblint_CFG` plus `Domain` and `Solver`. It sees neither
the compiler nor the executable carrier. `Routing/` and `Analysis_Surface` need
`Voblint_Compile` because a context policy is about a *compiled* program;
`DG_Result_Construction` needs `Voblint_Exec`. None of them could move down.

## Reading order

`Routing/Compiled_Routed_Equations` first for the executable construction. Then
`Result/DG_Result_Construction` for what a solve turns into,
`Result/Analysis_Surface` for how a caller reads that back, and
`Result/DG_Analysis` for the assembly that puts all of it together ---
its `dg_pipeline` is the construction with no correctness assumptions and
`dg_analysis` the same objects under the domain and solver contracts.
`Result/DG_Live_Unknowns` states the endpoints from termination alone.

`Routing/Context_Space_Finite` is cited by nothing, deliberately. It bounds the
candidate space a call-string or monovariant key set is drawn from, before any
solve is attempted. Both halves of its containment are hypotheses, so it is not
a reachability result, and a bounded key space neither implies nor is implied by
the `solve_dom` contract the routed instances rely on. It is retained as a
result nothing has needed to cite yet; `docs/NEXT_STEPS.md` records what closing
that gap would take.
