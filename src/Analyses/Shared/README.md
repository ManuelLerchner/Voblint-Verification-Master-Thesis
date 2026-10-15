# Analyses / Shared

Two sessions sit here, and neither is an analysis. They are what every
concrete domain would otherwise each rewrite: how a call site picks a context,
and what a solved system publishes. No lattice, no transfer function, no soundness theorem
about any particular abstraction.

`Shared/` is a directory, not a session. It exists to keep one fact visible in
the tree: these two sit *below* `Sign/`, `Interval/`, `Parity/`,
`Congruence/`, `Int/` and `Relational/` rather than beside them. A reader
scanning `src/Analyses/` should not have to open a ROOT to tell a domain from
the floor under it.

| Session | Directory | Holds |
| --- | --- | --- |
| `Voblint_Routing` | `Routing/` | compiled routed-equation construction, concrete context policies (call-string, entry-state), and key-space finiteness arguments |
| `Voblint_Result` | `Result/` | the domain-free bridge from a source run to a collecting-semantics bound (`Source_Activation_Sound`); what a solved routed system publishes (`DG_Result_Construction`) and the surface a caller reads it through (`Analysis_Surface`); `DG_Analysis` assembles one whole analysis --- at any context policy, the context-insensitive unit route included --- from a domain's choices, and `DG_Live_Unknowns` states its endpoints from termination alone |

## Vocabulary

| Term | Meaning |
| --- | --- |
| non-relational | a domain whose state is one abstract value per variable, independently --- a store of type `vname => 'a` |
| context policy | how a call site maps to a context: none, the entered abstract value, or a bounded call string |
| context space | the candidate contexts a context policy may choose. Its finiteness is separate from the solver's finite stabilized key set. |
| analysis surface | the published shape of a finished analysis --- the report a caller reads --- independent of which domain produced it |

## Worked example: how a domain uses these

Sign's numeric check queries
remain in `Sign_Numeric_Queries`;
`Routing/Compiled_Routed_Equations` assembles the common executable equation
system from the chosen keys, route, specification, graph, and initial state.
`Result/DG_Result_Construction` turns the solved system into a published table
and `Result/Analysis_Surface` is what every registration reads it back through,
at a given context.

Above those, `Result/DG_Analysis`'s `dg_analysis` is what the
CLI's combined registrations interpret at the routed policies: `mcp_cs_rule`
at the call-string routing pair and `mcp_es_rule` at the entry-state one
(`Voblint_CLI.MCP_Analyses`), each with Sign among the active analyses. That
locale owns the equation system, the solve, the covered keys, the reader, the
result table, the contextual report and the activation-indexed soundness
endpoints, so a policy costs an interpretation rather than a pipeline. The
context-insensitive route is the same locale at the unit route, local to a
domain: `sign_rule` is a `global_interpretation` of `dg_analysis_exec`
in Sign's own generated theory, `Sign_Analyses`. Every registration takes the global update rule as a
parameter, and the combined ones take the activation list besides. Sign
contributes the lattice and the transfer functions. Every other piece of those
sentences is from here.

## Why two sessions and not one

The groups own distinct responsibilities: routing over compiled programs and
publication of solved results. One import edge crosses them: `DG_Analysis`
imports `Compiled_Routed_Equations` and `Entry_State_Routed_Context` from
`Routing/`. Keeping those names explicit prevents shared code from becoming an
undifferentiated analysis base; CLI-only dispatch and `run_voblint` stay beside
their consumers in `Voblint_CLI`.

## Why they are chained

`Voblint_Routing` is parented on `Voblint_Exec`, and `Voblint_Result` on
`Voblint_Routing`, because `Result` needs `Routing`. The domain sessions are
parented on `Voblint_Result`, so they read both from one inherited heap instead
of re-elaborating them.

## Why none of this is in a core session

`Voblint_Framework` is `Voblint_CFG` plus `Domain` and `Solver`. It sees neither
the compiler nor the executable carrier. `Routing/` and `Analysis_Surface` need
`Voblint_Compile` because a context policy is about a *compiled* program;
`DG_Result_Construction` needs `Voblint_Exec`. None of them could move down.

## Reading order

`Routing/Compiled_Routed_Equations` first for the executable construction,
then `Entry_State_Routed_Context`. Then
`Result/DG_Result_Construction` for what a solve turns into,
`Result/Analysis_Surface` for how a caller reads that back, and
`Result/DG_Analysis` for the assembly that puts all of it together ---
its `dg_pipeline` is the construction with no correctness assumptions and
`dg_analysis` the same objects under the domain and solver contracts.

`Routing/Context_Space_Finite` is cited by nothing, deliberately. It bounds the
candidate space a call-string or monovariant key set is drawn from, before any
solve is attempted. Both halves of its containment are hypotheses, so it is not
a reachability result, and a bounded key space neither implies nor is implied by
the `solve_dom` contract the routed instances rely on. It is retained as a
result nothing has needed to cite yet; `docs/NEXT_STEPS.md` records what closing
that gap would take.
