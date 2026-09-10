# Analyses / Shared

Three sessions sit here, and none of them is an analysis. They are what every
concrete domain would otherwise each rewrite: how a call site picks a context,
what a solved system publishes, and the derived operations a non-relational
domain gets for free. No lattice, no transfer function, no soundness theorem
about any particular abstraction.

`Shared/` is a directory, not a session. It exists to keep one fact visible in
the tree: these three sit *below* `Sign/`, `Interval/`, `Parity/`,
`Congruence/`, `Int/` and `Relational/` rather than beside them. A reader
scanning `src/Analyses/` should not have to open a ROOT to tell a domain from
the floor under it.

| Session | Directory | Holds |
| --- | --- | --- |
| `Voblint_Routing` | `Routing/` | compiled routed-equation construction, concrete routing policies (call-string, entry-state), and key-space finiteness arguments |
| `Voblint_Result` | `Result/` | what a solved routed system publishes (`DG_Result_Construction`) and the surface a caller reads it through (`Analysis_Surface`); `Routed_DG_Analysis` assembles one whole analysis --- at any context policy --- from a domain's choices, and `Unit_DG_Analysis` does the same for the context-insensitive case |
| `Voblint_Nonrelational` | `Nonrelational/` | what a non-relational domain reuses: expression evaluation and soundness, special-call dispatch, generic procedure entry, executable backward filtering |

## Vocabulary

| Term | Meaning |
| --- | --- |
| reuse locale | a locale a domain *interprets* to obtain a family of derived operations, rather than redefining them. `Abstract_Arithmetic`, `Special_Ops`, `Numeric_Ops`, `Exec_Backward` are these. |
| non-relational | a domain whose state is one abstract value per variable, independently --- a store of type `vname => 'a` |
| routing policy | how a call site maps to a context: none, the entered abstract value, or a bounded call string |
| context space | the candidate contexts a routing policy may choose. Its finiteness is separate from the solver's finite stabilized key set. |
| analysis surface | the published shape of a finished analysis --- the report a caller reads --- independent of which domain produced it |

## Worked example: how a domain uses these

Sign interprets `Nonrelational/Abstract_Arithmetic` at its own lattice and gets
the shared expression evaluator and soundness induction;
`Nonrelational/Numeric_Ops` packages that evaluator, backward filter, and top
value into generic executable procedure entry. Sign's numeric check queries
remain in `Sign_Numeric_Queries`;
`Routing/Compiled_Routed_Equations` assembles the common executable equation
system from the chosen keys, route, specification, graph, and initial state.
`Result/DG_Result_Construction` turns the solved system into a published table
and `Result/Analysis_Surface` is what `Sign_Checks` reads it back through.

Above those, `Result/Routed_DG_Analysis`'s `routed_dg_analysis` is what
`Sign_Analyses` actually interprets, twice: once at the call-string routing pair
and once at the entry-state one. That locale owns the equation system, the
solve, the covered keys, the reader, the result table, the contextual report and
the activation-indexed soundness endpoints, so a policy costs Sign an
interpretation and a list of published names rather than a pipeline. The
context-insensitive route is the same shape one layer over:
`Sign_Assembly` is one `global_interpretation` of `Result/Unit_DG_Analysis`'s
`unit_dg_analysis`, and `Sign_Checks` binds the names it defines. Sign
contributes the lattice and the transfer functions. Every other piece of those
sentences is from here.

## Why three sessions and not one

The groups own distinct responsibilities: routing over compiled programs,
publication of solved results, and pointwise non-relational reuse. They have no
theory-import edges between them. Keeping those names explicit prevents shared
code from becoming an undifferentiated analysis base; CLI-only dispatch and
graph export stay beside their consumers in `Voblint_CLI`.

## Why they are chained, even though they are independent

`Voblint_Routing <- Voblint_Result <- Voblint_Nonrelational` is an invented
order. Isabelle gives a session one parent and one inherited heap: theories from
an ancestor come from that heap, theories from a merely *listed* session are
re-elaborated in the importer. Three independent siblings that each domain lists
would re-elaborate two of the three in all five pointwise domain sessions ---
`Exec_Backward` alone is around 680 lines, five times over. Linearising is the
price of elaborating once.

Read the chain as increasing commitment rather than as a dependency: program
shape (`Routing`), then publication (`Result`), then store shape
(`Nonrelational`). It does not claim `Result` needs `Routing`.

## Why `Nonrelational` is last, and what that buys

`Voblint_Analysis_Relational` is parented on `Voblint_Exec`, branching off
*below* this whole chain. That is deliberate and it is the load-bearing part of
the layout.

All four theories in `Nonrelational/` fix a pointwise store --- `ev :: exp =>
(vname => 'a) => 'a` in the first two, `n_aval` in `Numeric_Ops`, an explicit
`gs :: vname => bool` classifier throughout `Exec_Backward`. `Rel_Order_Domain`
exists to show that nothing below the domain layer assumes that structure, and
it makes the claim by running an order carrier that is not an `abs_state`
through the same generator, spine and solver.

The boundary is enforced by the ROOT graph. `Rel_Order_Domain` imports only
`Voblint_Framework.DG_Spec_Sound`, `DG_Keyed_Generator` and `State_Restriction`
--- nothing from any of these three sessions --- so parenting it on
`Voblint_Exec` puts `Nonrelational/` out of reach.

Keep the scope honest. This is a *reachability* guarantee about one session, not
a proof that relational code is free of pointwise assumptions. A shared theory
elsewhere that quietly assumed a `vname => 'a` state would still slip through.
What makes it mean something is the criterion:

> A theory belongs in `Nonrelational/` exactly when it fixes a `vname => 'a`
> store.

One that does not --- `Analysis_Surface`, generic in `'a` with no store at all
--- belongs elsewhere, and lives in `Result/`.

## Why none of this is in a core session

Two different reasons, and only the first is a hard constraint.

`Voblint_Framework` is `Voblint_CFG` plus `Domain` and `Solver`. It sees neither
the compiler nor the executable carrier. `Routing/` and `Analysis_Surface` need
`Voblint_Compile` because a routing policy is about a *compiled* program;
`Numeric_Ops`, `Exec_Backward` and `DG_Result_Construction` need `Voblint_Exec`.
None of them could move down even if we wanted it.

`Abstract_Arithmetic` (needs only `Domain` and `VIMP`) and `Special_Ops` (only
`Framework`) could. They must not: putting a pointwise expression evaluator in
`Voblint_Framework` would make the framework assume one value per variable,
which is exactly the assumption `Rel_Order_Domain` is there to refute. Framework
stays true for an arbitrary carrier and an arbitrary CFG; this layer is where a
program becomes compiled and a store becomes pointwise, but not yet where a
value becomes a sign or an interval.

## Reading order

`Routing/Compiled_Routed_Equations` first for the executable construction,
then `Call_String_Routed_Context` for the policy the flagships use;
`Entry_State_Routed_Context` reads as a variation on it. Then
`Result/DG_Result_Construction` for what a solve turns into,
`Result/Analysis_Surface` for how a caller reads that back, and
`Result/Routed_DG_Analysis` for the assembly that puts all of it together ---
its `routed_dg_pipeline` is the construction with no correctness assumptions and
`routed_dg_analysis` the same objects under the domain and solver contracts.
`Nonrelational/` is
reference material a domain author reaches for rather than a narrative;
`Abstract_Arithmetic` is the one to read first if you are adding a domain.

`Routing/Context_Space_Finite` is cited by nothing, deliberately. It bounds the
candidate space a call-string or monovariant key set is drawn from, before any
solve is attempted. Both halves of its containment are hypotheses, so it is not
a reachability result, and a bounded key space neither implies nor is implied by
the `solve_dom` contract the routed instances rely on. It is retained as a
result nothing has needed to cite yet; `docs/NEXT_STEPS.md` records what closing
that gap would take.
