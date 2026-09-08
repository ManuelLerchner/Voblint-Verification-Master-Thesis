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
| `Voblint_Routing` | `Routing/` | the concrete routing policies over a compiled program (call-string, entry-state), plus the finiteness arguments their key spaces need |
| `Voblint_Result` | `Result/` | what a solved routed system publishes (`DG_Result_Construction`) and the surface a caller reads it through (`Analysis_Surface`) |
| `Voblint_Nonrelational` | `Nonrelational/` | what a non-relational domain reuses: derived arithmetic, special-call dispatch, executable numeric queries, executable backward filtering |

## Vocabulary

| Term | Meaning |
| --- | --- |
| reuse locale | a locale a domain *interprets* to obtain a family of derived operations, rather than redefining them. `Abstract_Arithmetic`, `Special_Ops`, `Numeric_Ops`, `Exec_Backward` are these. |
| non-relational | a domain whose state is one abstract value per variable, independently --- a store of type `vname => 'a` |
| routing policy | how a call site maps to a context: none, the entered abstract value, or a bounded call string |
| context space | the set a policy's contexts are drawn from. Finiteness of the solved key set is a property of this set, not of the solver. |
| analysis surface | the published shape of a finished analysis --- the report a caller reads --- independent of which domain produced it |

## Worked example: how a domain uses these

Sign interprets `Nonrelational/Abstract_Arithmetic` at its own lattice and gets
derived arithmetic without restating it; `Nonrelational/Numeric_Ops` gives it the
executable numeric queries its check discharge needs;
`Routing/Call_String_Routed_Context` supplies the routing policy `Sign_Analyses`
instantiates for its `k`-bounded run; `Result/DG_Result_Construction` turns the
solved system into a published table and `Result/Analysis_Surface` is what
`Sign_Checks` reads it back through. Sign contributes the lattice and the
transfer functions. Every other piece of that sentence is from here.

## Why three sessions and not one

There used to be one, `Voblint_Analysis_Base`, and its name gave the problem
away: it named a *position* in the session graph --- "the base of the analysis
family" --- rather than a content. Nothing else was available, because there
were three contents.

The three groups do not depend on each other. Across the nine theories there is
exactly one intra-group import (`Entry_State_Routed_Context` uses
`Call_String_Routed_Context`, both in `Routing/`) and zero edges between the
groups. They were one session because they share an *audience*, not because they
share anything else --- and a session defined by "everything not yet
domain-specific" accretes. The graph export layer is what proved that: it was
domain-independent, so it satisfied the description, and it sat here for a long
time although no domain ever imported it. It now lives in `Voblint_CLI`, next to
its actual consumers.

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

Under the old layout the session graph did not protect that claim.
`Voblint_Analysis_Base` was Relational's parent, so all four theories were
already available to `Rel_Order_Domain`; the only thing keeping them out was
that its import list happened to name three `Voblint_Framework` theories and
nothing else. An import added tomorrow would have built green and quietly
retired the claim. A Python lint stood in for the missing boundary.

Now the boundary is the ROOT graph. `Rel_Order_Domain` imports only
`Voblint_Framework.DG_Spec_Sound`, `DG_Keyed_Generator` and `State_Restriction`
--- nothing from any of these three sessions --- so parenting it on
`Voblint_Exec` costs it nothing and puts `Nonrelational/` permanently out of
reach. The lint was deleted rather than kept: the build now fails where it used
to warn.

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

`Routing/Call_String_Routed_Context` first --- it is the policy the flagships
use, and `Entry_State_Routed_Context` reads as a variation on it. Then
`Result/DG_Result_Construction` for what a solve turns into, and
`Result/Analysis_Surface` for how a caller reads that back. `Nonrelational/` is
reference material a domain author reaches for rather than a narrative;
`Abstract_Arithmetic` is the one to read first if you are adding a domain.

`Routing/Context_Space_Finite` is cited by nothing, deliberately. It bounds the
candidate space a call-string or monovariant key set is drawn from, before any
solve is attempted. Both halves of its containment are hypotheses, so it is not
a reachability result, and a bounded key space neither implies nor is implied by
the `solve_dom` contract the routed instances rely on. It is retained as a
result nothing has needed to cite yet; `docs/NEXT_STEPS.md` records what closing
that gap would take.
