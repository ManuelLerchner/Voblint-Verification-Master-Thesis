# Analyses / Base

`Voblint_Analysis_Base` is what every concrete domain starts from. It contains no
lattice, no transfer function and no soundness theorem about any particular
abstraction — only the things all of them would otherwise each rewrite.

It is the parent session of `Voblint_Analysis_Sign`, `_Interval`, `_Parity`,
`_Congruence`, `_Relational` and `_Int`. Nothing here may mention a concrete
domain; if a definition needs to know whether values are signs or intervals, it
belongs one level down.

## Vocabulary

| Term | Meaning |
| --- | --- |
| reuse locale | a locale a domain *interprets* to obtain a family of derived operations, rather than redefining them. `Abstract_Arithmetic`, `Special_Ops`, `Numeric_Ops`, `Exec_Backward` are these. |
| non-relational | a domain whose state is one abstract value per variable, independently — a store of type `vname => 'a`. The four reuse locales all fix such a store, which is why they sit in `Nonrelational/` and not in a core session. |
| analysis surface | the published shape of a finished analysis — the report a caller reads — independent of which domain produced it (`Analysis_Surface`) |
| routing policy | how a call site maps to a context: none, the entered abstract value, or a bounded call string |
| context space | the set a policy's contexts are drawn from. Finiteness of the solved key set is a property of this set, not of the solver. |

## Folders

| Folder | Holds |
| --- | --- |
| `Nonrelational/` | the locales a *non-relational* domain interprets: derived arithmetic, special-call dispatch, executable numeric queries, executable backward filtering |
| `Config/` | `analysis_domain`, `solver_choice`, `context_mode` and `resolve_analysis_config` — which (domain, solver, context) triples are legal, decided in one place |
| `Context/` | the concrete routing policies over a compiled program (call-string and entry-state), plus the finiteness arguments their key spaces need |
| `Reporting/` | generic GraphViz rendering of an analysis result, domain-independent |
| `Result/` | the output end: what a solved routed system publishes (`DG_Result_Construction`) and the surface a caller reads it through (`Analysis_Surface`) |

## Worked example: how a domain uses this session

Sign interprets `Nonrelational/Abstract_Arithmetic` at its own lattice and gets derived
arithmetic without restating it; `Nonrelational/Numeric_Ops` gives it the executable
numeric queries its check discharge needs; `Context/Call_String_Routed_Context`
supplies the routing policy `Sign_Analyses` instantiates for its `k`-bounded
run; `Config/Analysis_Config` is where `Sign_Analysis` appears as a selectable
value at all. Sign contributes the lattice and the transfer functions; every
other piece of that sentence is this session's.

## Why `Nonrelational/` is not in a core session

Every theory there would build in a core session tomorrow. `Abstract_Arithmetic`
needs only `Voblint_Domain` and `Voblint_VIMP`, and `Voblint_Domain` is already
parented on `Voblint_VIMP`; `Special_Ops` needs only `Voblint_Framework`;
`Numeric_Ops` and `Exec_Backward` need only `Voblint_Exec`. Moving them down
would add no session edge.

What argues against it is `Voblint_Analysis_Relational`. All four locales fix a
pointwise store — `ev :: exp => (vname => 'a) => 'a` in the first two, `n_aval`
in `Numeric_Ops`, an explicit `gs :: vname => bool` classifier throughout
`Exec_Backward`. `Rel_Order_Domain` exists to show that nothing below the domain
layer assumes that structure, and it makes the claim by importing none of these
while running through the same generator, spine and solver.

Be exact about what protects that, because the session graph does not.
`Voblint_Analysis_Base` is Relational's *parent*, so all four theories are
already available to `Rel_Order_Domain` today; the only thing keeping them out
is that its import list names `Voblint_Framework.DG_Spec_Sound`,
`DG_Keyed_Generator` and `State_Restriction` and nothing else. Moving them into
`Voblint_Domain` or `Voblint_Exec` would not change what is reachable — it would
change where a reader looks for them and what a future author is nudged toward,
which is reason enough, but it is a documentation argument, not an enforcement
one.

`scripts/check_relational_boundary.py` (`pixi run relational-boundary`, a
pre-commit job, and a CI step) enforces exactly one thing: no theory under
`src/Analyses/Relational/` may reach anything under `Base/Nonrelational/`,
directly or transitively. It fails on an unresolved project import rather than
skipping it, since a name it cannot resolve is a route it did not follow.

Read that scope narrowly. It is a *dependency* check against one directory, not
a proof that relational code is free of pointwise assumptions. A shared theory
elsewhere that quietly assumed a `vname => 'a` state would pass it. Keeping
`Nonrelational/` the one place such assumptions live is what makes the check
mean anything, and that part is still convention.

So the folder is a criterion, not a convenience: **a theory belongs in
`Nonrelational/` exactly when it fixes a `vname => 'a` store.** One that does
not — `Analysis_Surface`, generic in `'a` with no store at all — belongs
elsewhere, and lives in `Result/`.

## Why the finiteness theories are here and not in Framework

`Context_Space_Finite` and `Call_String_Context_Finite` are about a *compiled*
program, so they need `Voblint_Compile`, which the framework deliberately never
sees. They are domain-generic all the same, which is why they sit at the base of
the analysis layer rather than inside any one domain.
