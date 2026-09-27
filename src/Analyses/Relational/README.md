# Analyses / Relational

The analysis over the order lattice `relc` (`Voblint_Domain.Order_Lattice`), a
carrier that is *not* an `abs_state`: it relates variables to each other, so it
cannot be decomposed variable by variable.

| Theory | Role |
| --- | --- |
| `Rel_Order_Domain` | The transfers, with a precise assume refinement on bare-variable comparisons, run through the same equation generator, routed spine and vendored solver as every other domain. It proves that the generic pipeline never assumed pointwise states |
| `Rel_Order_Local` | The same analysis as a component of the combined state: it answers comparisons (`rel_qry`) and, at an assignment, asks how the new value compares with the other variables. The CLI runs it as `--analysis order` |

## Why this is a session and not an example

The point is a negative one — that no layer below needs the pointwise structure —
and a negative claim about layering is only convincing if the build enforces it.
`Voblint_Analysis_Relational` is parented on `Voblint_Exec` and lists no other
domain. That placement is the enforcement: the pointwise reuse locales live in
`Voblint_Nonrelational`, which is *not* an ancestor of this session, so an import
of one is not merely absent but unavailable. If the generic machinery below ever
grew a dependency on `abs_state`, this session would stop building.

## Vocabulary

| Term | Meaning |
| --- | --- |
| order carrier | any type with the order structure the generator needs, whether or not it factors through variables |
| `abs_state` | the pointwise construction every other domain uses: `vname => 'a`. Deliberately absent here. |

## Worked example

`Example_Relational_DG_Demo` (Examples/Relational) compiles
`if (x < y) { z = 1; } else { z = 0; }`, runs it through `compiled_routed_eqs_for`
at the unit route and the
vendored solver over this carrier, and compares the computed result against
Interval's on the identical program. It is an execution witness, not a
soundness-certified result: what it demonstrates is that the pipeline *accepts* the
carrier, which is the claim being made.
