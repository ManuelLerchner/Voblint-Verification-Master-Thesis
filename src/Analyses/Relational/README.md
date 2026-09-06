# Analyses / Relational

One theory, one job: prove that the generic pipeline never assumed its abstract
values were pointwise maps from variables to lattice elements.

Every other domain here is non-relational — a state is one abstract value per
variable, independently. `Rel_Order_Domain` supplies an order carrier that is *not*
an `abs_state`: it relates variables to each other, so it cannot be decomposed
variable by variable. It is then run through the same equation generator, the same
routed spine and the same vendored solver.

## Why this is a session and not an example

The point is a negative one — that no layer below needs the pointwise structure —
and a negative claim about layering is only convincing if the build enforces it.
`Voblint_Analysis_Relational` is parented on `Voblint_Analysis_Base` and lists no
other domain, so if the generic machinery ever grew a dependency on `abs_state`,
this session would stop building.

## Vocabulary

| Term | Meaning |
| --- | --- |
| order carrier | any type with the order structure the generator needs, whether or not it factors through variables |
| `abs_state` | the pointwise construction every other domain uses: `vname => 'a`. Deliberately absent here. |

## Worked example

`Example_Relational_DG_Demo` (Examples/Relational) compiles
`if (x < y) { z := 1 } else { z := 0 }`, runs it through `unit_routed_eqs` and the
vendored solver over this carrier, and compares the computed result against
Interval's on the identical program. It is an execution witness, not a
soundness-certified result: what it demonstrates is that the pipeline *accepts* the
carrier, which is the claim being made.
