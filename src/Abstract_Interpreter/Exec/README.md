# Exec

The executable carrier, and the transport of a solved system from it back to
the carrier the framework is stated over. This session has no Goblint
counterpart, and that is the point of naming it: Goblint's `D.t` is already
executable, so it needs no second representation. Here the soundness theorems
of `Voblint_Framework` are stated over function-valued states `'k => 'a`, the
verified solver runs on the association-list quotient `('k, 'a) gdefault_st`,
and every theory in this session exists to connect the two. Read it as a
refinement layer, not as part of the framework.

| File | Role |
| --- | --- |
| `State/Default_St_Base.thy` | `('k, 'a) gdefault_st_rep`, one `gdefault_dict` (a default plus finite entries) per partition, and its quotient `('k, 'a) gdefault_st`; lookup at a local or global `'k glocation`, the pointwise order, executable equality and point update. Knows no global-name classifier |
| `State/Default_St_Algebra.thy` | Join, widening and narrowing through one pointwise combinator (`map2_default_dict`, applied to both dictionaries) over a deduplicated support, plus the lattice and warrowing instances |
| `State/Default_St_Transfer.thy` | Where the global-name classifier enters: `location_of`, `default_st_rep_to_fun` (the function a state represents), the call/return operations, the equations relating carrier operations to their `gabs_state` counterparts, and the carrier concretization `default_st_gamma` |
| `State/Default_St_Reachability.thy` | The readback of a lifted carrier state |
| `Refinement/Routed_Exec_Refinement.thy` | `pp_dg_spec_of` reconciles the buffered generator a component solves with the unbuffered one the framework is stated over |

Parent: `Voblint_Framework`. No theory here imports `Voblint_Compile`.

## Layout

```text
State/       the executable state: representation, algebra, classifier boundary,
             the represented function and the lifted readback
Refinement/  the routed post-solution
```

Dependencies run State -> Refinement.

## Reading order

The four `Default_St_*` theories form a chain, each adding exactly one concern:

```text
Default_St_Base          representation, quotient, order      (no variable names)
      |
Default_St_Algebra       join, widening, narrowing            (+ Abstract_Domain)
      |
Default_St_Transfer      classifier, function, call/return    (+ Transfer_Algebra)
      |
Default_St_Reachability  lifted readback                      (+ Nonrelational_Reachability)
```

The import of each layer names what that layer needs and nothing more, so the
chain is enforced by the build rather than only described here. A consumer
imports the layer it actually uses; there is deliberately no umbrella theory
re-exporting all four, since naming the layer says more than a catch-all would.
