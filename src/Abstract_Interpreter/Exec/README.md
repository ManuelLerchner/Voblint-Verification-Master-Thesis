# Exec

The executable carrier, and the transport of a solved system from it back to
the carrier the framework is stated over. This session has no Goblint
counterpart, and that is the point of naming it: Goblint's `D.t` is already
executable, so it needs no second representation. Here the soundness theorems
of `Voblint_Framework` are stated over function-valued states `vname => 'a`, the
verified solver runs on the association-list quotient `'a resolved_st_q`,
and every theory in this session exists to connect the two.

`docs/CORE_REFACTOR_PLAN.md` Phase 2 states the framework at the quotient
carrier directly (the design of HOL-IMP's `Abs_State`), after which the
transport theories are deleted and this session dissolves. Until then, read
it as a refinement layer, not as part of the framework.

| File | Role |
| --- | --- |
| `State/Exec_St_Base.thy` | `'a resolved_st` (local/global defaults plus location-keyed overrides) and its quotient `'a resolved_st_q`; lookup, the pointwise order, executable equality and point update. Knows no variable names |
| `State/Exec_St_Algebra.thy` | Join, widening and narrowing through one pointwise combinator (`map2_resolved_st`) over a deduplicated support, plus the lattice and warrowing instances |
| `State/Exec_St_Transfer.thy` | Where the global-name classifier enters: `location_of`, the readback `fun_of_resolved_st_for`, the call/return operations, and the equations relating carrier operations to their `abs_state` counterparts |
| `State/Exec_St_Reachability.thy` | The finite dead-code test, its exactness against `is_empty_state`, the quotient lift, and the lifted state that tracks emptiness incrementally |
| `State/Exec_St_Restriction_Refinement.thy` | `fun_of_resolved_st_q_for gs`: the readback into `'a abs_state`, and what commutes with it |
| `Spec/Exec_DG_State.thy` | The executable D/G carrier `exec_dg_st` and its classifier-parametric readback |
| `Spec/Ownership_Split_Exec.thy` | The ownership-splitting analysis at that carrier: the generic transfer at the executable merge/project triple |
| `Spec/DG_Local_State_Exec.thy` | The executable Base-style D/G construction: definitions and their selector equations |
| `Refinement/DG_Local_State_Exec_Refinement.thy` | `routed_dg_domain_exec`: soundness at the executable carrier, pulled back along the readback |
| `Refinement/Routed_Exec_Refinement.thy` | The routed layer, once for every domain and context policy: `pp_st` reconciles the buffered generator a domain solves with the unbuffered one the framework is stated over |
| `State/Exec_Result_Readback.thy` | `readback_result_value`: reading a solved local unknown back as an abstract state |

Depends on `Voblint_Framework` and, through `Result_Normalization`'s use of
`prog_cfg`, on `Voblint_Compile`.

## Layout

```text
State/       the executable state: representation, algebra, classifier boundary,
             dead-code test, and the two readbacks built directly on it
Spec/        analyses built at that carrier: the D/G pair, the ownership split,
             the Base local-state construction
Refinement/  what relates the carrier to the mathematical one: routed_dg_domain_exec
             and the routed post-solution
```

Dependencies run State -> Spec -> Refinement.

## Reading order

The four `Exec_St_*` theories form a chain, each adding exactly one concern:

```text
Exec_St_Base          representation, quotient, order      (no variable names)
      |
Exec_St_Algebra       join, widening, narrowing            (+ Abstract_Domain)
      |
Exec_St_Transfer      classifier, readback, call/return    (+ Transfer_Algebra)
      |
Exec_St_Reachability  dead-code detection                  (+ Nonrelational_Reachability)
```

The import of each layer names what that layer needs and nothing more, so the
chain is enforced by the build rather than only described here. A consumer
imports the layer it actually uses; there is deliberately no umbrella theory
re-exporting all four, since naming the layer says more than a catch-all would.
