# Exec

The executable carrier, and the transport of a solved system from it back to
the carrier the framework is stated over. This session has no Goblint
counterpart, and that is the point of naming it: Goblint's `D.t` is already
executable, so it needs no second representation. Here the soundness theorems
of `Voblint_Core` are stated over function-valued states `vname => 'a`, the
verified solver runs on the association-list quotient `'a resolved_st_q`,
and every theory in this session exists to connect the two.

`docs/CORE_REFACTOR_PLAN.md` Phase 2 states the framework at the quotient
carrier directly (the design of HOL-IMP's `Abs_State`), after which the
transport theories are deleted and this session dissolves. Until then, read
it as a refinement layer, not as part of the framework.

| File | Role |
| --- | --- |
| `Exec_St.thy` | `'a resolved_st` (local/global defaults plus location-keyed overrides) and its quotient `'a resolved_st_q`; lattice, widening and bottom detection on it |
| `Exec_Refinement.thy` | `fun_of_resolved_st_q_for gs`: the readback into `'a abs_state`, and what commutes with it |
| `Exec_DG_Refines.thy` | The D/G product on the executable carrier, its lattice instances, and the refinement relation to an abstract table |
| `Exec_DG_Trees.thy` | Executable per-edge, combine and enter trees; one tree's traversal commutes with the readback |
| `Exec_DG_Generator.thy` | The executable equation generator; one node's equation commutes with the readback (`dg_reader_commute_gen`) |
| `Exec_DG_Bridge.thy` | The transport theorem: a partial post-solution of the executable system is one of the abstract system |
| `DG_Base_Exec.thy` | The executable Base-style spec; `routed_dg_domain_exec`: the three commute facts a domain owes, and from them `sound_dg_spec_st` -- the executable spec is itself a `sound_dg_spec` under `gamma_exec`, the concretization read through the readback |
| `Routed_Domain_Exec.thy` | The routed layer, once for every domain and context policy: `pp_st` reconciles the buffered generator a domain solves with the unbuffered one the framework is stated over; `pp_abs` additionally transports the result to the abstract carrier |
| `DG_Coverage.thy` | `vars_cover` from graph reachability rather than from the solver's key set |
| `Solver_Side_RG.thy` | The side-effecting solver keeps every global slot globally restricted |
| `Solver_Menu.thy` | The three update rules (`join`, `per_origin`, `warrow`) behind one signature |
| `Monovariant_Analysis_Result.thy` | `normalize_point` (the readback into `point_state`) and the one constructor every monovariant `analysis_result` uses |

Depends on `Voblint_Core` and, through `Monovariant_Analysis_Result`'s use of
`prog_cfg`, on `Voblint_Compile`.
