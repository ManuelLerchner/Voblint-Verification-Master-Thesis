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
| `Exec_St.thy` | `'a resolved_st` (local/global defaults plus location-keyed overrides) and its quotient `'a resolved_st_q`; lattice, widening and bottom detection on it |
| `Exec_Refinement.thy` | `fun_of_resolved_st_q_for gs`: the readback into `'a abs_state`, and what commutes with it |
| `Exec_DG_Refines.thy` | The D/G product on the executable carrier, its classifier-parametric readback, the executable diagonal step/combine, and `merge_split_spec_exec`: four record-level commute facts pull a merge/split soundness argument back to the executable record |
| `Exec_DG_Generator.thy` | The executable equation generator; one node's equation commutes with the readback (`dg_reader_commute_gen`) |
| `DG_Local_State_Exec.thy` | The executable Base-style spec; `routed_dg_domain_exec`: the three commute facts a domain owes, and from them `sound_dg_spec_core_st` -- the executable spec is itself a `sound_dg_spec_core` under `gamma_exec`, the concretization read through the readback, with no separate transport theorem |
| `Routed_Domain_Exec.thy` | The routed layer, once for every domain and context policy: `pp_st` reconciles the buffered generator a domain solves with the unbuffered one the framework is stated over |
| `DG_Coverage.thy` | `vars_cover` from graph reachability rather than from the solver's key set |
| `Result_Normalization.thy` | `normalize_point` (the readback into `point_state`) and the one constructor every monovariant `analysis_result` uses |

Depends on `Voblint_Framework` and, through `Result_Normalization`'s use of
`prog_cfg`, on `Voblint_Compile`.
