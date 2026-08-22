# TD solver bridge (side-effecting, interprocedural)

Connect the vendored **TD side** solver (`vendor/td-verification`, session `TD`, theory `TD_side`)
to the procedure-aware CFG and the D/G equation format. Solver post-solutions
are connected to activation-local collecting semantics through
`sound_dg_spec`.

The layer is split into three concerns, one subfolder each:

| Subfolder | Concern |
| --- | --- |
| `Strategy_Tree/` | the domain-agnostic strategy-tree monad, its combinators, and `threefold_mono` |
| `Context/` | context-sensitive solver spine: `Context/Activation`, `Context/DG` |
| `Exec/` | executable witnesses and DG-native example support |

**External:** Algorithm correctness is in `TD.TD_side` (`partial_correctness`, `TD_side_mono`).
This layer wires `part_post_solution` to `is_post_fixpoint` via
`src/Core/Equations/Constraint_System_Sound.thy`.

**Downstream:** each domain's routed instance (`Sign_Exec_Ctx_Sound`,
`Interval_Ctx_None_Routed_Sound`, `Parity_Exec_Ctx_Sound`, `Int_Exec_Ctx_Sound`)
and `src/Formalization/Pipeline/Run_Analysis_Sound.thy`.

## `Strategy_Tree/`

`Strategy_Tree/README.md` has the file inventory: the monad, its bind/do-notation
registration, and reading/side-publishing combinators. Domain-agnostic and
solver-agnostic — reused directly by `Context/DG/Context_Refinement.thy` and by
`Examples/Tooling/Example_Strategy_Tree_Demo.thy`.

## `Context/`

`Context/README.md` is the pointer; per-concern inventories in
`Context/Activation/README.md` and `Context/DG/README.md`.

## `Exec/`

`Solver_Side_RG` (reach-global lemmas). The D/G product carrier is executable
through `Exec_DG_Bridge`
(`fun_of_dg_st`, `dg_gen_of`, `part_post_solution_dg_st_to_abs`), which lets the
verified solver run on D/G equations; executable examples use it directly.

`Solver_Menu` bundles the vendored update-rule solvers (`join`, `per_origin`,
`warrow`) behind one `side_solver` signature. `run_menu rd eqs entry k` reads
one slot under every discipline, projecting it with the caller's `rd` so the
same menu serves any solver carrier. A rule participates in a certified endpoint
only when its solver adapter yields the required partial post-solution theorem.
