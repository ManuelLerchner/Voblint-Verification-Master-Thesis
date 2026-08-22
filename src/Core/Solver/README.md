# TD solver bridge (side-effecting, interprocedural)

Connect the vendored **TD side** solver (`vendor/td-verification`, session `TD`, theory `TD_side`)
to the procedure-aware CFG and effectful equation format. Solver post-solutions
are connected to activation-local collecting semantics at nodes covered by the
query dependency cone.

The layer is split into four concerns, one subfolder each:

| Subfolder | Concern |
| --- | --- |
| `TD_Side/` | the TD-side solver interface: generator, monotonicity, base collecting soundness |
| `Strategy_Tree/` | the domain-agnostic strategy-tree monad and its combinators |
| `Context/` | context-sensitive solver spine: `Context/Activation`, `Context/DG` |
| `Exec/` | executable witnesses and DG-native example support |

**External:** Algorithm correctness is in `TD.TD_side` (`partial_correctness`, `TD_side_mono`).
This layer wires `part_post_solution` to `is_post_fixpoint` via
`src/Core/Equations/Constraint_System_Sound.thy`.

**Downstream:** `src/Analysis/Instances/Sign/Sign_Side_Soundness.thy` — `side_sign_analysis_sound`;
`src/Analysis/Instances/Interval/Interval_Side_Soundness.thy`; `src/Formalization/Pipeline/Mixed_Flow_Sound.thy`.

## `TD_Side/`

`TD_Side/README.md` has the file inventory: the TD-side solver interface built
directly on the strategy-tree monad.

## `Strategy_Tree/`

`Strategy_Tree/README.md` has the file inventory: the monad, its bind/do-notation
registration, and reading/side-publishing combinators. Domain-agnostic and
solver-agnostic — reused directly by `Context/DG/Context_Refinement.thy` and by
`Examples/Tooling/Example_Strategy_Tree_Demo.thy`.

## `Context/`

`Context/README.md` is the pointer; per-concern inventories in
`Context/Activation/README.md` and `Context/DG/README.md`.

## `Exec/`

`Exec_Bridge` (`'a st` fold mirror + `fun_of_st` simulation + the generic
`part_post_solution_st_to_abs_transport`) and `Solver_Side_RG` (reach-global
lemmas). The D/G product carrier is executable through `Exec_DG_Bridge`
(`fun_of_dg_st`, `dg_gen_of`, `part_post_solution_dg_st_to_abs`), which lets the
verified solver run on D/G equations; executable examples use it directly.

`Solver_Menu` bundles the vendored update-rule solvers (`join`, `per_origin`,
`warrow`) behind one `side_solver` signature. `run_menu eqs entry k var` reads
one slot under every discipline. A rule participates in a certified endpoint
only when its solver adapter yields the required partial post-solution theorem.
