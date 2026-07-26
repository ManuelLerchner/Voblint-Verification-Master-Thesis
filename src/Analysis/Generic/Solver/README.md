# TD solver bridge (side-effecting, interprocedural)

Connect the vendored **TD side** solver (`vendor/td-verification`, session `TD`, theory `TD_side`)
to the procedure-aware CFG and effectful equation format. Solver post-solutions
are connected to activation-local collecting semantics at nodes covered by the
query dependency cone.

The layer is split into three concerns, one subfolder each:

| Subfolder | Concern |
| --- | --- |
| `Core/` | the TD-side strategy-tree spine: monad, generator, monotonicity, base collecting soundness |
| `Context/` | context-sensitive solver spine: `Context/Activation`, `Context/DG`, `Context/Read` |
| `Exec/` | executable witnesses and DG-native example support |

**External:** Algorithm correctness is in `TD.TD_side` (`partial_correctness`, `TD_side_mono`).
This layer wires `part_post_solution` to `is_post_fixpoint` via
`src/Analysis/Generic/Equations/Constraint_System_Sound.thy`.

**Downstream:** `src/Analysis/Instances/Sign/Sign_Side_Soundness.thy` — `side_sign_analysis_sound`;
`src/Analysis/Instances/Interval/Interval_Side_Soundness.thy`; `src/Formalization/Pipeline/Mixed_Flow_Sound.thy`.

## `Core/`

| File | Role |
| --- | --- |
| `Strategy_Tree_Monad.thy` | `seqcomp_tree` (bind), `traverse_seqcomp`, `dep_aux_seqcomp`, `sides_of_rhs_seqcomp`; `static_deps`, `seqcomp_mono` |
| `TD_Side_CFG.thy` | `restrict_local`, `restrict_global`, `side_env`; unit-global tree constructors; `trans_dep\<^sub>L` step/trans lemmas |
| `TD_Side_Tree.thy` | `side_cfg_T_eff` effectful IP strategy trees; folds `side_acc_eff` |
| `TD_Side_Eff_Bounds.thy` | monotonicity + dependency stability |
| `TD_Side_Eff_Interface.thy` | `td_cfg_side_solver_eff` locale, `side_cfg_solve_dom_eff`, `side_analyse_eff` |
| `TD_Side_Eff_Pipeline.thy` | ties mono/static contract + collecting soundness for an arbitrary `etf` |
| `TD_Side_Eff_Sound.thy` | `post_fixpoint_sound_at_eff` |
| `TD_Side_Eff_Soundness.thy` | collecting soundness with pruning |
| `TD_Side_RHS_Generator.thy` | `unit_rhs_generator` / `mixed_rhs_generator` locale stacks; `threefold_mono` discharge |

## `Context/`

`Context/README.md` is the pointer; per-concern inventories in
`Context/Activation/README.md`, `Context/DG/README.md`, `Context/Read/README.md`.

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
