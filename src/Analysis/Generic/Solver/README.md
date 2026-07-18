# TD solver bridge (side-effecting, interprocedural)

Connect the vendored **TD side** solver (`vendor/td-verification`, session `TD`, theory `TD_side`)
to the interprocedural CFG and effectful `rhs` format.
`side_analyse_eff pi ps c etf bot s0 v` is proved sound against `cfg_collect` at `v`
(`side_analyse_eff_collect_sound_exit_pruned_gen`).

The layer is split into three concerns, one subfolder each:

| Subfolder | Concern |
| --- | --- |
| `Core/` | the TD-side strategy-tree spine: monad, generator, monotonicity, base collecting soundness |
| `Context/` | Goblint-facing context spine: `Goblint/Read`, `Goblint/Read/Support`, `Goblint/Routing`, `Goblint/Routing/Support`, `Goblint/DG` |
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

`Context/README.md` is the pointer. The live inventory is in
`Context/Goblint/README.md`.

## `Exec/`

`Exec_Bridge` (`'a st` fold mirror + `fun_of_st` simulation + the generic
`part_post_solution_st_to_abs_transport`) and `Solver_Side_RG` (reach-global
lemmas). The D/G product carrier is executable through `Exec_DG_Bridge`
(`fun_of_dg_st`, `dg_gen_of`, `part_post_solution_dg_st_to_abs`), which lets the
verified solver run on D/G equations; executable examples use it directly.

`Solver_Menu` bundles the vendored update-rule solvers (`join`, `per_origin`, `warrow`)
behind one `side_solver` signature; `run_menu eqs entry k var` reads one slot's variable
under every discipline in a single `value`/lemma. Currently an executable convenience only
— soundness per rule is the subject of `docs/UPDATE_RULE_FORMALIZATION_PLAN.md`.
