# TD-side solver interface

The effectful interprocedural solver interface built on the strategy-tree monad
(`../Strategy_Tree/`): generator, monotonicity, and the base collecting-soundness
theorem. Everything here is domain-agnostic; concrete reads/writes live in
`../Context/`, executable mirrors in `../Exec/`. See `../README.md` for how the
four subfolders fit together.

| File | Role |
| --- | --- |
| `TD_Side_CFG.thy` | `restrict_local`/`restrict_global`, `side_env`; unit-global tree constructors; `trans_dep\<^sub>L` step/trans lemmas |
| `TD_Side_Tree.thy` | `side_cfg_T_eff` effectful IP strategy trees; folds `side_acc_eff` |
| `TD_Side_Eff_Bounds.thy` | monotonicity + dependency stability |
| `TD_Side_Eff_Cone_Lemmas.thy` | dependency cone, exit pruning and entry seeding re-established for the effectful equation system, with pruning |
| `TD_Side_Eff_Interface.thy` | `td_cfg_side_solver_eff` locale, `side_cfg_solve_dom_eff`, `side_analyse_eff` |
| `TD_Side_Eff_Pipeline.thy` | ties the mono/static contract to collecting soundness for an arbitrary `etf` |
| `TD_Side_Eff_Sound.thy` | `post_fixpoint_sound_at_eff` |
| `TD_Side_RHS_Generator.thy` | `unit_rhs_generator` / `mixed_rhs_generator` locale stacks; `threefold_mono` discharge |
| `LTR_TD_Side_Eff_Sound.thy` | effectful equation-system soundness over the stack-faithful local-trace collector `ltr_collect` |
| `LTR_TD_Side_Eff_Exit.thy` | effectful solver soundness at the program exit over the original CFG's `ltr_collect`, with no graph transformation or compiled-CFG restriction |
