# Solver core — the TD-side strategy-tree spine

The effectful interprocedural solver spine: strategy-tree monad, generator,
monotonicity, and the base collecting-soundness theorem. Everything here is
domain-agnostic; concrete reads/writes live in `../Context/`, executable mirrors
in `../Exec/`. See `../README.md` for how the three subfolders fit together.

| File | Role |
| --- | --- |
| `Strategy_Tree_Monad.thy` | `seqcomp_tree` (bind), `traverse_seqcomp`, `dep_aux_seqcomp`, `sides_of_rhs_seqcomp`; `static_deps`, `seqcomp_mono` |
| `TD_Side_CFG.thy` | `restrict_local`/`restrict_global`, `side_env`; unit-global tree constructors; `trans_dep\<^sub>L` step/trans lemmas |
| `TD_Side_Tree.thy` | `side_cfg_T_eff` effectful IP strategy trees; folds `side_acc_eff` |
| `TD_Side_Eff_Bounds.thy` | monotonicity + dependency stability |
| `TD_Side_Eff_Interface.thy` | `td_cfg_side_solver_eff` locale, `side_cfg_solve_dom_eff`, `side_analyse_eff` |
| `TD_Side_Eff_Pipeline.thy` | ties the mono/static contract to collecting soundness for an arbitrary `etf` |
| `TD_Side_Eff_Sound.thy` | `post_fixpoint_sound_at_eff` |
| `TD_Side_Eff_Soundness.thy` | collecting soundness with exit pruning |
| `TD_Side_RHS_Generator.thy` | `unit_rhs_generator` / `mixed_rhs_generator` locale stacks; `threefold_mono` discharge |
