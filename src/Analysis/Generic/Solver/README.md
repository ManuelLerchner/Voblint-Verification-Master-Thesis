# TD solver bridge (side-effecting, interprocedural)

Connect the vendored **TD side** solver (`vendor/td-verification`, session `TD`, theory `TD_side`)
to the interprocedural CFG and effectful `rhs` format.
`side_analyse_eff pi ps c etf bot s0 v` is proved sound against `cfg_collect` at `v`
(`side_analyse_eff_collect_sound_exit_pruned_gen`).

The layer is split into three concerns, one subfolder each:

| Subfolder | Concern |
| --- | --- |
| `Core/` | the TD-side strategy-tree spine: monad, generator, monotonicity, base collecting soundness |
| `Context/` | context-indexed / cmp-filtered / digest-refined global reads and their soundness |
| `Exec/` | the `'a st` executable mirror and `fun_of_st` transport |

**External:** Algorithm correctness is in `TD.TD_side` (`partial_correctness`, `TD_side_mono`).
This layer wires `part_post_solution` to `is_post_fixpoint` via `Generic/Equations/Constraint_System_Sound`.

**Downstream:** `Instances/Sign/Sign_Side_Soundness.thy` — `side_sign_analysis_sound`;
`Instances/Interval/Interval_Side_Soundness.thy`; `Formalization/Pipeline/Trace_Analysis_Sound.thy`.

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

Context-indexed and digest-refined global reads. `Digest_Global_Read` holds the kernel
locale `digest_global_read` (`obs_digest`); `Global_Cmp_Read` / `Context_Domain` are the
degenerate context-only base the digest read collapses to; the `TD_Side_Eff_Cmp_*` /
`TD_Side_Eff_Ctx_Sound` files carry the EDGE/ENTRY discharge and combine soundness the
kernel builds on. `Value_Digest_Reader` is the generic value-projected reader locale
(`value_digest_reader`, `vd_obs`) the sign mode reader instantiates. `Digest_Keyed_Writer{,_Sound}`
is the value-derived (mode) writer.

## `Exec/`

`Exec_Bridge` (`'a st` fold mirror + `fun_of_st` simulation + the generic
`part_post_solution_st_to_abs_transport`), `Exec_Ctx_Bridge`, `Exec_Cmp_Bridge`
(executable generator variants and their transport), and `Solver_Side_RG` (reach-global
lemmas). `Digest_Keyed_Writer{,_Sound}` in `Context/` imports this chain.

`Solver_Menu` bundles the vendored update-rule solvers (`join`, `per_origin`, `warrow`)
behind one `side_solver` signature; `run_menu eqs entry k var` reads one slot's variable
under every discipline in a single `value`/lemma. Currently an executable convenience only
— soundness per rule is the subject of `docs/UPDATE_RULE_FORMALIZATION_PLAN.md`.

`Origin_Lift` realises **per-origin widening** as an equation-system transform, sidestepping
the vendored `warrowing_per_origin` rule that does not code-generate (P11). It lifts an
existing system's value domain to `('o, 'd) origin_st` (`Domain/Origin_State`): reads
`collapse_origins` the origin map, writes `inject_origin` at the evaluated unknown's origin,
transfers unchanged. The lifted system runs under the ordinary Apinis warrowing solver, whose
pointwise widening on `origin_st` is per-origin widening — so it `eval`s directly.
`TD_side_per_origin_widen_solve org_of T v` / `read_per_origin` are the entry points.
