# Migration — retire `TD_plain`, depend only on `TD_side`

Status: **DONE.** The interprocedural (IP) analysis now rides entirely on the
side-effecting solver (`TD_side`); `TD_plain` and everything built on it have
been deleted. `rg TD_plain src` is empty and the full `Voblint_Formalization`
session builds green, sorry-free, with `TD.TD_plain` no longer loaded.

Completed slices (each additive + build-gated until S5):

* **S1** `TD_Side_IP_CFG` — `side_cfg_T_ip` (edge fold + combine fold over
  `side_rhs_fold_ip`), denotation (`side_acc_ip`/`side_glob_ip`), full
  monotonicity, dependency/side independence, and the three `TD_side`
  preconditions (`is_mono_eq`/`mono_sides`/`mono_deps`). Also the per-edge and
  per-combine post-solution bounds (`apply_tf_combined_le_ip`,
  `combine_combined_le_ip`), dep membership, and the globals-free entry lemma.
* **S2** `TD_Side_IP_Interface` — packages `cfg_side_T_ip_pkg`, interprets
  `TD_side_mono`, reads back `side_sigma_at`/`side_stabl_at`/`side_env_at`, and
  exposes the executable `side_analyse_ip` over `compile_prog`.
* **S3** `TD_Side_IP_Soundness.side_collect_sound_ip_at` — IP collecting
  soundness over a side post-solution, reusing the generic, solver-agnostic
  bridge `post_fixpoint_sound_at_ip` with `env := side_env sigma`. The combine
  result splits `restrict_local` (caller locals) / `restrict_global`
  (callee-exit globals).
* **S4** Reachability (`ip_reaches_imp_trans_dep_or_eq_side`,
  `side_ip_cone_in_vars`) + pruned exit soundness
  (`side_collect_sound_ip_exit_pruned`, no coverage hypothesis) + the executable
  `side_analyse_ip_collect_sound_exit_pruned`, the Sign instantiation
  (`Sign_Side_IP_Soundness.side_ip_sign_analysis_sound`), and the end-to-end
  witness `Example_Side_Proc_Global`. The digest overlay (`Analysis_Sound`,
  `Trace_IP_Analysis_Sound`) needed **no** re-point — it sits at the
  constraint/collecting level and is solver-agnostic.
* **S5** Deleted `TD_CFG_Core`, `TD_CFG_IP_Core`, `TD_Interface`,
  `TD_IP_Soundness`, `Sign_IP_Soundness`, `Example_Proc_Global`; dropped
  `CFG_Prune`'s plain reach-discharge lemmas and its `TD_CFG_IP_Core` import.

Everything below is the original plan, kept for the record.

---

The interprocedural (IP) analysis used to ride on the plain top-down solver
(`TD_plain`); this migration re-expressed it over the side-effecting solver
(`TD_side`) and then deleted `TD_plain` and everything built on it.

> This **reverses** the unified-handoff decision "two backends stay"
> (`UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md` §7). The justification: in Voblint the
> side-effecting constraint system is the universal one — flow-sensitive locals
> and flow-insensitive globals both go through it; plain TD is a special case with
> no side effects. One backend is the faithful end state.

## 0. The key fact — this is a rewrite, not a deletion

You cannot "delete files using `TD_plain`" and keep the analysis: **the entire IP
spine is built on `TD_plain`.**

`rg TD_plain src` consumers: `TD_CFG_Core`, `TD_CFG_IP_Core` (comment: *"Solver
stays TD_plain"*), `TD_Interface` (`td_cfg_ip_solver = td_cfg_ip_core + TD_plain
cfg_T_ip`), `TD_IP_Soundness`, `Sign_IP_Soundness`, `Example_Proc_Global`,
`Constraint_System` (RHS format *"expected by the TD_plain locale"*).

`TD_side` consumers are only the Side (M3) stack: `TD_Side_CFG`,
`TD_Side_Interface`, `TD_Side_Soundness`, `Sign_Side_Soundness`,
`Example_Side_Global`.

The two solvers use **different data structures**, with no subsumption in the
vendored AFP `TD`:

| | plain (IP today) | side (target) |
| --- | --- | --- |
| RHS object | `(pp, 'a abs_state) strategy_tree` | `(pp, unit, 'a abs_state) eqsT` |
| build fn | `make_rhs_tree_ip` | `side_cfg_T`-style |
| denotation | `traverse_rhs` | `eq` + `sides_of_rhs` (`Query`/`Side`) |
| solver | `TD_plain.solve` / `partial_correctness` | `TD_side_mono.solve` |
| solver precond | (none beyond tree) | `is_mono_eq` + `mono_sides` + `mono_deps` |

So retiring `TD_plain` = re-encode the IP equation system as a side-effecting one
and re-prove IP soundness over `TD_side`. Then delete the plain stack.

## 1. The template — `TD_Side_CFG`

The Side (M3) stack already does exactly this for the **intra** CFG with a
locals/globals split. `src/Solver/TD_Side_CFG.thy` is the blueprint; reuse its
shape verbatim for IP, extending only the per-point fold:

- `side_rhs_fold` folds incoming edges into a `QueryL u / QueryG () / Side ()`
  chain; `make_side_rhs_tree` seeds the entry; `side_cfg_T` is the `eqsT`.
- Denotation lemmas: `side_acc` (local fold, `= eq`), `side_glob` (global side
  contribution, `= sides_of_rhs … (Inr ())`), with `traverse_side_rhs_fold`,
  `eq_side_cfg_T`, `sides_side_rhs_fold_Inl/Inr`.
- Solver preconditions: `side_cfg_T_is_mono_eq`, `side_cfg_T_mono_sides`,
  `side_cfg_T_mono_deps` (all from `tf_mono` + the `side_acc/side_glob/dep_aux`
  monotonicity lemmas).
- Post-solution bounds: `side_post_solution_le_local/_global`,
  `apply_tf_combined_le`, dependency/reachability
  (`cfg_path_node_in_trans_dep_side`, `side_vars_on_query_path`), and the
  collecting-soundness theorem `side_collect_sound_path` / `side_collect_sound_at`
  inside `context sound_transfer`.

## 2. The gap — encoding the interprocedural combine

The intra `side_rhs_fold` handles ordinary edges only. IP adds two constructs the
plain encoding carries (`make_rhs_tree_ip` in `TD_CFG_IP_Core`, combine triples in
`compile_prog`):

- **`EA_Enter` edges** `(call, EA_Enter, proc_entry)` — a plain edge in the fold,
  no special handling needed beyond inclusion in `predecessor_list`.
- **Combine triples** `(call, proc_exit, return)` in `combines g` — the return
  point reads *two* unknowns (caller `call` and callee `proc_exit`) and combines
  them (`combine_states`). This is the real extension: the per-point RHS for a
  return node must, in addition to the edge fold, query both endpoints of each
  incoming combine triple and join `combine_states su sx`.

Design for `side_rhs_fold_ip` (new): after the edge fold, fold the incoming
combine triples `[(call, ex) | (call, ex, v) <- combines g]` as a
`QueryL call / QueryL ex / answer-join combine_states` chain. Globals: the combine
result also splits local/global like the edge case (`restrict_local`/
`restrict_global` + `Side ()` for the global part) — confirm against the digest
semantics (`cfg_collect_ip` `collect_combine_pp`).

Open question: digest indexing (M4). The current IP soundness is digest-refined
(`Trace_IP_Analysis_Sound`, `Analysis_Sound`). Decide whether the side encoding
carries the digest hook or whether digest precision is re-derived as an overlay
(as it is now over the plain solver). Recommend: keep the side encoding
digest-agnostic first (match `cfg_collect_ip`), reattach digest as the existing
`alpha_last` overlay.

## 3. Slices (each additive + build-gated; delete plain only at the end)

| Slice | New / changed | Exit |
| --- | --- | --- |
| S1 | `TD_Side_IP_CFG` — `side_cfg_T_ip` (edge fold + combine fold), denotation, `is_mono_eq`/`mono_sides`/`mono_deps` | theory builds, monotonicity green |
| S2 | `TD_Side_IP_Interface` — package `cfg_side_T_ip`, `TD_side_mono.solve` readback, `side_env_at` (mirror `TD_Side_Interface`) | solver interpretation green |
| S3 | IP collecting soundness over the side post-solution: `side_collect_sound_ip_at` (mirror `side_collect_sound_at`, add the combine step into the per-edge/-combine bound) against `cfg_collect_ip` | soundness theorem green |
| S4 | Re-point `Constraint_System_IP_Sound` / `Analysis_Sound` (or add side variants), then `TD_IP_Soundness`, `Sign_IP_Soundness`, `Example_Proc_Global` onto the side solver. Re-attach digest (`Trace_IP_Analysis_Sound`) as overlay | examples green, no `TD_plain` use left in IP |
| S5 | Delete `TD_CFG_Core`, `TD_CFG_IP_Core`, `TD_Interface`, the `TD.TD_plain` import, `make_rhs_tree`/`make_rhs_tree_ip`, and any now-dead constraint-format lemmas. Drop `TD_plain` from `ROOT` reach | `rg TD_plain src` empty; full build green |

## 4. Risks

- **Combine encoding correctness** (S1/S3) — the side combine fold must match
  `collect_combine_pp` of `cfg_collect_ip`; get the local/global split right for
  combine results, not just edges. Highest-risk step.
- **`Constraint_System` RHS format** is currently "expected by the TD_plain
  locale." Deleting plain (S5) means re-checking nothing else (Sign domain,
  examples) depends on `make_rhs_tree` shapes.
- **Digest / M4** — keep out of S1–S3; reattach as overlay in S4 to avoid baking
  context-sensitivity into the new encoding.
- Effort: comparable to the original M3 Side slice **per** IP construct — this is a
  research-grade migration, not a refactor. Budget multiple sessions; keep each
  slice additive so `main` stays green until S5.

## 5. Build gate

```bash
isabelle build -v -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization
```

I/Q for development (`./scripts/start-both.sh`); each slice exits sorry-free.
