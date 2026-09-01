# Core refactor plan

Status: **active plan.** The execution sequence for splitting and cleaning
`Voblint_Core`, written to be followed directly. Edit it as phases land:
tick the status column, record what the build taught, and move anything that
turned out wrong into the "Decisions and corrections" section rather than
deleting it.

Read `docs/SESSION_CLEANUP_PLAYBOOK.md` first. Its procedure (survey, act on
the ranked verdict, gate) and its traps apply unchanged. This document is the
ranked verdict for Core.

## Why Core is hard to read

`Voblint_Core` is 52 theories and 25,407 lines in three folders. The folders
do not match the concepts: the executable state (`Exec_St`) sits under
`Domain/` next to the domain classes it barely uses, `Solver/Context/DG/`
holds the abstract D/G spine, its executable transport, its context
instances, and the result table at once, and the four per-domain reuse
locales are spread over two folders. Five theories exceed the 1500-line cap
(`DG_Framework` 2472, `DG_Soundness` 2317, `Exec_St` 2231,
`Abstract_Domain` 2110, `Exec_DG_Generator` 1718).

The session also mixes three things a reader wants kept apart:

1. **The abstract framework** -- what a sound analysis is and why a solved
   system covers the collecting semantics. Carrier-agnostic: `sound_dg_spec`,
   `dg_ctx_activation_base` and `routed_context_base_hetero` are generic in
   the local carrier `'D`, and `Rel_Order_Domain` already interprets them at
   a relational one.
2. **The executable transport** -- 3,700 lines (`Exec_DG_Trees`,
   `Exec_DG_Generator`, `Exec_DG_Bridge`, the transport halves of
   `DG_Base_Exec` and `Routed_Domain_Exec`, the owner-aware trees in
   `Exec_DG_Refines`) whose only job is to move a `part_post_solution` from
   the solver's quotient carrier `'a resolved_st_q` to the function carrier
   `vname => 'a` the framework was instantiated at.
3. **Base-level material** -- expression evaluation, guard refinement,
   special calls, local/global restriction -- which upstream Goblint keeps
   inside the `Base` analysis, not in the framework.

## Reference architectures

Two checked references fix the target shape.

**Goblint** (`analyzer` at `8d32b6b3d8cc08c5455817895b3af6eb5b00c21a`, the
alignment register's pinned commit). Its dune libraries are its
architecture: `goblint.domain` (`Lattice.S`, `Lift`, `MapDomain`) ->
`goblint.constraint` + `goblint.solver` (`EqConstrSys`, `GlobConstrSys`,
the `Var2`/`Lift2` translator, `td3`, `PostSolver.Verify`) -> the framework
(`Analyses.Spec`, `Constraints.FromSpec`, `Control`, `AnalysisResult`) ->
analyses (`Base`, `Callstring`) -> lifters (`Spec -> Spec` functors,
composed in a fixed order in `control.ml`). Dead code is a 75-line
`DeadCodeLifter` over the whole `Spec`, not part of the domain layer.

**HOL-IMP `Abs_State`** (`src/HOL/IMP/Abs_State.thy` in the Isabelle
distribution). `quotient_type 'a st = (vname * 'a) list / eq_st`, with
`fun_rep` as the readback and gamma, order and join defined on the
quotient. One carrier; every soundness theorem is stated over `'a st`.
Core's `'a resolved_st_q` (`Exec_St.thy`, `quotient_type` at line 267) is
the same construction and `fun_of_resolved_st_q_for gs` is its `fun_rep`.

The difference from both: Core states the framework over `vname => 'a`,
solves over the quotient, and transports the solved system back. The
register records the cause ("the semantic layer was built before the
executable route"). The plan removes the transport, not the quotient.

## Evidence the plan rests on

Measured with two scratchpad scripts, both worth recreating:

- `edge_usage.py` -- for an (importer, imported) pair, which names defined
  in the imported theory the importer mentions. Distinguishes a real
  dependency from an import that only rides along.
- `partition_check.py` -- given a session assignment per theory and the
  session order, lists every import edge that points from an earlier session
  to a later one.

Findings that decide the phases:

| Import edge | What crosses it | Verdict |
| --- | --- | --- |
| `Abstract_Domain -> Voblint_CFG.CFG_Def` | `type_synonym pp = cfg_node`, one line | move `pp` |
| `DG_Framework -> Exec_Placement` | nothing | drop |
| `DG_Framework -> Exec_St` | the `bounded_warrowing` class, three mentions | move the class |
| `Context_Refinement -> Constraint_System` | `part_post_solution_iff_se_constraint_holds`, one lemma | move the block |
| `CFG_Enumeration -> Voblint_Compile.VIMP_Proc_to_CFG` | no compiler name | repoint |
| `Analysis_Result -> Exec_St` | `normalize_point`, lines 133-250 | move the readback |
| `Exec_St -> Constraint_System` | `enter_frame_D`, `combine_env_abs`, `enter_D` | real; exec is below core |
| `Monovariant_Analysis_Result -> Compile_Invariants` | `prog_cfg` | real; stays after Compile |

Usage counts (`rg -w` over `src/`):

- `td_cfg_side_solver_dg` with `cfg_pkg_dg`, `stabl_at`, `nu_at`
  (`DG_Framework` 2365-2470): no user outside the file.
- `sound_dg_hooks`, `sound_dg_hooks_ltr`, `hook_gen`, `gamma_join`,
  `unit_dg_spec_placed`: reached only from `Example_Sign_Placement` and
  `Example_Interval_Placement`. The spec route (`sound_dg_spec`, interpreted
  12 times) is what Analysis and Soundness use.
- `Exec_Placement` (1134 lines): imported by `DG_Framework`, which uses nothing
  from it, and reached through that import by `Exec_DG_Refines`,
  `Exec_DG_Trees` and `Exec_DG_Generator`, which use 70 of its names (see
  "Decisions and corrections"). It is the executable transport's support
  algebra.
- Fourteen of `DG_Framework`'s 45 definitions and nine of `DG_Soundness`'s
  27 have no use outside their file.
- `routed_context_hetero` restates all six assumptions of
  `routed_context_base_hetero` verbatim and then declares it a sublocale;
  `unit_routed_context_hetero` does the same to `unit_routed_context`.
- `routed_dg_domain_exec` (`DG_Base_Exec` 168) is the whole per-domain
  executable obligation: three commute facts against
  `fun_of_resolved_st_q_for`.

Style baseline for the proof half: 45 `metis` (19 in `Exec_DG_Generator`,
13 in `Exec_St`), 61 `apply` lines (14 `Routed_Domain_Exec`, 12 each
`DG_Framework` and `DG_Soundness`, 10 `Activation_Local_Sound`), four
`[rule_format]`, 31 lemmas named `...I`/`...E`/`...D` without their
attribute, three theories without an orientation block. The two longest
proofs are `dg_post_solution_postfix` (272 lines) and
`side_cfg_T_eff_keyed_seed_dg_buffered_correspondence` (249).

## Target layout

Sessions follow Goblint's library boundaries. One extra session exists only
until Phase 2 deletes what it holds.

| Session | Goblint counterpart | Theories | Parents |
| --- | --- | --- | --- |
| `Voblint_Domain` | `goblint.domain` | `Abstract_Domain`, `Reachability_Lift`, `Nonrelational_State`, `Nonrelational_Reachability`, `Backward_Domain`, `Abstract_Numeric_Queries` | `Voblint_VIMP`, `TD` |
| `Voblint_Solver` | `goblint.constraint`, `goblint.solver` | `Strategy_Tree_Monad` (absorbing `Strategy_Tree_Do`, `Solver_Mono`), `Strategy_Tree_Rhs`, `Strategy_Tree_Relabel`, `Strategy_Tree_Combinators`, `Side_Buffering`, `Post_Solution` (new), `Context_Refinement` | `TD` only |
| `Voblint_Core` | `Analyses`, `Constraints`, `Control`, `AnalysisResult` | `CFG_Enumeration`, `Constraint_System` (absorbing `Constraint_System_Sound`), `State_Restriction`, `DG_Framework`, `DG_Unit_Spec`, `DG_Keyed_Generator`, `DG_Soundness`, `DG_LTR_Sound`, `Activation_Local_Sound`, `Activation_Backbone`, `DG_Ctx_Activation`, `DG_Transfer_Combinators`, `Routed_Context`, `Routed_Context_Unit`, `DG_Base`, `Call_String_Context`, `Call_String_Collecting_Refinement`, `Call_String_Solver_Projection`, `Analysis_Result`, `Checks`, `Abstract_Checks`, `DG_Analysis_Adapter`, `DG_Coverage` | `Voblint_CFG`, `Voblint_Domain`, `Voblint_Solver` -- never `Voblint_Compile` |
| `Voblint_Exec` (quarantine) | none | `Exec_DG_Refines`, `Exec_DG_Trees`, `Exec_DG_Generator`, `Exec_DG_Bridge`, `DG_Base_Exec`, `Routed_Domain_Exec`, `Solver_Side_RG`, `TD_Solver_Menu`, `Monovariant_Analysis_Result` | `Voblint_Core`, `Voblint_Compile` |
| into `Voblint_Analysis` | `analyses/base.ml`, `lifters/` | `Abstract_Arithmetic`, `Special_Ops`, `Numeric_Ops`, `Exec_Backward`; `Call_String_Context_Finite`, `Call_String_Routed_Context`, `Entry_State_Routed_Context` | |
| into `Voblint_Examples` | none | the hooks route: `sound_dg_hooks` and the hook-parametric section (`DG_Soundness` 968-1508), `sound_dg_hooks_ltr`, `gamma_join`, `unit_dg_spec_placed`, as a `Placement/` group next to the two examples that use them | |

The session graph after Phase 1:

```text
VIMP -> Domain -+
                +-> CFG -> Core -+-> Compile -> Exec -> Analysis -> ...
TD   -> Solver -+                |
                                 +-> Compile (unchanged)
```

`Voblint_Core` is compiler-free for the same reason `Voblint_CFG` is: the
soundness endpoints are stated for an arbitrary CFG, and only a session
boundary enforces that.

## Phases

Each phase is one gate run and one PR. Do not polish in an earlier phase
what a later phase deletes.

### Phase 0 -- boundary repairs, no proof changes

| # | Step | Status |
| --- | --- | --- |
| 0.1 | Move `type_synonym pp = cfg_node` from `Abstract_Domain` to `CFG_Def`; drop `Abstract_Domain`'s `CFG_Def` import. | landed |
| 0.2 | Move `bounded_widening`, `bounded_narrowing`, `bounded_warrowing` and `instance lifted :: bounded_warrowing` from `Exec_St`'s preamble into `Abstract_Domain`. Drop `DG_Framework`'s `Exec_St` and `Exec_Placement` imports. | landed |
| 0.3 | Move the `se_constraint_holds` block (`Constraint_System` 1008-1053: definition, two `[dest]` halves, `part_post_solution_imp_se_constraint_holds`, `part_post_solution_iff_se_constraint_holds`) to a new `Solver/Strategy_Tree/Post_Solution.thy` importing `Strategy_Tree_Rhs`. Repoint `Context_Refinement`. | landed |
| 0.4 | `CFG_Enumeration`: import `Voblint_CFG.CFG_Transfer` instead of `Voblint_Compile.VIMP_Proc_to_CFG`. The build shows whether a VIMP name rode on the transitive import. | landed |
| 0.5 | Move `normalize_point` and its lemmas (`Analysis_Result` 133-250) into `Monovariant_Analysis_Result`. `Abstract_Checks` cites `normalize_point` once; repoint its import for now and resolve in Phase 2. | landed |
| 0.6 | Delete `td_cfg_side_solver_dg`, `cfg_pkg_dg`, `stabl_at`, `nu_at`, `solve_prod`, `part_post_at`, `least_part_post_at` (`DG_Framework` 2365-2470). Then check `threefold_mono` (one remaining user, `Voblint.thy`). | landed |
| 0.7 | Delete the other zero-use definitions in `DG_Framework` and `DG_Soundness` one at a time; keep any the build wants (grep cannot see simp-set uses). | open -- every candidate has internal users (it is a self-contained cluster with no external consumer, e.g. `pair_of_dg`/`dg_of_pair`/`merge_dg`/`split_dg`, `dgs_enter_pair`, `apply_dg_spec_contribution_at`, `indep_dg_spec`, `gamma_dg`, `dg_trees`/`dg_acc`, `hook_trees`/`hook_acc`, `gamma_unit_lifted`); deciding per cluster is Phase 3 work |
| 0.8 | Run `partition_check.py` with the target assignment: zero violating edges is the exit criterion. | landed |

Gate: `AFP=$HOME/afp/thys pixi run build`, `pixi run codegen`,
`pixi run codegen-modules`, `pixi run cli-test`, `pixi run codegen-regression`,
`pixi run property`.

### Phase 1 -- sessions

Mechanical once Phase 0 is green.

| # | Step | Status |
| --- | --- | --- |
| 1.1 | Split `Abstract_Domain` at line 919: `Backward_Domain.thy` takes `semantic_intersection`, `backward_domain`, `backward_domain_refined`, the inverse-operator sections, `show_val`. | landed (`Backward_Domain.thy`, 1180 lines; `Abstract_Domain` 1013) |
| 1.2 | Rename `Exec_St` to `Abstract_State` (it is the quotient state, the counterpart of HOL-IMP's `Abs_State`; nothing about it is specific to execution). Keep the constant names for now. | deferred with 1.1 |
| 1.3 | Extract the hooks route from `DG_Soundness` (968-1508) and `DG_LTR_Sound` (`sound_dg_hooks_ltr`), plus `gamma_join` and `unit_dg_spec_placed`, into `Examples/Placement/Placement_Hooks.thy`. Move `Exec_Placement` beside it. | landed as `Examples/Placement/Placement_Policy.thy`: the `*_placed` specification, `gamma_join` and its section, and `sound_dg_hooks_ltr`; `sound_dg_hooks` itself stays, it is the engine `sound_dg_spec` reduces to |
| 1.4 | Create `src/Domain/ROOT`, `src/Solver/ROOT`, `src/Exec/ROOT`; rewrite `src/Core/ROOT`; add the four directories to `ROOTS`. | landed |
| 1.5 | Move the seven Base-level and compile-dependent theories into `src/Analysis/` (`Instances/Common/` for the four reuse locales, `Instances/Ctx/` for the three routed contexts, or wherever the Analysis README's layout puts them). | landed |
| 1.6 | Repoint every qualified import across Analysis, Soundness, CLI, Codegen, Examples. Check by arity where a locale header changed, not by grep. | landed |
| 1.7 | Extend the `code_identifier` block in `Analyse_Dispatch.thy` for every new session whose constants reach an export root; run `pixi run codegen-modules`. | landed |
| 1.8 | Rewrite the READMEs from the final tree: `src/Domain`, `src/Solver`, `src/Core`, `src/Exec`; delete `Solver/Context/Activation/README.md` and `Solver/Context/DG/README.md` (both list theories that do not exist). Fix `GLOSSARY.md`'s `dg_gen_of` path and the session graph in `AGENTS.md`. | landed |

### Phase 2 -- one carrier

Spike before committing to it.

| # | Step | Status |
| --- | --- | --- |
| 2.1 | Spike on Sign, in a scratch theory: interpret `sound_dg_spec` at `base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st` with `gammaDG d g = gamma_state (fun_of_resolved_st_q_for gs (unlift d)) ...` using only `routed_dg_domain_exec`'s three commute facts and Sign's `sound_transfer_for`. Then `dg_ctx_activation_base` and `routed_context_base_hetero` at that carrier. Exit criterion: no citation of anything in `Voblint_Exec` except `Exec_DG_Refines`'s lattice instances for `exec_dg_st`, and `cli-test` green with Sign routed through the new interpretation. | landed: `Examples/Tooling/Spike_Sign_Quotient.thy` |
| 2.2 | If 2.1 fails, record why under "Decisions and corrections", keep `Voblint_Exec` as a permanent session named for what it is, and skip to Phase 3. | open |
| 2.3 | Delete `Exec_DG_Trees`, `Exec_DG_Generator`, `Exec_DG_Bridge`; the transport half of `DG_Base_Exec` (keep `routed_dg_domain_exec` and the `base_dg_spec_st_for_lifted` commute lemmas it cites); the owner-aware trees and classifier-parametric readback in `Exec_DG_Refines` (keep the `exec_dg_st` lattice instances and `fun_of_dg_st_for`). `Routed_Domain_Exec` stays -- superseded, see decision below. | partly landed (2026-08-31) -- `Exec_DG_Bridge` itself is deleted, zero remaining importers. `Exec_DG_Trees`, `Exec_DG_Generator`, and `Routed_Domain_Exec` are load-bearing and stay (see "Decisions and corrections"); the owner-aware half is now deleted (2026-09-01, G1-G6 of `docs/MERGE_SPLIT_GENERALIZATION.md` executed): `merge_split_spec`/`merge_split_spec_exec` generalize the unit/placed skeleton once; `Placement_Policy_Exec` supplies the classifier-split executable projection, `unit_dg_spec_placed_st`, and the `placed_dg_exec_analysis` registration locale; `Example_Sign_Placement` (949 -> 153 lines), `Example_Interval_Placement` (2926 -> 203), and `Example_Interval_Global_Flow_Sensitivity` re-solve on that spine with every value, check, and equation-count regression reproducing unchanged; then `Exec_Placement.thy` (1149 lines) is deleted whole and the owner-aware halves of `Exec_DG_Refines` (863 -> 379), `Exec_DG_Trees` (905 -> 96) and `Exec_DG_Generator` (1719 -> 1009) are removed. `dg_gen_of`, the classifier-parametric readback, the unit executable ops, and the carrier-generic commute engine are what remains. Step closed |
| 2.4 | `routed_context_hetero` becomes `routed_context_base_hetero` at whichever carrier the instance chooses; delete the restated assumptions. Same for `unit_routed_context_hetero`. | landed: `entry_state_routed_context` and `call_string_routed_context` (Analysis) are stated at a carrier parameter with `gammaDG`/`gammaM` and sublocale `routed_context_base_hetero`; `routed_context_hetero` and `unit_routed_context_hetero` are deleted, having no interpreter left |
| 2.5 | `Analysis_Result` holds the quotient; `normalize_point` becomes the single readback at publication, in `DG_Analysis_Adapter`. `Abstract_Checks` reads the published table. | landed in the generic form: `dg_analysis_adapter` extends `routed_context_base_hetero` and takes a readback `rd` with `gammaDG d g = gamma_state_lift (rd d)`; the four abstract-carrier sites pass `rd = id` |
| 2.6 | Rewrite the twelve `*_Ctx_*_Sound` theories and the four CLI `*_Entry` theories to interpret at the quotient carrier. Expect the transport boilerplate that NEXT_STEPS records as the 23-suffix duplication to shrink. | landed: the four unit-context instances (Sign, Parity, Interval, Int, with their `*_Checks`/`*_Entry` consumers), the three entry-state instances and the two call-string instances are on the executable carrier; the two Interval entry-state examples and `Example_Interval_Source_Ctx` follow the theory; the four CallString examples interpret `call_string_routed_context` at their executable spec and get their headline theorem from `activation_collect_sound`. `Run_Analysis_Sound`'s flat bundles and `Interval_Ctx_Entry_State_Sound`'s hand-rolled Hstep/Henter/Hcomb/Hcont transport lemmas are migrated too (2026-08-31 decision entry); `ectx_abs_spec`/`entry_state_route_abs_gen` stay by design, being the genuine abstract-carrier route witness. What is left on the transport now is only `Example_Sign_Placement`, `Example_Interval_Placement`, and `Monovariant_Analysis_Result` -- tracked under 2.3, not 2.6 |
| 2.7 | Move `routed_dg_domain_exec`, `Solver_Side_RG`, `TD_Solver_Menu`, `Monovariant_Analysis_Result`, `DG_Coverage` to their final homes (`DG_Base`, Solver, Core); retire `Voblint_Exec` from `ROOTS`. | partly landed (2026-09-01, see decision entry): `TD_Solver_Menu` moved to `Voblint_Solver`, `Solver_Side_RG` deleted whole (its one generic fact, `solve_dom_of_solve_c`, folded into `TD_Solver_Menu`; the rest was confirmed dead, not carrier-specific-but-kept). `routed_dg_domain_exec` and most of `Monovariant_Analysis_Result` stay in `Voblint_Exec` -- they are the executable-carrier transport itself, not misplaced generic content, and cannot move before the carrier does. `DG_Coverage` (confirmed fully generic) and the 12x-repeated domain/context solve-bridge boilerplate remain open, deliberately not touched this round |

### Phase 3 -- inside the theories

| # | Step | Status |
| --- | --- | --- |
| 3.1 | One `dead_code_lift :: ('dl, 'dg) dg_spec => ('dl lifted, 'dg) dg_spec` with `sound_dg_spec S ==> sound_dg_spec (dead_code_lift S)`; `base_dg_spec_for_lifted`, `unit_step_for_lifted`, `unit_dg_spec_for_lifted` and `base_dg_spec_st_for_lifted` become instances. This is Goblint's `DeadCodeLifter`, stated once. Design the seam so widening delay and context gas can use it. | open -- and narrower than written: the merge/split research (2026-09-01 decision entry, `docs/MERGE_SPLIT_GENERALIZATION.md`) found this step was conflating two axes. The merge/split axis (unit vs placed routing) is handled by that document's own generalization and is no longer on 2.3's critical path; what remains for 3.1 is only the orthogonal Bot-carrier wrapper `('dl,'dg) dg_spec => ('dl lifted,'dg) dg_spec` with `sound_dg_spec S ==> sound_dg_spec (dead_code_lift S)`, which then wraps one unlifted core instead of two, with the four `*_for_lifted` constructions as its instances. Design pass complete (2026-09-01): the external carrier-architecture review and the follow-up lifter-pipeline session fixed the shape -- reachability-first functor with `lift_gamma`, normalization as a separate layer over an explicit emptiness interface, one executable commute-preservation theorem per lifter, `\|>` pipe bundle deferred until a second lifter exists; see "External review" and "Lifter pipeline design" in `docs/MERGE_SPLIT_GENERALIZATION.md`. Core landed (2026-09-01, uncommitted): `src/Core/Lifters/DG_Dead_Code_Lift.thy` holds `dead_code_lift` + `lift_gamma` + `dead_code_lift_sound`, `sound_dg_spec_cong`, `dead_code_normalize` + its soundness, and the `dg_spec_commute` naturality theorems (`dead_code_lift_commute`, `dead_code_normalize_commute`); `DG_Base` gains the unlifted `base_dg_spec_for` and re-derives `base_dg_spec_sound` through the functor chain, deleting its three hand-rolled obligation walls. The unit-lifted family (`unit_step_for_lifted`, `unit_dg_spec_for_lifted`, `gamma_unit_lifted` + walls, `assemble_env_abs`; ~460 lines) turned out consumer-free -- absent from every other theory and the generated OCaml -- and is deleted rather than subsumed; the canonical dead-code-aware unit analysis is now the one-expression functor application (see the design doc's resolved finding 3a). Remaining: wire the Base executable records onto `dg_spec_commute` when a second lifter lands; batch gate at phase end. Step 3.3 progress: DG_Soundness's four `apply` sites converted to structured Isar in the same pass. |
| 3.2 | Split `DG_Framework`: the homogeneous unit analysis (685-956) and the keyed generators (1393-end) are separate concerns from the `dg_spec` record and edge trees. Split the domain foundation at the reachability lift. | landed: `Abstract_Domain`, `Reachability_Lift`, `Nonrelational_State`, and `Nonrelational_Reachability` separate value semantics, generic reachability, pointwise stores, and their composition; `combine_env` is the sole pointwise selector and `State_Restriction` derives projections from it. `DG_Framework` (2230 lines) split three ways: the file itself keeps only the carrier-agnostic core (`dg_state`, `dg_edge_tree`/`dg_combine_tree`, the fold combinators `side_rhs_fold_dg`/`side_acc_dg`, the `dg_spec` record and `apply_dg_spec`) at 951 lines; `DG_Unit_Spec.thy` (327 lines) holds the homogeneous `unit_dg_spec_for`/`unit_combine_step_*` instantiation; `DG_Keyed_Generator.thy` (995 lines) holds the keyed generators, the buffered-generator correspondence proof, and the generic instance's `threefold_mono` discharge. All three under the 1500-line cap. Only two theories anywhere directly `imports DG_Framework`'s pre-split content and needed repointing (`DG_Soundness`, `Example_Keyed_Solver_Update_Rule_Regression`); everything else reached it transitively through `DG_Soundness` and needed no change |
| 3.3 | Retire `metis`: after Phase 2 the count is 26; `Abstract_State` holds 13. Retire the 61 `apply` lines; `Activation_Local_Sound`'s 10 and `Routed_Domain_Exec`'s 14 first. | open |
| 3.4 | Hoist `dg_post_solution_postfix` (272 lines) and `side_cfg_T_eff_keyed_seed_dg_buffered_correspondence` (249) into helper lemmas with named subgoals. | open |
| 3.5 | Tag the 31 untagged `...I`/`...E`/`...D` lemmas or rename them; remove the four `[rule_format]`; add orientation blocks where missing; move the `section` heading below the `theory` header in the four `Exec_DG_*` survivors, if any survive. | landed: repo-wide sweep of `src/Core` and `src/Analysis` found 23 untagged `I`/`E`/`D`-named lemmas (down from 31, some already fixed by earlier passes). 21 tagged (`[dest]`: `vars_cover_edgeD`/`_enterD`/`_combineD`, `dg_postfix_entryD`/`_edgeD`/`_enterD`/`_combineD`, `hook_postfix_entryD`, `le_dg_state_localsD`/`_globsD`, `special_min_soundD`/`_max_soundD`/`_min_monoD`/`_max_monoD`, `ev_soundD`/`_monoD`, `calls_source_uniqueD`; `[elim]`: `first_deciding_SomeE`, `first_deciding2_SomeE`, `int_dom_not_bot_componentsE`; `[intro]`: `distinct_map_filterI`). Two left deliberately bare: `gamma_ivlD` is a genuine multi-conclusion `D` bundle (`shows "l <= Fin x" and "Fin x <= u"`) -- tagging would spawn both facts from every occurrence of its premise, the same exception `wf_compile_inputD(8)` gets; `ivl_exhaustE` already carries its own comment explaining it is deliberately cited explicitly rather than left to `auto`/`blast`'s uncontrolled case-splitting. Batch build green with the new attributes (no automation loop or broken proof anywhere downstream). `[rule_format]` checked: every occurrence repo-wide (`Exec_St` x2, `Interval_Warrowing` x1, `Activation_Context` x2) is an inline use-site citation (`fact[rule_format, of ...]` instantiating an already-proved quantified fact at one call site), not a lemma *declared* with `[rule_format]` in place of proper `fixes`/`assumes`/`shows` -- the actual anti-pattern the style rule bans. No lemma anywhere is declared that way. "Remove the four" was based on a shallow count that didn't distinguish the two shapes; there is nothing here to remove without breaking the proof that cites it. The `Exec_DG_*` heading-placement item is landed: `Exec_DG_Generator`, `Exec_DG_Refines`, and `Exec_DG_Trees` (the only three survivors -- `Exec_DG_Bridge` is deleted, so "four" is now three) each had their `section`/orientation `text` block sitting before the `theory ... imports ... begin` header instead of after `begin` like every other theory in the codebase; moved all three, batch build green. A repo-wide orientation-block survey across `src/Core`, `src/Solver`, `src/Domain`, `src/Exec` found only two real gaps out of 51 theories: `Exec_Placement.thy` had none at all (added one covering `scoped_location`, `scope_locations`, `effective_support`/`raw_support`/`resolved_default`, and the lax/strict `project_resolved_on` pair -- the support algebra the executable D/G transport's owner-aware readback builds on); `Exec_St.thy` had a good orientation block, but a stray lemma (`normalized_lift_sup_over_origins`, bridging `Voblint_Domain.Reachability_Lift`'s `normalized_lift` with the vendored `sup_over_origins`) sat before it. That lemma turned out to have zero citations anywhere in the repo and no automation attribute, so it was dead, not merely misplaced -- deleted rather than relocated. Batch build green. Step 3.5 fully closed |
| 3.6 | Strip project-history references from theory text (`#77`, `#121`, "the wider carrier migration"); fix the duplicated subsection heading at `DG_Soundness` 1870/1872. | landed: repo-wide sweep found nine issue-number citations across eight files (`Example_Random_Sign_Showcase`, `Example_Keyed_Solver_Update_Rule_Regression`, `Analyse_Dispatch`, `Sign_Checks`, `Call_String_Context_Finite`, `Voblint` x4, `Interval_Checks`, `Int_Checks`) plus two bare "the issue"/"tracking issue" references not matching the `#NN` pattern (`Call_String_Context_Finite`, `Placement_Policy`, the latter also grammatically broken); all rewritten to state the content inline instead of citing a tracker number. The literal phrase "the wider carrier migration" no longer exists anywhere (already fixed by earlier work). The `DG_Soundness` 1870/1872 duplicate heading is gone too -- a `subsection` listing shows no duplicates; whatever the plan saw there was resolved by an intervening edit before this pass |
| 3.7 | Run the playbook's style script; update the compliance table in `SESSION_CLEANUP_PLAYBOOK.md`. | open |

## Decisions and corrections

Record here, dated, anything the build or a proof contradicted, and any
step deliberately changed. Keep the original step text in the table above
and mark it `superseded (see below)`.

- 2026-08-30: plan written from the survey. No step executed yet.
- 2026-08-30: `Exec_St` cannot sit in `Voblint_Domain` yet: it uses
  `enter_frame_D`, `enter_D` and `combine_env_abs` from `Constraint_System`
  (20, 4 and 9 mentions). Those abstract-state call-boundary operations
  are Domain-level in nature, but their soundness lemmas cite the concrete
  `call_enter`/`combine_collect` from `Voblint_CFG`, so separating them is
  proof work, not a move. Until Phase 2 does it, `Exec_St` and
  `Exec_Refinement` live in `Voblint_Exec`, and `Voblint_Domain` holds only
  `Abstract_Domain`, `Abstract_Numeric_Queries`. Step 1.2 is
  deferred to the same point.
- 2026-08-30: `DG_Coverage` imports `Exec_DG_Generator`, so it is in
  `Voblint_Exec`, not `Voblint_Core` (the target table said Core).
- 2026-08-30: `Checks` and `Call_String_Context` reached `pp` only through
  `Abstract_Domain`'s `CFG_Def` import; both now import `Voblint_CFG.CFG_Def`
  themselves. `Strategy_Tree_Relabel` mentions `pp` in prose only.
- 2026-08-30: Steps 1.1 (`Backward_Domain` split) and 1.3 (hooks route to
  Examples) are content surgery on theories that I/Q must see in their new
  session, so they follow the first green build of the moved tree rather
  than precede it. `Exec_Placement` itself moved to `Examples/Placement/`.
- 2026-08-30: **`Exec_Placement` is not example-only.** The survey measured
  it only against `DG_Framework` (zero names) and counted three Example
  importers; but `Exec_DG_Refines`, `Exec_DG_Trees` and `Exec_DG_Generator`
  reached it transitively and use `scoped_location`, `effective_support`,
  `resolved_default` and the projection algebra (28, 20 and 20 mentions).
  It is the support algebra of the executable transport and lives in
  `Voblint_Exec`, imported explicitly by `Exec_DG_Refines`. Step 1.3 shrinks
  to the hooks route alone. Lesson for the playbook: measure an edge
  against every theory that *reaches* the import, not only the one that
  writes it.
- 2026-08-30: `Routed_Context` cited `Voblint_Compile.VIMP_Proc_to_CFG` and
  `compile_prog` in two checked antiquotations inside prose; they are
  unchecked `\<open>...\<close>` now. Core is compiler-free in fact, not only
  in its import list.
- 2026-08-30: The hooks route is not example-only either: `sound_dg_spec`
  is proved by reduction to `sound_dg_hooks` (`sublocale sound_dg_spec
  \<subseteq> hooks`, DG_Soundness), so the locale stays in Core. What was
  placement-only is the `*_placed` specification, `gamma_join` with its
  policy section, and the `sound_dg_hooks_ltr` re-packaging whose
  `hooks_ltr.` sublocale nothing cited. Those are `Placement_Policy.thy` in
  Examples now; `DG_Soundness` is 2182 lines, `DG_LTR_Sound` 68.
- 2026-08-30: **Spike 2.1 succeeds.** `Spike_Sign_Quotient.thy` proves a
  generic pullback inside `routed_dg_domain_exec` -- `sound_dg_spec` at the
  abstract Base spec gives `sound_dg_spec` at the executable Base spec with
  `gamma_exec d g = gamma_dg_base (readback d) (readback g)`, from the three
  commute facts alone -- and then interprets `sound_dg_spec`,
  `dg_ctx_activation_base` and `unit_routed_context` at
  `sctx_spec gs is_bot_pred` with `sigma := snd (sctx_sol ...)`, the solver's
  own table. The post-solution of the unbuffered generator is the first half
  of `routed_domain_exec.pp_abs` (`part_post_solution_seed_dg_buffered_to_old`
  plus the `routed_cmb_g_contribution_*` facts); the second half, the
  transport, is not needed. Nothing in `Exec_DG_Trees`, `Exec_DG_Generator`
  or `Exec_DG_Bridge` is cited. Phase 2 proceeds.
- 2026-08-30: The two generic halves of the spike are now framework facts:
  `routed_dg_domain_exec.sound_dg_spec_st` with `gamma_exec` (DG_Base_Exec)
  and `routed_domain_exec.pp_st` (Routed_Domain_Exec, factored out of
  `pp_abs`, which now cites it). An instance migrating to the executable
  carrier interprets `sound_dg_spec` by `sound_dg_spec_st`, feeds
  `dg_ctx_activation_base` the solver's table with `pp_st`, and needs nothing
  from `Exec_DG_Trees`/`Generator`/`Bridge`. The spike is 123 lines and is
  the template for step 2.6.
- 2026-08-30: `dg_analysis_adapter` is carrier-generic (step 2.5, done
  before 2.3/2.4 because it is what every migrated instance publishes
  through): it extends `routed_context_base_hetero` with a readback
  `rd :: 'D => 'a abs_state lifted` and the one assumption
  `gammaDG d g = gamma_state_lift (rd d)`; `analyse_result` reads the table
  through `rd`. The four existing interpretations (Sign, Parity, Interval and
  Int at `unit` context) pass `gamma_dg_base`, `gamma_state_lift` and `id`;
  the CLI entry theories that apply `dg_analysis_adapter.analyse_result`
  positionally gained the `id` argument. `routed_context_hetero` itself is
  untouched so far; step 2.4 removes it once no instance interprets it.
- 2026-08-30: Sign at unit context is the first instance on the executable
  carrier. `Sign_Ctx_None_Sound` defines `sctx_gamma gs d g =
  gamma_state_lift (readback d)` and the covered reader `sctx_sg_st`, proves
  `sctx_sound_exec` by `sound_dg_spec_st` and `sctx_pp_routed` by `pp_st`,
  and interprets `unit_routed_context` at `sctx_spec` with
  `sigma := snd (sctx_sol ...)`. `Sign_Checks` interprets the adapter with
  `rd := map_lift (fun_of_resolved_st_q_for gs)`; `sctx_analyse_result_eq`
  is now a one-line case split. `sctx_sigma_abs`, `sctx_sg`, `sctx_pp_abs`
  and `sign_pp_abs_gen` are gone, and the spike theory is deleted because
  the instance is its content. Recipe per remaining instance: replace the
  `*_sigma_abs`/`*_sg` section with `*_gamma`/`*_sg_st`, replace `*_pp_abs`
  with `*_pp_routed`, re-interpret `sound_dg_spec` and the routed locale at
  the executable spec, and hand the adapter `rd := map_lift readback`.
- 2026-08-30: Parity, Interval and Int at unit context follow the recipe
  unchanged. Interval and Int keep their solver-generic `ictx_solved`
  locale; `pp_routed` and `sg_st` live in the locale, the four update-rule
  `global_interpretation`s lose their `sigma_abs`/`sg` `defines`, and the
  `*_Entry` theories read `snd (ictx_sol_* ...)` directly. Int's hand-rolled
  `ictx_activation_collect_sound`, `ictx_sg_seed`, `ictx_sg_comb` and
  `ictx_locals_ge_s0d` are deleted; the theorem name survives as a
  re-export of the adapter's `activation_collect_dg_sound`, which is the
  same statement at the executable carrier. Int's per-mode
  `ictx_abs_spec_sound` moves above the `int_unit` context so
  `ictx_sound_exec` can pull it back along the readback.
- 2026-08-30: the contextual instances follow the recipe once the two policy
  locales are stated at a carrier parameter. `entry_state_routed_context`
  additionally takes its route as a parameter (`formals_route_lifted_gen S`
  on the abstract carrier, a domain's own quotient route such as
  `sctx_entry_route_gen gs is_bot_pred` on the executable one); its generic
  discharge of `resolve_sound`, `route_enterc_agree` and
  `call_enter_store_agree` does not depend on the carrier. Each entry-state
  instance now interprets `dg_analysis_adapter` at the executable spec with
  `enterc := route_enterc_of_sigma spec route (snd sol) Global g` and gets its
  `*_activation_collect_sound` as a re-export of the adapter's
  `activation_collect_dg_sound`; the `wf_compile_input` premise Interval's
  version carried was never used and is dropped, so the examples discharge six
  hypotheses instead of seven. The two Interval entry-state examples prove
  their routed-callee-entry facts by `eval` on the executable route instead of
  by the abstract-route commute lemmas. The call-string instances have no
  soundness section; for them the recipe is only `*_pp_abs` -> `*_pp_routed`.
- 2026-08-30: `locals_ge_s0d` and `activation_collect_dg_sound` move from
  `dg_analysis_adapter` into `routed_context_base_hetero`. Both use only the
  routed locale's own facts (`pp_eq_bound`, `pp_entry_s0g_bound`,
  `gammaDG_mono`, `sg_cov`, `dg_ctx_act_edge`, the CALL/COMB theorems), so the
  adapter's classifier was never a premise; a routed instance without a check
  layer -- the four CallString examples -- now gets its activation-indexed
  soundness theorem from the interpretation alone. `Routed_Context` imports
  `Activation_Backbone` for `activation_collect_sound_gen`; the two policy
  locales re-export the fact as `activation_collect_sound`.
- 2026-08-30: the four CallString examples solve the unbuffered
  `side_cfg_T_eff_keyed_seed_dg` at the executable spec already, so their
  migration is only the interpretation: `sound_dg_spec` at `*_S_st` via
  `routed_dg_domain_exec.sound_dg_spec_st`, `sigma := snd *_sol`, the covered
  reader typed at the executable carrier, and the hand-rolled
  `dg_reader_commute_gen`/`part_post_solution_seed_dg_st_to_abs_lifted_for`
  transport deleted. The examples were the last interpreters of
  `dg_reader_commute_gen` outside `Voblint_Exec`.
- 2026-08-30: `routed_context_hetero` and `unit_routed_context_hetero` are
  deleted. After the policy locales moved to `routed_context_base_hetero`
  nothing interpreted them; their only remaining mentions were prose, now
  pointed at the base locale. Step 2.4 is closed.
- 2026-08-30: what still keeps the transport theories alive is the flat
  (unrouted, `dg_gen_of`) executable bundle in `Run_Analysis_Sound` and its
  two registration locales, interpreted by four flagship examples. Step 2.3
  either restates those bundles at the executable carrier the same way
  (`sound_dg_spec_st` for the flat spec, the collecting endpoint fed by the
  solver's own table) or retires the flat registration API in favour of the
  routed adapter; decide there, not here.
- 2026-08-30 (superseded by the entry above): the six contextual instances cannot follow the recipe yet.
  `entry_state_routed_context` and `call_string_routed_context` are stated
  over `'a abs_state lifted` with `gamma_dg_base`/`gamma_state_lift` baked
  in and sublocale `routed_context_hetero`; step 2.4 generalizes both to
  `routed_context_base_hetero` at a carrier parameter first. Their Examples
  consumers (`Example_Sign_DG_EntryState_Result_Regression`,
  `Example_Interval_DG_EntryState_Collect`, `Example_Interval_Source_Ctx`,
  `Example_Interval_DG_Ctx_Collect`, the four CallString examples) cite the
  `*_sigma_abs`/`*_sg` names and move with them.
- 2026-08-30: Core's layout inside `src/Core/` is `Equations/`, `DG/`,
  `Context/`, `Result/`; Domain, Solver and Exec are flat. Phase 0 steps
  0.1--0.6 and Phase 1 steps 1.4--1.7 are landed (I/Q-clean per theory for
  Phase 0, `isabelle build -n` clean for the session structure); the batch
  build is the gate.
- 2026-08-31: `Abstract_Domain` now contains only abstract-value capabilities
  and their concretization laws. `Reachability_Lift` owns the generic dead-code
  carrier and its solver updates; `Nonrelational_State` owns pointwise stores,
  product concretization and witness-bottom tests. `Nonrelational_Reachability`
  owns the facts that compose those independent constructions. `combine_env`
  is the sole pointwise selector; `State_Restriction`, frame entry, and executable
  projections specialize it. The redundant `Split_State` representation and its
  unused D/G conversions were removed. The old state-normalization,
  finite-fold, D/G reconstruction and printing clusters had no live consumer
  and were removed. Domain printing reuses `VIMP_Source_Print.string_of_int`.
  The Domain-session attribute audit added only rules with narrow conclusion
  heads and removed redundant `bfilter.simps` registrations; all six theories
  are I/Q-clean with no warnings.
- 2026-08-31: the flat bundle restatement from the entry above is done.
  `Run_Analysis_Sound`'s `base_dg_exec_analysis` (Sign, Parity) now proves
  soundness via `routed_dg_domain_exec.sound_dg_spec_st` directly at the
  executable carrier, with G narrowed to match D (the only shape either
  instance actually used). `unit_dg_exec_analysis` (both Interval flagships)
  gets the same treatment via a new, file-local `sound_dg_spec_st` built from
  the existing `unit_dg_Hstep_for`/`unit_dg_Henter_for`/`unit_dg_Hcomb_for`/
  `unit_dg_Hcont_for` commute lemmas -- no shared locale needed, since this
  spec shape has exactly one consumer. Neither locale transports a solved
  system to the abstract carrier any more. `Run_Analysis_Sound` no longer
  imports `Exec_DG_Bridge`. `Interval_Ctx_Entry_State_Sound`'s own dead
  hand-rolled transport lemmas (`ivl_Hstep_lifted_for`/etc.,
  `dg_reader_commute_gen_ivl_lifted`) were deleted too, duplicating exactly
  what `routed_dg_domain_exec` already gives; its `ectx_abs_spec`/
  `entry_state_route_abs_gen` stay, being the genuine abstract-carrier route
  witness `routed_context_base_hetero` structurally requires.
- 2026-08-31: **step 2.3 is not safely executable yet**, despite the above
  closing both items the plan named as gating it. A repo-wide sweep found
  ~19 files with a directly-imported, apparently-dead `Exec_DG_Bridge`; 14
  were genuinely dead and had the import dropped (the four `*_Ctx_None_Sound`
  theories, `Interval_Exec_Sound`, `Int_Exec_Sound`, both Interval flagships,
  the Parity flagship, `Exec_Sign_DG_Run`, `Example_Interval_Global_Flow_Sensitivity`,
  `Example_Int_Refinement_Mode_Regression`, `Exec_Int_DG_Run`, `Voblint.thy`).
  Three findings block the theory-level deletions the step names:
  - `Routed_Domain_Exec` is load-bearing, not deletable: `routed_domain_exec`
    (extending `routed_dg_domain_exec` with the routing/seed-key parameters)
    is actively interpreted by `Sign_Ctx_None_Sound`, `Interval_Ctx_None_Sound`,
    `Int_Ctx_None_Sound`, and `Interval_Ctx_Entry_State_Sound` for
    `.pp_st`/`.sound_dg_spec_st`. This was already known generically ("the
    owner-aware trees ... keep routed_dg_domain_exec") but the step's own
    text still lists the whole theory for deletion; it should not be.
  - `dg_gen_of` -- the core "build an equation system from a spec" function
    every registration locale calls, including the ones just migrated above
    -- is defined in `Exec_DG_Generator.thy`, one of the three theories named
    for outright deletion. `Example_Relational_DG_Demo` and
    `Example_Sign_DG_Custom_Combine` need it directly (plus `exec_dg_st`,
    `unit_combine_step_st_env`) and had their import narrowed to
    `Exec_DG_Generator` alone rather than dropped.
  - The Placement examples (`Example_Sign_Placement`, `Example_Interval_Placement`,
    and `Monovariant_Analysis_Result` itself) are genuine, heavy consumers of
    the owner-aware tree machinery (`placed_abs_dg_edge_of`/`_enter_of`/
    `_combine_of`, `scoped_location`, `traverse_rhs_placed_abs_dg_edge_of`,
    ...) -- removing their import broke 24-76 commands each. These were
    never migrated off the transport route the way the flagship examples
    were; step 1.3's hooks-route move to `Examples/Placement/` did not
    include this. Deleting `Exec_DG_Trees`/`Exec_DG_Refines`'s owner-aware
    half, as the step's last clause names, needs these three migrated first
    -- a separate, real proof-engineering task, not a mechanical import
    cleanup, closer in size to today's flagship migration than to the import
    sweep above.
  Net: `Exec_DG_Trees`, `Exec_DG_Generator`, `Exec_DG_Bridge`, and
  `Routed_Domain_Exec` all stay for now. The step's own three-way split
  (transport theories / `DG_Base_Exec`'s transport half / `Exec_DG_Refines`'s
  owner-aware half) is right in shape; what changed is that `Routed_Domain_Exec`
  isn't part of what's being deleted, and the Placement examples are a
  precondition, not a side effect, of the `Exec_DG_Refines`/`Exec_DG_Trees`
  half landing.
- 2026-08-31: the precondition above is closed, and `Exec_DG_Bridge.thy` is
  deleted. Its three named consumers were re-checked against what they
  actually cite, not what the entry above assumed: none of
  `Example_Sign_Placement`, `Example_Interval_Placement`, or
  `Monovariant_Analysis_Result` cites a name `Exec_DG_Bridge.thy` itself
  defines (`dg_tree_st_commute_for`, `part_post_solution_dg_st_to_abs_for`,
  and siblings) -- every `placed_*`/`traverse_rhs_*`/`scoped_location` name
  the earlier 76-error count turned up lives in `Exec_DG_Trees.thy` or
  `Exec_Placement.thy`, both kept. The prior finding conflated "breaks if the
  import is deleted outright" with "needs Bridge specifically"; the fix in
  both cases was narrowing the import to `Exec_DG_Generator`, the same
  mechanical move already used for `Example_Relational_DG_Demo` and
  `Example_Sign_DG_Custom_Combine`, not a migration. `DG_Base_Exec.thy`'s own
  `imports ... Exec_DG_Bridge` was the same class of dead import (zero uses
  of Bridge's own content) and was the reason `Example_Interval_DG_IP_Flagship`
  still type-checked with a leftover pre-migration `twice_pp_abs`/
  `twice_collect_sound` pair reaching `part_post_solution_dg_st_to_abs_for`
  transitively; both are dead (superseded by the `twice_ex_reg`-registered
  route `twice_source_run_sound` already uses) and are deleted along with
  the stray citation. With every consumer narrowed to `Exec_DG_Generator`,
  `Exec_DG_Bridge.thy` had zero remaining importers repo-wide and is removed
  from `src/Exec/ROOT` and disk; `src/CLI/Analyse_Dispatch.thy`'s
  `code_module Exec_DG_Bridge` remap entry, and the stale `@{theory
  Voblint_Exec.Exec_DG_Bridge}` references in `Run_Analysis_Sound.thy` and
  `Voblint.thy`, are updated to match. `Exec_DG_Trees`, `Exec_DG_Generator`,
  and `Routed_Domain_Exec` remain load-bearing and are not part of this
  deletion.
- 2026-09-01: the batch build the deletion above claimed as verification
  caught what the interactive sweep missed: `Routed_Domain_Exec.thy`'s
  `pp_abs` theorem cited `part_post_solution_seed_dg_st_to_abs_lifted_for`
  directly, a name `Exec_DG_Bridge.thy` itself defined, not merely something
  reachable through its import. `pp_abs` is the same dead
  executable-to-abstract transport shape as `twice_pp_abs` above -- zero
  external consumers (`rg` for `\bpp_abs\b` outside its own file finds
  none) -- and is deleted; `pp_st`, the theorem right above it in the same
  file, stays: `sign_pp_st_gen`/`ivl_pp_st_gen`/`int_pp_st_gen`/
  `parity_pp_st_gen` all cite it. `src/Exec/README.md`'s `Routed_Domain_Exec`
  row is corrected to match. This is the load-bearing reminder for next
  time: an import-narrowing sweep only proves a file doesn't need Bridge's
  *import*; a direct citation of one of Bridge's twelve own names inside a
  file that imports something else entirely (here, `DG_Base_Exec`) still
  needs checking name-by-name before the file it names is deleted.
- 2026-09-01 (superseded by the merge/split entry below): scoped what step
  2.3's last blocker -- migrating
  `Example_Sign_Placement`, `Example_Interval_Placement`, and
  `Monovariant_Analysis_Result` off the owner-aware transport -- actually
  requires, before attempting it. Both Placement examples are not ad hoc:
  their top-level readback already goes through one generic lemma
  (`dg_refines_on_completed_sigma_abs`, citing `completed_sigma_abs`), and
  their per-node work already cites the generic owner-aware commute lemmas
  `Exec_DG_Trees` provides (`dg_refines_on_placed_edge_strict` and its
  enter/combine counterparts, per the file's own comments). What the
  flagship migration doesn't hand them for free is the *policy* itself: the
  flagships interpret `sound_dg_spec` and get `routed_dg_domain_exec`'s
  generic `sound_dg_spec_st` pullback; the Placement examples interpret
  `sound_dg_hooks` with a custom `keep_local`/`publish_side` split threaded
  through `placed_abs_dg_gen_of`, and no spike has proved the analogous
  pullback for that generator. That pullback is exactly what step 3.1
  ("One `dead_code_lift` ... `sound_dg_spec S ==> sound_dg_spec
  (dead_code_lift S)`, design the seam so widening delay and context gas
  can use it") would need to produce as a byproduct of making the placement
  policy an instance of the general spec shape -- 3.1 is a precondition
  for finishing 2.3's owner-aware half, not independent Phase 3 polish.
  Until 3.1 lands, this is genuine proof design (a new pullback lemma, or a
  new generic spec shape), not a mechanical port; it does not belong in an
  unsupervised pass. 2.3 stays partly landed; work continues on Phase 3
  items that are actually mechanical.
- 2026-09-01, merge/split research (supersedes the entry above): a deeper
  read found the entry above wrong on both counts.
  (1) The placement policy is *already* an instance of the general spec
  shape: `Placement_Policy.thy` defines `unit_dg_spec_placed` as a genuine
  `dg_spec` record and proves `sound_dg_spec_unit_placed` -- the
  abstract-carrier soundness the entry above thought was missing. (2)
  `dead_code_lift` is therefore not a precondition for 2.3; the actual gap
  is only the *executable mirror* of that record and its pullback, and the
  established recipe for exactly that already exists twice
  (`routed_dg_domain_exec` for the lifted Base shape,
  `unit_dg_exec_analysis`'s `Hstep`/`Henter`/`Hcomb`/`Hcont` derivation for
  the unit shape). Moreover `unit_dg_spec_for` and `unit_dg_spec_placed`
  turn out to be two instances of one merge/split skeleton
  (`restrict_global_for gs = project_component gs`,
  `restrict_local_for gs = project_component (\<lambda>n. \<not> gs n)`), so
  the right move is to generalize that skeleton and its pullback once and
  instantiate it twice, rather than mirror the derivation a third time.
  The full design -- the exact locale shape, the combine-case wrinkle, the
  executable projection's defaults problem and its `Exec_Placement.thy`
  resolution, the covering argument for both examples at the vname level,
  the deletion inventory, and the G1-G6 execution sequence -- is
  `docs/MERGE_SPLIT_GENERALIZATION.md`. Step 3.1 shrinks to the orthogonal
  Bot-carrier wrapper and is no longer on 2.3's critical path.
- 2026-09-01: `Solver_Mono` absorbed into `Strategy_Tree_Monad`, as the
  target layout table already named (`Voblint_Solver` row). Its
  `threefold_mono` bundle and three `D`-lemmas had zero citations anywhere
  outside their own file -- the three obligations it bundled are discharged
  directly, unbundled, by `DG_Keyed_Generator`'s three `*_gen` lemmas -- and
  are deleted. `fun_upd_sup_mono` is genuinely load-bearing (one citation,
  in `DG_Keyed_Generator`'s `mono_sides` proof) but mentions no strategy-tree
  concept, so it moved to sit next to that one call site rather than into
  `Strategy_Tree_Monad`. Its `hide_const (open) \<sigma>` guard against
  `TD.TD_side`'s own record field moved with it, onto `DG_Keyed_Generator`'s
  own `"TD.TD_side"` import (the file's `@{const TD_side_mono}` antiquotation
  is what actually needs that theory; `DG_Framework` no longer imports
  `Solver_Mono` and does not need it transitively).
- 2026-09-01: `map_ltree`/`map_gtree` (`Strategy_Tree_Relabel`) renamed to
  `relabel_ltree`/`relabel_gtree` to match the theory's own name and stop
  reading as a value-level `fmap`; their characterization lemmas renamed to
  match (`traverse_rhs_relabel_ltree`, `dep_aux_relabel_gtree`, etc.).
  Tagging the observer-characterization lemmas (`traverse_rhs_relabel_*`,
  `dep_aux_relabel_*`, `sides_of_rhs_fold_rhs_trees_char`, and siblings)
  `[simp]` was tried and reverted: it broke two proofs each in `DG_Soundness`
  and `DG_Keyed_Generator` that build specific normal forms by explicit
  `simp add:` citation, which a wider default simp set changes out from
  under them. Left untagged; a future attempt should budget for repairing
  those call sites rather than treating the tag as safe by inspection.
- 2026-09-01: `dg_combine_tree_at` landed in `DG_Framework` (definition plus
  `traverse_dg_combine_tree_at`, `sides_dg_combine_tree_at`,
  `sides_dg_combine_tree_at_other`, `dep_aux_dg_combine_tree_at`, and the
  bridge lemma `dg_combine_tree_as_at` connecting it back to the bare
  `dg_combine_tree`/`relabel_gtree` form), mirroring `dg_edge_tree_at`'s
  existing shape: `dg_edge_tree step u = dg_edge_tree_at step (Inl u) ()`
  (`DG_Framework.thy:305`). This is a pure addition -- nothing else in the
  session references it yet -- verified clean (0 errors) against both
  `DG_Soundness` and `DG_Keyed_Generator`.
  Migrating the actual consumers off `relabel_ltree`/`relabel_gtree` remains
  open and did not start this session; the scope is larger than first
  estimated. `dg_cmb_at` (`DG_Soundness`) and `dg_cmb_at_of`/`dg_extra_of`'s
  inner call (`Exec_DG_Generator`) still build the keyed address by
  relabeling the bare tree, and a citation trace found the real consumer
  chain to migrate alongside them is not just those two definitions but the
  soundness lemma family built on top: `dg_edge_tree_local`,
  `dg_edge_tree_global`, `dg_combine_tree_local`, `dg_combine_tree_global`,
  `dg_enter_tree_local`, `dg_enter_tree_global`, `edge_tree_mem`, and the
  `dg_edge_tree_hook`/`dg_combine_tree_hook` wrappers in `DG_Soundness`
  (35 matches for that name family in one file) -- proof-rewriting work, not
  a mechanical swap. Two related bridge lemmas in `DG_Keyed_Generator`
  (`apply_dg_spec_relabel_as_at`, `apply_dg_spec_contribution_relabel_as_at`)
  were checked for disposition: the first is genuinely cited twice in
  `DG_Soundness` (lines 608, 1683) and stays; the second has zero citations
  anywhere outside its own definition and is itself dead code, independent
  of this migration.
  Next steps, in order: add `dg_spec_combine_tree_at` to
  `DG_Keyed_Generator` (mirrors `apply_dg_spec_at`, `DG_Keyed_Generator.thy:179`,
  over the new `dg_combine_tree_at`); migrate `dg_cmb_at`/`dg_enter` to build
  on the `_at` forms directly; re-derive the `DG_Soundness` consumer family
  against that; migrate `Exec_DG_Generator`'s `dg_cmb_at_of`/`dg_extra_of`;
  re-verify `Exec_DG_Trees`/`DG_Coverage`; delete
  `apply_dg_spec_contribution_relabel_as_at`; then check whether
  `relabel_ltree`/`relabel_gtree` (`Strategy_Tree_Relabel`) are fully dead.
- 2026-09-01: the combine-tree/enter half of the `_at` migration landed.
  `dg_spec_combine_tree_at` added to `DG_Keyed_Generator` (mirrors
  `apply_dg_spec_at` over the new `dg_combine_tree_at`, plus a bridge lemma
  `dg_spec_combine_tree_as_at` and, for symmetry with the edge former's own
  bridge, `dg_spec_combine_tree_relabel_as_at`). Four call sites migrated off
  `relabel_ltree`/`relabel_gtree` onto direct `_at` addressing, each a
  statement-preserving change to a named definition's body (`dg_cmb_at`,
  `dg_enter` in `DG_Soundness`; `dg_cmb_at_of`, `dg_extra_of` in
  `Exec_DG_Generator`), so no downstream lemma *statement* changed --- only
  proofs that unfolded the old relabel-based body, all re-derived directly
  from `traverse_dg_combine_tree_at`/`sides_dg_combine_tree_at`/
  `traverse_dg_edge_tree_at`/`sides_dg_edge_tree_at` instead of
  `traverse_intra_keyed`/`sides_relabel_gtree_unit_gen`/`sum.map_comp`.
  Touched: `dg_combine_tree_local`, `dg_combine_tree_global`,
  `dg_enter_tree_local`, `dg_enter_tree_global` (`DG_Soundness`);
  `dep_aux_dg_cmb_at_of`, `dep_dg_gen_of_entry` (`DG_Coverage`). Three
  characterization lemmas that only existed to support the old relabel-based
  proofs (`dep_aux_dg_combine_tree`, `dep_aux_dg_spec_combine_tree`,
  `dep_aux_dg_edge_tree_relabelled`, all in `DG_Coverage`) went dead as a
  result and were deleted, verified by citation trace across every `.thy`
  file. `Run_Analysis_Sound`'s `dg_cmb_at_of_eq_for`/`dg_extra_of_eq_for`
  (bridging Exec's generator to Core's) needed no change: both sides now
  unfold to literally the same `_at` term. Full batch build green after this
  step (`Voblint_Codegen` finished, exit 0).
  What is left before `relabel_ltree`/`relabel_gtree` can be deleted: unlike
  `dg_cmb_at`/`dg_enter`, `dg_edge_tree_local`/`dg_edge_tree_global` in
  `DG_Soundness` have the relabel expression baked directly into their own
  *statement* (there is no intermediate named definition to swap the body
  of), so migrating them means restating both lemmas in terms of
  `apply_dg_spec_at` and updating every citer -- a materially larger,
  statement-level change. `edge_tree_mem` and one more site (~line 917,
  post-migration numbering) build the relabel expression inline for the same
  reason. `apply_dg_spec_contribution_relabel_as_at` (`DG_Keyed_Generator`,
  confirmed dead in the prior entry) is still there, pending deletion
  alongside this next step rather than on its own.
- 2026-09-01: `Exec_DG_Trees` deleted whole, and ~360 lines of dead commute
  lemmas removed from `Exec_DG_Generator` (1010 -> 650 lines). Both trace to
  one root: `Exec_DG_Bridge` (deleted earlier, "zero remaining importers" per
  the 2.3 entry above) was the sole consumer of a "_for"/"wrapped" diagonal-
  reader commute subsystem -- `sides_of_rhs_Inl_bot`, `sides_wrap_reduce`,
  every `*_commute_for` and `*_wrapped_*_commute` lemma, and the two dead
  `dg_tree_st_commute_wrapped_{edge,combine}` -- that nothing has cited since.
  `Exec_DG_Trees`'s entire content (four `traverse_*_commute_for`/
  `traverse_wrapped_*_commute_for` lemmas) was exactly that subsystem's
  traverse half; deleting it and repointing `Exec_DG_Generator`'s import
  straight at `Exec_DG_Refines` builds clean. The live commute engine
  (`dg_tree_st_commute_at_edge`, `seed_dg_list_commute`, and the generic
  `dg_reader_commute_gen` locale) never used the dead subsystem -- it commutes
  through `dg_edge_tree_at`-style addressing directly, which is also why the
  follow-up above expects `dg_combine_tree_at` to make
  `relabel_ltree`/`relabel_gtree` fully dead too. Verified by full citation
  trace across every non-`.thy~` file, not by attribute inspection: none of
  the deleted lemmas carried `[simp]`/`[intro]`/`[dest]`, so a zero-hit
  `rg -w` search is conclusive here (the general trap below, about grep
  missing simp-set uses, does not apply to unattributed lemmas). One
  near-miss: `dep_aux_dg_edge_tree`/`dep_aux_dg_combine_tree`/
  `dep_aux_relabel_gtree` in `Exec_DG_Generator` looked like the same kind of
  dead local restatement, but `dep_aux_dg_edge_tree` is genuinely relied on
  by `DG_Coverage` through name shadowing across the session boundary
  (`DG_Framework` in Core defines the same name; the Exec-local copy shadows
  it for anything importing through `Exec_DG_Generator`) -- deleting it would
  have been a real regression. `dep_aux_dg_combine_tree`/`dep_aux_relabel_gtree`
  were safe because `DG_Coverage` carries its own separate local copy of the
  former, and `Strategy_Tree_Relabel`'s copy of the latter remains reachable
  to absorb the shadow once the local one is gone.
- 2026-09-01: the statement-level half of the `_at` migration landed, closing
  the "what is left" note above. `dg_edge_tree_local`/`dg_edge_tree_global`
  (`DG_Soundness`) restated in terms of `apply_dg_spec_at` directly, `dep_aux`
  of `edge_tree_mem` likewise, and `dg_edge_tree_hook` (a named definition,
  like `dg_cmb_at`/`dg_enter`) had its body swapped the same way its two
  siblings' were. All five downstream citers (`edgeD`, `edgeG`,
  `dg_edge_tree_hook_local`, `dg_edge_tree_hook_global`, and
  `dg_trees_as_hook_shape`) needed no change beyond dropping
  `apply_dg_spec_relabel_as_at` from one `auto simp:` set -- once both sides
  of the equality being proved build via `apply_dg_spec_at`, the relabel
  bridge lemma has nothing left to bridge. That made all three relabel-bridge
  lemmas in `DG_Keyed_Generator` dead by the same citation-trace standard as
  above (`apply_dg_spec_relabel_as_at`, `apply_dg_spec_contribution_relabel_as_at`,
  and the newly-added `dg_spec_combine_tree_relabel_as_at`, which never
  ended up load-bearing anywhere), and `relabel_ltree`/`relabel_gtree`
  themselves went unreachable from every consumer in the tree.
  `Strategy_Tree_Relabel.thy` deleted whole; `DG_Framework`'s import of it
  dropped. Full batch build green (`Voblint_Codegen` finished, exit 0);
  committed as `4e9a30e5`. One process note: the first build attempt failed
  with "Cannot load theory Strategy_Tree_Relabel" from `DG_Framework` even
  though I/Q diagnostics had shown 0 errors for the import removal -- the
  edit was verified in the I/Q buffer but never actually saved to disk
  before the file was deleted, so batch (which reads disk) built the
  pre-edit import against a theory that no longer existed. `list_files`'s
  `is_modified` flag catches this class of mistake directly; check it before
  trusting a "0 errors" diagnostic as evidence a change reached disk.
- 2026-09-01: `Context_Refinement.thy` (`Voblint_Solver`), and its sole
  consumer `Call_String_Solver_Projection.thy` (`Voblint_Core`) and *its*
  sole consumer `Call_String_Solver_Refinement_Seeded.thy`
  (`Voblint_Examples`), deleted as one vertical slice on architectural
  grounds, not because anything in them was unreachable dead code -- all
  three built and proved cleanly right up to deletion. `seed_eqs` forces a
  post-solution to additionally dominate an externally supplied valuation by
  rewriting every equation's right-hand side to join a fixed seed into its
  answer; `call_string_projection_refinement`'s only real content is
  `post_solution_of_seeded` applied to a projected fine solution used purely
  as seed data, with no hypothesis relating the coarse system being seeded
  to whatever system that fine solution actually solves, and no `k1 <= k2`
  premise. That is a coarse/project/seeded-refine construction from an
  earlier design where context-sensitive equations were not built directly
  over their final contextual unknowns; it does not fit the direct-`_at`-
  addressing architecture this file's other entries establish, where a
  context-sensitive equation is constructed at its final address from the
  start and no second, seeded solve is needed. Citation-traced first: every
  name in both theories (`seed_sides`, `seed_eqs`, `post_solution_of_seeded`,
  `proj_local`, `proj_global`, `proj_P`, `proj_global_keys`, `proj_local_ge`,
  `proj_global_ge`, `proj_local_ge_refl`, `cs_route_project_ctx`,
  `project_seeded_eqs`, `call_string_projection_refinement`) had zero
  citers outside this three-file chain; `cs_route_project_ctx` had zero
  citers even inside its own file (its own comment records it as recorded
  for a `comb`-hook simulation argument that was never written). Neither
  `Context_Refinement` nor `Call_String_Solver_Projection` appeared in
  `Analyse_Dispatch`'s `code_identifier` block, so the deletion has no
  codegen surface at all. Updated: `Solver/ROOT`, `Core/ROOT`,
  `Examples/ROOT`, `Solver/README.md`, `Core/README.md`,
  `Examples/Interval/README.md`, `Voblint.thy` (theory list, the capstone
  bullet, and one comparison clause in a neighboring bullet that named the
  deleted theory), `Call_String_Solver_Regression.thy` (one prose sentence
  contrasting itself with the deleted theory's proof). Moved
  `CALLSTRING_PROJECT_SIGMA_GENERALIZATION_DESIGN.md` to `docs/history/`:
  its entire subject is now deleted.

- **2026-09-01, later same day** -- a four-agent architecture audit (Solver
  boundary, `_at` cleanup, Goblint manager comparison, Phase 2.7 Exec
  classification) converged on three independent commits, all batch-green:
  1. `dg_edge_tree`/`dg_combine_tree` (`DG_Framework.thy`) redefined as
     literal specializations of `dg_edge_tree_at`/`dg_combine_tree_at`
     (`dg_edge_tree step u == dg_edge_tree_at step (Inl u) ()`), with the
     "Edge formers over a solution address"/"Combine formers over a
     solution address" subsections reordered ahead of the bare forms so the
     specialization is definitional rather than bridged by a separate
     lemma. Every bare-form characterization lemma (`traverse_dg_edge_tree`,
     `sides_dg_edge_tree_Inl`/`_Inr`, `dep_aux_dg_edge_tree`, and the
     `dg_combine_tree` analogues, plus a new `dep_aux_dg_combine_tree` that
     did not exist before) is now a one-line corollary of its `_at`
     counterpart. Fixed the two proofs (`env_indep_deps_dg_edge_tree`,
     `env_indep_deps_dg_combine_tree`) that cited `dg_edge_tree_def`/
     `dg_combine_tree_def` directly rather than through a named
     characterization lemma, and deleted one dead duplicate
     (`Exec_DG_Generator.thy`'s own copy of `dep_aux_dg_edge_tree`, unused
     in its own file). No live consumer depended on the bare forms'
     definitional shape -- confirmed by full-codebase citation trace before
     touching anything.
  2. `Voblint_Solver` now owns the generic bridge from the vendored TD
     solver's executable termination check to `part_post_solution`:
     `TD_Solver_Menu.thy` moved wholesale from `Voblint_Exec` to
     `Voblint_Solver`, and `Solver_Side_RG.thy`'s `solve_dom_of_solve_c`
     (previously the only fact in that file cited by more than one
     external site -- 30+ citers across Analysis/Soundness/Examples/CLI)
     merged into it; `part_post_solution_of_solve_c`'s proof now cites
     `solve_dom_of_solve_c` instead of re-deriving the same `solve_dom x`
     fact inline. 19 files' imports retargeted from
     `"Voblint_Exec.TD_Solver_Menu"`/`"Voblint_Exec.Solver_Side_RG"` to
     `"Voblint_Solver.TD_Solver_Menu"`. `DG_Keyed_Generator.thy`'s own direct
     `"TD.TD_side"` import (for `TD_side_mono`) is unrelated to this move
     and was left alone -- Core reaching TD directly for that one locale
     predicate is a separate, smaller fact than the solve/`part_post_solution`
     boundary this commit centralizes. (Follow-up split, same day: the two
     generic `TD_side_upd_rule` lemmas -- `solve_dom_of_solve_c` and
     `part_post_solution_of_solve_c` -- moved out of `TD_Solver_Menu.thy` into
     a new `TD_Solver_Bridge.thy`, so `TD_Solver_Menu` is genuinely only the
     named menu of concrete update rules and `TD_Solver_Bridge` is the one
     place TD's own proof vocabulary -- `term_equivalence`, `solve_c_dom_def`,
     `partial_post_solution` -- stops leaking upward. `TD_Solver_Menu` now
     imports `TD_Solver_Bridge`; no other file needed a new import, since
     every existing `"Voblint_Solver.TD_Solver_Menu"` importer gets the bridge
     transitively.)
  3. Deleted `Solver_Side_RG.thy` entirely (689 lines, `git rm`, no
     replacement) after a citation trace stronger than name-grep: every
     head symbol (`side_rg`, `rg_val`, `rg_state`, `rg_sides`, `rg_ug`,
     `rg_both`, both `TD_side_always_join_solve_Inr_rg`/`_rg_ind` and
     their `..._warrowing_apinis_...` mirror halves) has zero occurrences
     anywhere else in `src/`, so no `[simp]`-tag could be firing implicitly
     either -- confirmed by checking the pattern, not just the lemma name.
     This refutes `EXPORT_SURFACE_AUDIT.md`'s earlier claim that the
     warrowing-apinis half "is live via `Interval_Warrowing.thy`": that
     file only *mentioned* `TD_side_warrowing_apinis_solve_Inr_rg` in a
     `text` comment explaining why two local lemmas existed, never cited
     it in a proof. Those two local lemmas (`ivl_widen_bot_bot`,
     `ivl_narrow_bot_bot`, `Interval_Warrowing.thy`) existed solely to
     satisfy that now-deleted fact's preconditions and were dead in exactly
     the same way once traced -- deleted alongside it. Also deleted 11
     dead lemmas from `Monovariant_Analysis_Result.thy` on the same
     evidence standard (`normalize_point_correct`,
     `normalize_point_Reachable_map_lift`, all four
     `normalize_point_canonicalize_lift_*`,
     `gamma_point_normalize_point_canonicalize_lift`,
     `lookup_context_monovariant_analysis_result_for`,
     `contexts_at_monovariant_analysis_result_for`, `length_dg_globals_for`,
     `map_fst_dg_globals_for`) -- `normalize_point` itself and its other
     consumers (`dg_globals_for`, `ctx_solved_for`,
     `monovariant_analysis_result_for`) stayed, still heavily cited.
     Updated the six files whose prose named a deleted lemma by number
     (`Interval_Checks.thy`, `Sign_Checks.thy`, `Int_Checks.thy`,
     `Sign_Ctx_None_Sound.thy`, `Interval_Ctx_None_Sound.thy`,
     `Interval_Ctx_Entry_State_Sound.thy`, `DG_Analysis_Adapter.thy`,
     `Reachability_Lift.thy`) to describe the fact inline instead of
     dangling a reference to a name that no longer exists -- one of these
     (`DG_Analysis_Adapter.thy`, in `Voblint_Core`) had cited
     `\<^theory>\<open>Voblint_Exec.Monovariant_Analysis_Result\<close>`, an actual layering
     violation caught by the batch build (Core does not, and must not,
     depend on Exec) rather than by the citation trace.
  This closes the `_at` half and the Solver-boundary half of
  `docs/HANDOFF.md`'s two open tracks; the manager question was re-audited
  against a fresh clone of the real `goblint/analyzer` source (not memory)
  and reconfirmed **A -- no manager needed**, with one honest new gap noted
  (Goblint's `man.split` has no Voblint equivalent, because no current VIMP
  transfer wants more than one resulting state outside `tf_branch`'s binary
  case). Phase 2.7 itself turned out narrower than its own wording: only
  `TD_Solver_Menu` and `solve_dom_of_solve_c` were genuinely misplaced-but-
  generic; `DG_Base_Exec.thy`/`routed_dg_domain_exec` and most of
  `Monovariant_Analysis_Result.thy` remain in `Voblint_Exec` because they
  are fundamentally about transporting between the concrete
  `resolved_st_q`/`exec_dg_st` carrier and the abstract framework carrier --
  `Voblint_Exec` does not dissolve from this round, and does not get closer
  to dissolving until the larger, already-deferred quotient-carrier
  restatement happens. `DG_Coverage.thy` (fully generic Core/DG content,
  stranded only by importing `Exec_DG_Generator` for `dg_gen_of`) and the
  12x-repeated `solve_c -> solve_dom -> part_post_solution` boilerplate
  across `Analysis/Instances/**/Ctx/*_Sound.thy` remain open, deliberately
  not touched this round -- the former needs a not-yet-done audit of
  `Exec_DG_Generator.thy` in full, the latter is real proof engineering
  (a new parametrized lemma/locale), not a move.

## Traps specific to Core

- `interpretation` sites downstream: the four `call_string_routed_context`
  interpretations spell the entry as `"STR ''main''"`; a grep for the
  parameter name misses them. Check arity at every interpretation of a
  locale whose header changes (playbook, parameter-deletion pass).
- `Exec_St`'s preamble defines classes before its `section`; moving the
  classes changes which theory the `instance lifted :: bounded_warrowing`
  belongs to, and `Solver_Side_RG`, `Exec_DG_Refines` and nine Analysis
  theories cite that instance implicitly through sort constraints.
- `gamma_join` and the hooks route are recorded in the alignment register as
  a kept alternative concretization target. Moving them to Examples keeps
  the register true; deleting them would not.
- `Rel_Order_Domain` interprets `sound_dg_spec` at a carrier that is not an
  `abs_state`. It is the existing witness that the framework is
  carrier-agnostic; if a Phase 2 change breaks it, the change narrowed the
  framework.
- The build abandons a session at its first failing theory. After each
  phase's first build, budget for the tail.
- A change in `Voblint_Core` rebuilds every session above it, which is longer
  than the ten minutes an agent harness allows one background command. If the
  command is killed mid-session, the finished sessions keep their heaps and a
  rerun resumes from the first unfinished one; only a build killed while
  writing a session database, or two builds at once, corrupts it. Start such
  a build early and let it run alone.
- Two interpretations in one context whose locale hierarchies share an
  instance at syntactically identical parameters register that instance's
  facts once, under the first qualifier. `Int_Ctx_None_Sound` interprets
  `unit_routed_context` and then `dg_analysis_adapter` at the same
  `routed_context_base_hetero` instance, so the hoisted
  `activation_collect_dg_sound` is `ictx_routed.routed.…`, not
  `ictx_adapter.…`; the entry-state instances escape this only because their
  adapter names `enterc` by a definition the routed locale spells out. I/Q
  does not re-check a dependent theory after an edit to its Core ancestor
  until that theory is touched; the batch build does.
- I/Q `write_file` with a line range uses the buffer's current numbering.
  After any earlier edit in the same file, re-read the target lines before
  the next range edit; a stale range silently replaces the wrong block
  (an off-by-two dropped a `lemmas` re-export in `Interval_Ctx_None_Sound`
  and surfaced two theories later as an undefined fact). Anchor on a unique
  string with `str_replace` wherever one exists.
