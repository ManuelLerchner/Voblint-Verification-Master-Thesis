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
| `Voblint_Domain` | `goblint.domain` | `Abstract_Domain` (classes, `lifted`), `Backward_Domain` (the `backward_domain` locales, today `Abstract_Domain` 919-2078), `Split_State`, `Abstract_Numeric_Queries`, `Abstract_State` (today `Exec_St`), `Exec_Refinement` | `Voblint_VIMP`, `TD` |
| `Voblint_Solver` | `goblint.constraint`, `goblint.solver` | `Strategy_Tree_Monad` (absorbing `Strategy_Tree_Do`, `Solver_Mono`), `Strategy_Tree_Rhs`, `Strategy_Tree_Relabel`, `Strategy_Tree_Combinators`, `Side_Buffering`, `Post_Solution` (new), `Context_Refinement` | `TD` only |
| `Voblint_Core` | `Analyses`, `Constraints`, `Control`, `AnalysisResult` | `CFG_Enumeration`, `Constraint_System` (absorbing `Constraint_System_Sound`), `State_Restriction`, `DG_Framework`, `DG_Soundness`, `DG_LTR_Sound`, `Activation_Local_Sound`, `Activation_Backbone`, `DG_Ctx_Activation`, `DG_Transfer_Combinators`, `Routed_Context`, `Routed_Context_Unit`, `DG_Base`, `Call_String_Context`, `Call_String_Collecting_Refinement`, `Call_String_Solver_Projection`, `Analysis_Result`, `Checks`, `Abstract_Checks`, `DG_Analysis_Adapter`, `DG_Coverage` | `Voblint_CFG`, `Voblint_Domain`, `Voblint_Solver` -- never `Voblint_Compile` |
| `Voblint_Exec` (quarantine) | none | `Exec_DG_Refines`, `Exec_DG_Trees`, `Exec_DG_Generator`, `Exec_DG_Bridge`, `DG_Base_Exec`, `Routed_Domain_Exec`, `Solver_Side_RG`, `Solver_Menu`, `Monovariant_Analysis_Result` | `Voblint_Core`, `Voblint_Compile` |
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
| 2.3 | Delete `Exec_DG_Trees`, `Exec_DG_Generator`, `Exec_DG_Bridge`; the transport half of `DG_Base_Exec` (keep `routed_dg_domain_exec` and the `base_dg_spec_st_for_lifted` commute lemmas it cites); `Routed_Domain_Exec`; the owner-aware trees and classifier-parametric readback in `Exec_DG_Refines` (keep the `exec_dg_st` lattice instances and `fun_of_dg_st_for`). | open |
| 2.4 | `routed_context_hetero` becomes `routed_context_base_hetero` at whichever carrier the instance chooses; delete the restated assumptions. Same for `unit_routed_context_hetero`. | landed: `entry_state_routed_context` and `call_string_routed_context` (Analysis) are stated at a carrier parameter with `gammaDG`/`gammaM` and sublocale `routed_context_base_hetero`; `routed_context_hetero` and `unit_routed_context_hetero` are deleted, having no interpreter left |
| 2.5 | `Analysis_Result` holds the quotient; `normalize_point` becomes the single readback at publication, in `DG_Analysis_Adapter`. `Abstract_Checks` reads the published table. | landed in the generic form: `dg_analysis_adapter` extends `routed_context_base_hetero` and takes a readback `rd` with `gammaDG d g = gamma_state_lift (rd d)`; the four abstract-carrier sites pass `rd = id` |
| 2.6 | Rewrite the twelve `*_Ctx_*_Sound` theories and the four CLI `*_Entry` theories to interpret at the quotient carrier. Expect the transport boilerplate that NEXT_STEPS records as the 23-suffix duplication to shrink. | in progress: the four unit-context instances (Sign, Parity, Interval, Int, with their `*_Checks`/`*_Entry` consumers), the three entry-state instances and the two call-string instances are on the executable carrier; the two Interval entry-state examples and `Example_Interval_Source_Ctx` follow the theory; the four CallString examples interpret `call_string_routed_context` at their executable spec and get their headline theorem from `activation_collect_sound`. Still on the transport, gating 2.3: `Run_Analysis_Sound`'s flat bundles (`dg_exec_run_source_sound_for`, `dg_exec_collect_sound_for`, their `_lifted` twins and the registration locales `unit_dg_exec_analysis`/`base_dg_exec_analysis`, interpreted by `Exec_Sign_DG_Run`, `Example_Parity_DG_Flagship`, `Example_Interval_DG_Flagship`, `Example_Interval_DG_IP_Flagship`), and the abstract-transport section of `Interval_Ctx_Entry_State_Sound` (`dg_reader_commute_gen_ivl_lifted`, `entry_state_route_abs_gen`, `ectx_abs_spec`) |
| 2.7 | Move `routed_dg_domain_exec`, `Solver_Side_RG`, `Solver_Menu`, `Monovariant_Analysis_Result`, `DG_Coverage` to their final homes (`DG_Base`, Solver, Core); retire `Voblint_Exec` from `ROOTS`. | open |

### Phase 3 -- inside the theories

| # | Step | Status |
| --- | --- | --- |
| 3.1 | One `dead_code_lift :: ('dl, 'dg) dg_spec => ('dl lifted, 'dg) dg_spec` with `sound_dg_spec S ==> sound_dg_spec (dead_code_lift S)`; `base_dg_spec_for_lifted`, `unit_step_for_lifted`, `unit_dg_spec_for_lifted` and `base_dg_spec_st_for_lifted` become instances. This is Goblint's `DeadCodeLifter`, stated once. Design the seam so widening delay and context gas can use it. | open |
| 3.2 | Split `DG_Framework`: the homogeneous unit analysis (685-956) and the keyed generators (1393-end) are separate concerns from the `dg_spec` record and edge trees. Split `Abstract_State` at the reachability lift (1763). | open |
| 3.3 | Retire `metis`: after Phase 2 the count is 26; `Abstract_State` holds 13. Retire the 61 `apply` lines; `Activation_Local_Sound`'s 10 and `Routed_Domain_Exec`'s 14 first. | open |
| 3.4 | Hoist `dg_post_solution_postfix` (272 lines) and `side_cfg_T_eff_keyed_seed_dg_buffered_correspondence` (249) into helper lemmas with named subgoals. | open |
| 3.5 | Tag the 31 untagged `...I`/`...E`/`...D` lemmas or rename them; remove the four `[rule_format]`; add orientation blocks where missing; move the `section` heading below the `theory` header in the four `Exec_DG_*` survivors, if any survive. | open |
| 3.6 | Strip project-history references from theory text (`#77`, `#121`, "the wider carrier migration"); fix the duplicated subsection heading at `DG_Soundness` 1870/1872. | open |
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
  `Abstract_Domain`, `Split_State`, `Abstract_Numeric_Queries`. Step 1.2 is
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
