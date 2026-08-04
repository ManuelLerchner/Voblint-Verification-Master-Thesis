# M4 placement-spine migration checklist

**Cancelled by architectural review.** This migration effort is not paused —
it is cancelled. After the Sign and Parity flagship migrations (`57d2b377`,
`31574413`) showed large size growth (158->997, 269->1336 lines) for a small
proven-generic benefit (issue #81, ~2-3% recovered), a from-scratch boundary
audit, `docs/reviews/M4_SPINE_BOUNDARY_AUDIT.md`, checked whether the classic
route still contains genuine duplicate proof stacks that would justify
continuing. **It does not.** Every classic constant this migration was meant
to retire is already architecture-neutral, a thin one-line definitional
specialization of the generic layer, or a bare compatibility name. No
classic example family depends on an independent-implementation duplicate.
The two completed migrations were correct and remain committed, but were, on
this evidence, unnecessary churn: both examples were already sound through
the same generic, classifier-parametric `sound_dg_spec` machinery every
other classic example uses.

**Decision: do not migrate any further example.** `sound_dg_hooks`/
`sound_dg_hooks_ltr` is a low-level framework-construction API, not the
everyday user-facing one — it requires a per-CFG-node hook-tree instance,
`dg_refines_on`, `se_constraint_holds`, and transport proof, which is exactly
why migrated examples ballooned 5-6x. `sound_dg_spec` is already the concise
user-facing adapter: one `sublocale`/`interpretation` line per instance,
three locale obligations proved once and discharged generically over the
whole CFG. Interval, Mixed, CallString, and Ctx examples stay on the classic
route. `sound_dg_spec`, `dg_spec`, and `dg_gen_of` are not being deleted.

The one remaining real finding is a framework-internal duplicate-proof-stack
risk between `sound_dg_spec` and `sound_dg_hooks` themselves (two
independently-proved locales over the same shape of per-step obligation) —
see `docs/reviews/M4_SPINE_BOUNDARY_AUDIT.md` Section 2/4 for the scoped
follow-up (making `sound_dg_spec` a `sublocale`/`interpretation` of
`sound_dg_hooks`, zero example changes). That is tracked separately from this
checklist; this file's own task list below is historical record of the
cancelled migration attempt, kept for reference, not an active plan.

Background and the two-spine situation: `docs/reviews/M4_ARCHITECTURE_PR_REVIEW.md`.
This file originally tracked the "migrate every classic-route D/G example
onto the placement spine, then retire the classic spine" instruction set,
which is the plan being cancelled here.

**Hard ordering rule (historical, no longer live)**: nothing gets deleted
(task 5) until every in-scope example below is migrated and green. Moot —
task 3 will not resume, so task 5 will not be attempted under this plan.

## Progress snapshot

- Task 1 (audit): **done**, this file is the output.
- Task 2 (classic-policy adapters): **assessed, not adding new ones yet** — see
  "Task 2 findings" below.
- Task 3 (migrate examples): **in progress, blocked on CallString/Ctx family
  specifically**. `Exec_Sign_DG_Run.thy` migrated and committed (`57d2b377`).
  Sign CallString K1/K2 investigated next per the task order and found
  **architecturally blocked**, not merely hard — see "CallString/Ctx family is
  blocked" under Unexpected findings. Proceeded to Parity instead:
  `Example_Parity_DG_Flagship.thy` migrated and committed (`31574413`), which
  required first adding a generic join-node (two-predecessor) transport
  lemma, `placed_hook_se_join_edge`, to `Exec_DG_Bridge.thy` (`121fd0e5`) —
  see "Join-node transport lemma" below. `Example_Sign_Placement.thy` was
  already on the new route before this task started, but as a *standalone
  parallel example*, not a migration of an existing classic Sign flagship (see
  "Sign" row below).
- Task 4 (residual audit): not reached.
- Task 5 (delete classic spine): not reached, and must not be attempted until
  task 3 is 100% complete.

## Scope note: three architectures, only one in scope

The repository has three independent proof architectures under
`src/Examples/` and `src/Analysis/Instances/`. Only the first is in scope for
this migration:

1. **D/G route** (classic `dg_spec`/`sound_dg_spec`/`unit_dg_spec`/`dg_gen_of`
   vs. new `hook_gen`/`sound_dg_hooks`/`placed_dg_gen_of_strict`) — **in scope**.
2. **TD side-effect route** (`effectful_domain_transfer`/`etf`/
   `cone_compatible_etf`, e.g. `Interval_Side_Soundness.thy`,
   `Sign_Side_Soundness.thy`, `Sign_Named_Global_Eff.thy`, the `Example_Side_*`
   examples, `Exec_Sign_Run.thy`/`Exec_Ivl_Run.thy`,
   `Example_Interval_Loop_Coverage.thy`, `Example_Proc_Call.thy`,
   `Example_Interval_Side_Proc_Global.thy`, `Example_Mixed_Flow_Sign.thy`) —
   **out of scope, do not touch**. Never touches `dg_spec` or `hook_gen`.
3. **Pure CFG/compile/print/tooling infrastructure** (no analysis-soundness
   claim at all) — **out of scope**.

The tables below mark route-2 and route-3 files `non-DG` / `n/a` so it is
explicit they were checked and excluded, not overlooked.

## Task 2 findings: classic-policy adapters

Checked whether thin `classic_hook_gen`/`classic_sound_dg_hooks`/
`classic_exec_dg_gen`-style wrappers are needed before migrating examples.

Already exist and are usable as-is:

- `unit_dg_spec tf = unit_dg_spec_for is_global tf`
  (`src/Core/Solver/Context/DG/DG_Framework.thy:585-592`) — the classic/`_for`
  bridge the PR review flagged as missing is already landed (commit
  `865cbe10`).
- `unit_dg_spec_for gs tf` and `unit_dg_spec_placed source_global keep_local
  publish_side tf` (`DG_Framework.thy:526-578`) — fully generic, `gs`/
  `keep_local`/`publish_side` are plain parameters.
- `classic_keep_local`, `classic_publish_side` :: `scoped_location => bool`
  (`src/Core/Domain/Exec_Placement.thy:17-23`) — the classic local/global split
  restated as a placement policy. `Split_State.thy`'s colliding, unused
  `_for`/`classic_*` duplicate that the PR review flagged was already deleted
  (commit `865cbe10`, "Split_State.thy's dead layer removed").
- `hook_gen` (`src/Core/Solver/Context/DG/DG_Soundness.thy:856-865`) and
  `placed_dg_gen_of_strict` (`src/Analysis/Instances/Mixed/Exec_DG_Bridge.thy:2038-2052`)
  are already fully generic in every parameter, including the classifier.
- `sound_dg_hooks`/`sound_dg_hooks_ltr` locales fix `gs` as a plain locale
  parameter (same generalize-in-place shape as `sound_dg_spec`), so
  `interpretation ... sound_dg_hooks gammaDG is_global edge_tree combine_tree
  enter_tree` is already the "classic instantiation" — no separate constant
  needed for that half.

**Not adding a new wrapper now.** The one place a classic-route example would
need boilerplate beyond `Example_Sign_Placement.thy`'s pattern is
`placed_dg_gen_of_strict`'s `owner_of`/`locations_of` arguments: the classic
spine has no owner-scoped locations at all (it is a flat single-store
`dg_spec`), so "classic" values for those two arguments are a trivial
constant-scope instantiation, not a mechanical rename — genuinely a
per-example modeling choice (what counts as "the" scope when there is no
owner-local/global split to begin with), not something a single generic
constant can prejudge correctly for every domain. Revisit after the Parity
migration (next in order): if the same trivial `owner_of`/`locations_of`
shape repeats verbatim, promote it to a named generic constant then, with a
concrete second data point instead of a guess from zero migrations.

## Example audit and migration status

Legend for **Route**: `classic` = uses `dg_spec`/`sound_dg_spec`/
`unit_dg_spec`/`dg_gen_of`/`restrict_local_resolved_q`/
`restrict_global_resolved_q` directly or via its own from-scratch instance;
`new` = uses `hook_gen`/`sound_dg_hooks`/`placed_dg_gen_of_strict`/
`dg_refines_on`; `n/a` = not a D/G collecting-soundness example (route 2 or 3
above).

Legend for **Status**: `MIGRATED` (done + committed), `TODO`, `N/A` (out of
scope), `INFRA` (core-instance-infra backing classic examples; migrated only
as a side effect of migrating its consuming examples, not standalone).

### Sign family

| File | Route | Headline theorem | Size | Difficulty | Status |
| --- | --- | --- | --- | --- | --- |
| `src/Examples/Sign/Example_Sign_Placement.thy` | new | `sign_placement_dg_td_collect_sound` | 972 | done | MIGRATED (already on new route; see note below) |
| `src/Analysis/Instances/Sign/Sign_DG.thy` | classic | `sign_dg_post_solution_collect_sound` (interpretation `sound_dg_spec "unit_dg_spec sign_tf" gamma_unit is_global`) | 85 | medium | INFRA (backs `Exec_Sign_DG_Run.thy` and both CallString examples) |
| `src/Examples/Sign/Exec_Sign_DG_Run.thy` | new (migrated) | `dgEx_source_run_sound` | 1029 | done | **MIGRATED** (`57d2b377`) — see note below |
| `src/Examples/Sign/CallString/Example_Sign_DG_CallString_K1.thy` | classic | `sign_nest_1_pp_abs`, `sign_nest_1_activation_collect_sound` | 536 | **blocked** — call-string-keyed (`pp × cfg_node list`/`gk_1`), `sound_dg_hooks`/`sound_dg_hooks_ltr` are hardcoded to `pp × unit`/`unit`; see Unexpected findings | BLOCKED |
| `src/Examples/Sign/CallString/Example_Sign_DG_CallString_K2.thy` | classic | `sign_nest_2_pp_abs`, `sign_nest_2_activation_collect_sound`, `sign_k2_strictly_more_precise_than_k1_at_g` | 426 | **blocked** — same gap as K1, reuses K1's `Spoly` | BLOCKED |
| `src/Examples/Sign/Example_Mixed_Flow_Sign.thy` | n/a (route 2) | — | 104 | — | N/A |
| `src/Examples/Sign/Example_Side_Branch_Calls.thy` | n/a (route 2) | — | 184 | — | N/A |
| `src/Examples/Sign/Example_Side_Execute.thy` | n/a (route 2) | — | 126 | — | N/A |
| `src/Examples/Sign/Example_Side_Proc_Global.thy` | n/a (route 2) | — | 72 | — | N/A |
| `src/Examples/Sign/Exec_Sign_Run.thy` | n/a (route 2, plain eval demo) | — | 70 | — | N/A |

**Note on Sign — investigated per task instructions, do not assume "already
done":** `Example_Sign_Placement.thy` is **not** a migration of an existing
classic Sign example. It is a standalone new-route validation example with
its own minimal program (`x := 5; g := x`, one global), imported by nothing
and importing nothing from the classic Sign examples. The actual classic Sign
D/G flagship — the thing that plays the role
`Example_Interval_DG_Flagship.thy` plays for Interval — was
`src/Examples/Sign/Exec_Sign_DG_Run.thy` (its own doc comment used to read
"matching the pattern in `Example_Interval_DG_Flagship`"). That file has now
been migrated (commit `57d2b377`), built directly on
`Example_Sign_Placement.thy`'s already-proven pattern (`hook_gen`/
`sound_dg_hooks`/`sound_dg_hooks_ltr`/`placed_dg_gen_of_strict`, classifier
`declared_global sign_ex_prog`) rather than a fresh design. The program (a
call-free `x := 1; y := x`, no globals) made `keep_local`/`publish_side`
trivial the same way Sign_Placement's own policy is trivial, so the migration
was close to a faithful structural port with node/edge substitutions, not new
proof engineering. The Sign CallString K1/K2 pair remain fully on the classic
spine and are **not** superseded or made redundant by either placement
example — different programs, different theorem names, no import
relationship. Those two remain open migration work.

**Precision-preservation judgment call, recorded for review**: the classic
`Exec_Sign_DG_Run.thy` used `unit_dg_spec`'s "diagonal" instance, which joins
the local (`D`) and global (`G`) unknowns unconditionally at every read. For
this call-free, global-free program that join was pure noise (there is
nothing in `G` to join against), and it made the classic route's own computed
value imprecise (`STop` for `x` at the exit) as a side effect of that
specific instance's design, not because the program or route required it.
The migrated file's placement policy keeps every location local (matching
`Example_Sign_Placement.thy`'s own "everything local" trivial-instance
choice), so it reads `x` and `y` back *exactly* as `SPos` — strictly more
precise than the retired classic file, not the same value. The task's
"preserve computed analysis results (same concrete values it currently
proves)" instruction is read here as "do not silently weaken or fabricate a
result," not as "reproduce a specific instance's incidental imprecision" —
the final soundness theorem's claim strength is unchanged (still a sound
over-approximation, just a tighter one), and the difference is documented
in-file (`dgEx_inspect`'s comment) and here rather than hidden. Flagging this
explicitly since it is a judgment call, not a mechanical fact.

### Interval family

| File | Route | Headline theorem | Size | Difficulty | Status |
| --- | --- | --- | --- | --- | --- |
| `src/Examples/Interval/Example_Interval_Placement.thy` | new | `placement_dg_td_collect_sound` | 3114 | done | MIGRATED (already on new route; standalone, see note) |
| `src/Analysis/Instances/Interval/Interval_DG.thy` | classic | `ivl_dg_post_solution_collect_sound` (interpretation `sound_dg_spec "unit_dg_spec ivl_tf" gamma_unit is_global`) | 81 | medium | INFRA |
| `src/Examples/Interval/Example_Interval_DG_Flagship.thy` | classic | `flagship_source_run_sound`, `flagship_head_bound_proper` | 329 | large — investigated, found a new complication (assume/guard transfer needs full-state not per-location commutation); see "Interval flagship investigation" below | TODO (investigated, not started) |
| `src/Examples/Interval/Example_Interval_DG_IP_Flagship.thy` | classic | `twice_collect_sound`, `twice_source_run_sound` | 323 | large (own `dg_gen_of`; baseline the Ctx/CallString family builds on) | TODO |
| `src/Examples/Interval/Ctx/Example_Interval_DG_Ctx_Sound.thy` | classic | `twice_ctx_pp_abs` | 269 | **blocked** — `side_cfg_T_eff_keyed_seed_dg` with routed keys; see Unexpected findings | BLOCKED |
| `src/Examples/Interval/Ctx/Example_Interval_DG_Ctx_Flagship.thy` | classic | graph-inspection lemmas, own `Spoly :: (ivl exec_dg_st, ivl exec_dg_st) dg_spec` | 266 | **blocked** — same gap | BLOCKED |
| `src/Examples/Interval/Ctx/Example_Interval_DG_Ctx_Collect.thy` | classic | `twice_activation_collect_sound` | 441 | **blocked** — instantiates `activation_collect_sound` directly, same key-type gap | BLOCKED |
| `src/Examples/Interval/Ctx/Example_Interval_DG_Ctx_Multi_Call_Regression.thy` | classic (via import) | `multi_call_naive_head_reconstruction_is_wrong_for_some_return` | 84 | **blocked (transitively)** — consumes Ctx_Flagship's classic CFG/result; unblocks only once Ctx_Flagship does | BLOCKED |
| `src/Examples/Interval/Ctx/Example_Interval_Source_Ctx.thy` | classic (via import) | `twice_source_ctx_run_sound`, `twice_source_toplevel_at_bot` | 56 | **blocked (transitively)** — consumes Ctx_Collect's classic result | BLOCKED |
| `src/Examples/Interval/CallString/Example_Interval_DG_CallString_K1.thy` | classic | `nest_1_pp_abs`, `nest_1_activation_collect_sound` | 595 | **blocked** — `side_cfg_T_eff_keyed_seed_dg`, `gk_1`/`cfg_node list` keys; see Unexpected findings | BLOCKED |
| `src/Examples/Interval/CallString/Example_Interval_DG_CallString_K2.thy` | classic | `nest_2_pp_abs`, `nest_2_activation_collect_sound` | 471 | **blocked** — same gap, reuses K1's `Spoly` | BLOCKED |
| `src/Examples/Interval/CallString/Example_Interval_DG_CallString.thy` | classic | `twice_cs_pp_abs`, `twice_cs_activation_collect_sound` | 605 | **blocked** — same gap | BLOCKED |
| `src/Examples/Interval/CallString/Call_String_Solver_Refinement.thy` | classic | many per-node facts, `project_sigma_part_post_solution` | 1797 | **blocked** — call-string-keyed (`pp × cfg_node list + gk_1`) throughout; same gap, and separately the hardest single file to port even once unblocked (hand-derived on `restrict_local_resolved_q`/`restrict_global_resolved_q`, no `dg_spec` abstraction layer) | BLOCKED |
| `src/Examples/Interval/Example_Guard_Refinement.thy` | n/a (route 3, backward-filter precision compare) | — | 96 | — | N/A |
| `src/Examples/Interval/Example_Interval_Loop_Coverage.thy` | n/a (route 2, plain LTR) | — | 179 | — | N/A |
| `src/Examples/Interval/Example_Interval_Side_Proc_Global.thy` | n/a (route 2) | — | 41 | — | N/A |
| `src/Examples/Interval/Example_Proc_Call.thy` | n/a (route 2) | — | 339 | — | N/A |
| `src/Examples/Interval/Exec_Ivl_Run.thy` | n/a (route 2, plain eval demo) | — | 133 | — | N/A |

**Note on Interval — investigated per task instructions:**
`Example_Interval_Placement.thy` does not duplicate or supersede
`Example_Interval_DG_Flagship.thy` (loop program, `x:=0; while(x<20){x:=x+1}`)
or `Example_Interval_DG_IP_Flagship.thy` (two-call `twice` program, the
declared context-insensitive baseline for the whole classic Ctx/CallString
family). All three use different programs and prove differently-named,
differently-shaped theorems. `Example_Interval_Placement.thy` is a standalone
leaf (its own `balance`/`request_count` global-routing program), imported by
nothing and importing nothing from the classic Interval lineage. Nothing in
the classic Interval family is redundant; all of it remains open migration
work.

### Mixed / Parity

| File | Route | Headline theorem | Size | Difficulty | Status |
| --- | --- | --- | --- | --- | --- |
| `src/Analysis/Instances/Mixed/Mixed_Sign_Interval.thy` | classic | `mixed_si_postfix_collect_sound` / `mixed_si_post_solution_collect_sound` (own `dg_spec` combining Sign+Interval) | 216 | medium | INFRA |
| `src/Analysis/Instances/Mixed/Rel_Order_Domain.thy` | classic | own `rel_order_spec :: (relc, relc) dg_spec`, interpretation only | 460 | medium (custom relational domain) | TODO |
| `src/Examples/Mixed/Example_Relational_DG_Demo.thy` | classic | graph-inspection lemmas, own `dg_gen_of` combining `Rel_Order_Domain` + `Interval_DG` | 192 | medium | TODO |
| `src/Examples/Parity/Example_Parity_DG_Flagship.thy` | new (migrated) | `parity_source_run_sound` | 1371 | done | **MIGRATED** (`31574413`) — see "Join-node transport lemma" below |

`src/Analysis/Instances/Mixed/Exec_DG_Bridge.thy` (4217 lines) is shared
transport-lemma infrastructure for **both** routes simultaneously — classic
machinery (`fun_of_dg_st`, `fun_of_exec_dg_st`, `restrict_local_resolved_q`,
`restrict_global_resolved_q`, `dg_tree_st_commute`) and new-route machinery
(`dg_refines_on`, `placed_dg_gen_of_strict`, the `placed_dg_*_of_strict`
family) are interleaved throughout the same file. It is imported by nearly
every example in every family above. Not itself an "example" to migrate, but
the single highest-leverage/highest-risk file for task 4/5 — do not delete
anything from it until every classic consumer listed in this file is
confirmed migrated. Route: `mixed/comparison`, Status: INFRA, do not touch
structurally until task 4.

### CallString / Context — see Sign and Interval family tables above

All CallString and Ctx examples are listed under their domain (Sign or
Interval) above; there is no separate cross-domain CallString/Ctx file.

### Remaining flagship / capstone

| File | Route | Notes | Status |
| --- | --- | --- | --- |
| `src/Examples/Voblint.thy` | classic-only today | Pure `imports` bundle (zero own lemmas/definitions). Imports every classic-route example listed above (directly or transitively via the Ctx chain) plus every route-2/route-3 example. **Imports neither `Example_Sign_Placement.thy` nor `Example_Interval_Placement.thy`** — the two new-route examples are currently outside the capstone's build graph entirely. | TODO (must be updated once its classic imports are migrated; low individual difficulty since it has no own proofs, but is the integration point — see "Unexpected findings") |

### Non-DG examples and infra checked and excluded (confirmed, not skipped)

Everything below was checked directly (imports, grep for `dg_spec`/`hook_gen`
markers, and file content) and confirmed to never touch the D/G collecting-
soundness architecture. No action needed; listed so a future resume does not
re-check them.

`src/Examples/CFG/*.thy` (7 files, pure CFG/compile/simulation regression) ·
`src/Analysis/Instances/Interval/{Interval_Arithmetic,Interval_Bounds,Interval_Print,Interval_Warrowing,Interval_Point_Digest,Interval_Side_Soundness}.thy`
· `src/Analysis/Instances/Interval/{Interval_Backward,Interval_Domain,Interval_Lattice,Interval_Transfer,Ivl_Exec}.thy`
(core-instance-infra, classifier-parametric `_for` transfer/readback shared
prerequisite of both routes, not itself route-specific) ·
`src/Analysis/Instances/Parity/*.thy` (4 files, core-instance-infra) ·
`src/Analysis/Instances/Sign/{Sign_Arithmetic,Sign_Backward,Sign_Domain,Sign_Exec,Sign_Lattice,Sign_Local_Effects,Sign_Print,Sign_Side_Soundness,Sign_Transfer}.thy`
(core-instance-infra / route 2) ·
`src/Analysis/Instances/Sign/Sign_Exec_Sound.thy` (route 2, `LTR_TD_Side_Eff_Exit`;
one incidental `restrict_global_resolved_q` textual hit inside an unrelated
proof, does not make it a classic-DG example) ·
`src/Analysis/Instances/NamedGlobalSign/Sign_Named_Global_Eff.thy` (route 2) ·
`src/Analysis/Instances/Tooling/Analysis_GraphViz.thy` (tooling) ·
`src/Examples/Tooling/*.thy` (4 files, GraphViz/strategy-tree demos).

## Unexpected findings

- **Correction (superseded by `M4_SPINE_BOUNDARY_AUDIT.md`): the CallString/Ctx
  family is not "architecturally blocked" in any sense that matters, because it
  was never going to be migrated in the first place.** The paragraph below
  (kept for historical accuracy) correctly found that `sound_dg_hooks`/
  `sound_dg_hooks_ltr` hardcode the `pp \<times> unit`/`unit` key shape and have no
  call-string/context-sensitive generalization. What it got wrong was the
  framing that this is a *gap* blocking otherwise-desirable migration. The
  boundary audit found `dg_ctx_activation`/`routed_context`
  (`DG_Ctx_Activation.thy`, `Routed_Context.thy`) already provide exactly that
  generalization — for `sound_dg_spec`, not `sound_dg_hooks` — already proven,
  already used by every classic CallString/Ctx example in the repository
  today. Since the migration itself is cancelled (see top of file), there is
  nothing to unblock: these examples were never going to move, and they are
  not missing any generalization they actually need. If `sound_dg_spec` is
  ever unified with `sound_dg_hooks` (the one real follow-up the audit
  recommends), `dg_ctx_activation`/`routed_context`'s existing key-polymorphic
  machinery would plausibly transfer to the hooks route with much less new
  proof engineering than building an equivalent from scratch — but that is
  downstream of the unification, not something anyone needs to solve now.

  Original (superseded) finding, kept verbatim below for record: investigated
  `Example_Sign_DG_CallString_K1.thy` as the
  next migration target per the task order. It builds its equation system with
  `side_cfg_T_eff_keyed_seed_dg` directly over unknowns typed
  `(pp \<times> cfg_node list, gk_1, ...) eqsT` — call-string-keyed locals (`pp \<times>
  cfg_node list`, truncated call stack) and a routed global-key type (`gk_1`),
  not the flat `(pp \<times> unit, unit, ...)` shape every migrated/migratable
  placement example uses. The M4 hook/placement soundness locales
  (`sound_dg_hooks` and `sound_dg_hooks_ltr`, `src/Core/Solver/Context/DG/DG_Soundness.thy:799-808`
  and `DG_LTR_Sound.thy:134-144`) fix `edge_tree`/`combine_tree`/`enter_tree`'s
  type literally as `pp \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow> (pp \<times> unit, unit, ('D,'G)
  dg_state) strategy_tree` — `pp \<times> unit` and `unit` are hardcoded in the
  locale signature, not type variables. `hook_gen`
  (`DG_Soundness.thy:856-865`) and `hook_post_solution_collect_sound_ltr`
  inherit that same fixed shape. (The claim in the original text that "there is
  no context-sensitive/call-string generalization of this locale anywhere in
  the repo today" was checked against `sound_dg_hooks` only and is the part the
  boundary audit corrected — the generalization exists for `sound_dg_spec`.)
  **Consequence, now moot**: `Example_Sign_DG_CallString_K1.thy`/`_K2.thy`,
  `Example_Interval_DG_CallString*.thy` (`.thy`, `_K1`, `_K2`),
  `Call_String_Solver_Refinement.thy`, and all four `Interval/Ctx/*.thy`
  examples (Ctx_Sound, Ctx_Flagship, Ctx_Collect are context-/call-string-keyed
  by the same mechanism; Ctx_Multi_Call_Regression and Source_Ctx consume
  Ctx_Collect's classic result) stay on the classic route permanently, not as a
  blocked migration but as the correct architectural choice. Historical
  recommendation at the time (skip this family for now, proceed to Parity, task order item
  2) and plain Interval (item 3) — both context-insensitive, same shape as the
  completed Sign migration — and revisit CallString/Ctx only once someone
  explicitly scopes and authorizes the locale generalization as its own task.
- **Sign and Interval "migration" is not what it looks like from the outside.**
  Both `Example_Sign_Placement.thy` and `Example_Interval_Placement.thy` were
  *new, additional, standalone* examples proving the new architecture sound —
  not rewrites of any existing classic example — when this task started. The
  classic Sign flagship (`Exec_Sign_DG_Run.thy`) has since been migrated
  (`57d2b377`); the classic Interval flagships
  (`Example_Interval_DG_Flagship.thy`, `Example_Interval_DG_IP_Flagship.thy`)
  are still fully untouched open work. Anyone reading only the top-level task
  framing ("Sign — already done") would wrongly conclude Sign requires no
  further work; the CallString finding above shows Sign is not even fully
  unblocked yet.
- **`Voblint.thy` imports neither placement example.** The capstone's build
  graph is 100% classic-route today. This means task 3 migrations can proceed
  bottom-up (leaves first) without breaking the capstone at any point, but
  also means nobody has yet proven a *multi-domain* new-route capstone
  assembles (i.e., that `hook_gen`-based Sign and Interval specs can coexist
  the way `Mixed_Sign_Interval.thy`/`Example_Relational_DG_Demo.thy` currently
  combine under classic `dg_spec`). Worth flagging as a real open question for
  whoever migrates the Mixed family, not something to solve speculatively now.
- **`unit_dg_spec` and `Split_State.thy` pre-merge corrections are already
  landed** (commit `865cbe10`), so the two mechanical fixes the PR review
  flagged as blocking are done; they do not need to be redone here.
- **Parity has no dedicated `_DG.thy` infra file.** Unlike Sign/Interval,
  `Example_Parity_DG_Flagship.thy` builds the classic `unit_dg_spec`/
  `dg_gen_of` wiring inline. Migrating it is therefore comparable effort to
  porting `Interval_DG.thy` and its flagship together, not a lighter lift
  despite Parity being the "simpler" domain.
- (Superseded by the CallString/Ctx blocked-family finding above:
  `Call_String_Solver_Refinement.thy` would additionally have been the
  hardest single file to port even if the key-type gap did not exist.)

## Batch build status

Green as of commit `31574413`: `make build SESSION=Voblint_Examples` (which
transitively builds `Voblint_VIMP`/`Voblint_CFG`/`Voblint_Core`/
`Voblint_Analysis`/`Voblint_Formalization` first) exits 0, `Finished`, zero
errors, zero `sorry`/`oops` across every file touched so far
(`Exec_Sign_DG_Run.thy`, `Parity_Transfer.thy`, `Parity_Exec.thy`,
`DG_Framework.thy`, `Exec_DG_Bridge.thy`, `Example_Parity_DG_Flagship.thy`).

## Join-node transport lemma (generic library addition)

**Done and committed.** Migrating `Example_Parity_DG_Flagship.thy` required a
generic library addition first, since its loop compiles to a join node
(`Statement 2`, two predecessors — `(Statement 1, EA_Assign ''y'' (N 1))`
the loop entry and `(Statement 4, EA_Assign ''y'' (Plus (V ''y'') (N 1)))`
the back-edge, confirmed by direct `eval` of
`intra_predecessor_list parity_cfg (Statement n)` for every node) that
`placed_hook_se_edge` cannot cover — it assumes
`intra_predecessor_list g v = [(u, a)]`, a literal singleton, throughout its
~150-line proof (`Exec_DG_Bridge.thy:2508-2658`). Every prior placement
example (`Example_Sign_Placement.thy`, `Example_Interval_Placement.thy`,
`Exec_Sign_DG_Run.thy`) is a straight-line, single-predecessor-per-node CFG,
so this gap had never been hit before.

**Assessed as in-scope, not a repeat of the CallString/Ctx blocker**: the
CallString gap is a locale whose *type* is hardcoded (`pp × unit` baked into
`sound_dg_hooks`'s fixed constants), with no per-example workaround short of
changing the locale. Here the underlying combinators
(`side_cfg_T_eff_keyed_seed_trees`, `dep_aux_seqcomp`, the `Finite_Set.fold`-
based join per the project's locked "Joins" decision) are already generic
over an arbitrary predecessor list — `placed_hook_se_edge` is only a
*convenience wrapper* that special-cases the singleton case. A generalized
sibling covering two predecessors is exactly the accepted "issue #81 cost"
(hand-rolled per-node work), not the disallowed generic post-solution-
assembly abstraction.

**What was added** (commit `121fd0e5`), alongside `placed_hook_se_edge` as
instructed, fully generic (not Parity-specific — usable by Interval's own
loop next):

- `side_cfg_T_eff_keyed_seed_trees_two_edges` (`DG_Framework.thy`, next to
  `_single_edge`): the two-predecessor fold law. The generator's own
  accumulator (`side_acc_dg`) reduces a join node to a plain `⊔` of its two
  predecessors' individually-projected contributions, with `sides_of_rhs`
  accumulator-independent per the existing `sides_of_rhs_side_rhs_fold_dg_acc_indep`
  lemma — an ordinary instance of the same generic fold, not new solver
  machinery.
- `placed_hook_se_join_edge` (`Exec_DG_Bridge.thy`, right after
  `placed_hook_se_edge`): the join-node counterpart, fully generic in
  classifier/owner/scope/policy/transfer/CFG, identical to
  `placed_hook_se_edge` except one predecessor `(u, a)` becomes two,
  `(u1, a1)` and `(u2, a2)`, each with its own transport-agreement
  hypothesis (`raw1`/`raw2`, `side_outside_raw1`/`side_outside_raw2`). Reuses
  `placed_hook_se_edge`'s own structure twice (once per edge, via
  `dg_refines_on_project_strict`) and combines the two facts with the
  already-existing `dg_refines_on_sup` (found already proved generically at
  `Exec_DG_Bridge.thy:126-142` — did not need to write a new one, an initial
  attempt to do so was removed as a duplicate).
- Debugging note for future reference: `rule placed_hook_se_join_edge[where
  v = ... and u1 = ... and a1 = ... and u2 = ... and a2 = ...]` at a call
  site raised "No such variable in theorem: ?u1" — instantiating `v` first
  in the `where` clause while also trying to instantiate premise-only
  variables `u1`/`a1`/`u2`/`a2` (which don't appear in the lemma's `shows`
  conclusion) failed to elaborate. Dropping `u1`/`a1`/`u2`/`a2` from the
  `where` clause and letting them stay schematic — filled in automatically
  when the later `show "intra_predecessor_list ... = [(concrete_u1,
  concrete_a1), (concrete_u2, concrete_a2)]"` step unifies against the
  schematic subgoal — worked cleanly. Single-variable-per-position `where`
  substitutions (`u`, `a`, as `placed_hook_se_edge` itself uses) do not hit
  this; it was specific to instantiating multiple premise-only variables at
  once. Worth knowing before writing the next join-node call site.

Batch-verified as part of the full `Example_Parity_DG_Flagship.thy` build
(see below) and separately confirmed green on its own before that (`make
build SESSION=Voblint_Examples`, `Finished`, exit 0).

## Parity flagship migration — done

**Done and committed (`31574413`)**, built on the join-node lemma above plus
the `_for` transfer layer (`9d676a84`, already recorded). Structure mirrors
`Exec_Sign_DG_Run.thy` for the eight single-predecessor nodes (entry,
Statement 0/1/3/4/5/6, FunctionResult) via `parity_se_edge` (a
file-local wrapper around `placed_hook_se_edge`, same pattern as `dgEx_se_edge`),
and uses `placed_hook_se_join_edge` directly for `Statement 2`
(`parity_se_join_statement2`). Also added a file-local
`parity_hook_gen_two_edge_dep` (dependency-closure bound for the join node,
mirroring the existing single-edge version) and two small executable
agreement lemmas Parity didn't yet have,
`parity_tf_st_for_assume_agree`/`_assume_not_agree` (Parity's assume/
assume-not transfer is the identity, so these have the same trivial shape as
`parity_tf_st_for_nop_agree`).

Placement policy is the same trivial "everything local" choice as
`Example_Sign_Placement.thy`/`Exec_Sign_DG_Run.thy`, despite this program
having a real declared global (`G`) — establishing that the trivial policy
is an accepted default for a migrated flagship, not something that needs
solving per-program. Preserves `parity_source_run_sound`'s name and
source-run-level claim shape (via `source_reaches_ltr_collect` +
`parity_collect_sound`, mirroring `dgEx_source_run_sound`'s construction).
Preserves the GraphViz rendering section (`parity_graph_config`/
`parity_dot`) essentially unchanged, since node/key types stayed
`pp × unit`/`unit`. Computed values (`PEven` for `x` at every reachable
point) match the retired classic file's own results exactly — no precision
judgment call needed here, unlike Sign: the classic Parity instance already
seeded its global unknown through `restrict_global_resolved_q` rather than
the unrestricted local state, so it was never polluted the way the retired
classic Sign flagship's diagonal instance was.

Batch build: `make build SESSION=Voblint_Examples`, `Finished`, exit 0,
`Example_Parity_DG_Flagship` shown compiling at 100% in the log. Zero
`sorry`/`oops` across all touched files.

## Interval flagship investigation — stopped before touching the file

Parity family is fully done (`_for` layer `9d676a84`, join-node lemma
`121fd0e5`, flagship `31574413`). Moved to
`Example_Interval_DG_Flagship.thy` next per the task order and investigated
it (read-only: opened the file, ran temporary `eval` checks on
`intra_predecessor_list`, reverted them — `git diff` on this file is empty,
nothing was changed).

**CFG shape confirmed by `eval`** (program `x:=0; while(x<20){x:=x+1}`, 6
nodes: `FunctionEntry`, `Statement 0..3`, `FunctionResult`):
`Statement 1` (the loop head) has two predecessors — `(Statement 0,
EA_Assign ''x'' (N 0))` and `(Statement 2, EA_Assign ''x'' (Plus (V ''x'')
(N 1)))` — so `placed_hook_se_join_edge` applies directly there, same as
Parity's `Statement 2`. `Statement 2`'s own predecessor is `(Statement 1,
EA_Assume (Less (V ''x'') (N 20)))` and `Statement 3`'s is `(Statement 1,
EA_AssumeNot (Less (V ''x'') (N 20)))` — both ordinary single-predecessor
nodes, but both edges are `EA_Assume`/`EA_AssumeNot`, not `EA_Assign`.
Interval's `_for` transfer layer is already complete (`ivl_tf_for`,
`ivl_tf_st_for`, `ivl_is_sound_transfer_for`, and all five action-agreement
lemmas already exist in `Interval_Transfer.thy`/`Ivl_Exec.thy` — unlike
Parity, no prerequisite layer needed building).

**New complication found, not yet resolved**: `ivl_tf_st_for_nop_agree`/
`_assign_agree`/`_ret_none_agree`/`_ret_some_agree` (`Ivl_Exec.thy:228-283`)
are stated in the same per-*location*, `universe`-scoped form
`placed_hook_se_edge`'s `raw` premise needs (matching the shape every
migration so far has used for Nop/Assign/Ret). But
`ivl_tf_st_for_assume_agree`/`_assume_not_agree` (`Ivl_Exec.thy:292-306`)
are stated differently — over **full function equality**,
`fun_of_resolved_st_q_for gs s_exec = s_abs` as the hypothesis, not a
per-location `\<forall>location \<in> universe. ...` hypothesis. The file's own
comment explains why: "Guard filters commute totally through the readback
... no scope side condition is needed, unlike the write-shaped actions
above" — i.e. `bfilter_ivl`'s soundness is proved at the whole-store level
because the underlying backward-filter machinery
(`ivl_backward_domain.bfilter`, `Interval_Backward.thy`) is not assumed
local to the guard's own variables anywhere in its generic statement, even
though for this specific guard (`x < 20`, one variable) it plausibly only
touches `x` in practice.

This matters because `placed_hook_se_edge`'s `raw` premise is per-location:
it needs agreement and the transfer's output only at locations in
`locations_of v`, not a whole-store equality. Full-store agreement between
`fun_of_resolved_st_q_for gs (dg_hook_D sigma_exec u)` and `dg_hook_D
sigma_abs u` genuinely does **not** hold outside `locations_of v` — that
mismatch (executable defaults vs. `top_val` completion outside scope) is
exactly what the completion machinery (`complete_abs_on`,
`le_lift_if_dg_refines_on_and_le`) exists to bridge, so it cannot be
sidestepped by assuming it away.

**Not yet determined whether this is a real blocker or a bounded, in-scope
fix.** A plausible path (not attempted, not verified): construct a "patched"
abstract state agreeing with the executable state everywhere outside
`locations_of v` and with the real `sigma_abs` inside it, invoke
`ivl_tf_st_for_assume_agree` against that patched state (satisfying its
full-equality premise by construction), then argue the *output* at
in-scope locations is insensitive to the patching — which requires either
an existing "`bfilter_ivl` only reads/writes the guard's own variables"
fact (not found in `Interval_Backward.thy` after a direct search for a
scoped/local variant of `bfilter_ivl_st_commute`) or a fresh one. Building
that fact, if it doesn't reduce to something already proved, risks being
exactly the kind of new general reasoning about the backward-filter
machinery that would need real investigation to scope correctly — not
attempted this session because of that uncertainty, per the coordinator's
own instruction to stop and report rather than push through if a gap turns
out to run deeper than a per-example hand-roll (unlike the join-node case,
which was confirmed shallow before implementing it).

**Recommendation for next resume**: before writing any `.thy` content,
resolve this specific question first: does `bfilter_ivl`/`bfilter_ivl_st`
(`Interval_Backward.thy`, `ivl_backward_domain.bfilter`) have, or can it
cheaply be shown to have, a property like "for `location \<notin>` the guard's
own variable set, the filter's output at `location` equals its input at
`location`"? If yes, deriving a scoped corollary of
`ivl_tf_st_for_assume_agree`/`bfilter_ivl_st_commute` (mirroring the
`_nop_agree`/`_assign_agree` shape) is bounded, per-example-appropriate work
in `Ivl_Exec.thy` (or file-local in the flagship example itself) and the
migration proceeds exactly like Parity's did. If the backward-filter
machinery is genuinely relational (output at one location can depend on
input at another location currently in a *different* clause of a compound
guard) even in principle, this needs the same "stop and report" treatment
the CallString gap got, since patching around it would risk quietly
weakening the transport argument. Read `Interval_Backward.thy` in full
(especially `ivl_backward_domain`'s locale assumptions and
`bfilter_st_commute`'s actual statement) before deciding.

`Example_Interval_DG_IP_Flagship.thy` (queued after
`Example_Interval_DG_Flagship.thy`) and the Mixed family
(`Rel_Order_Domain.thy`, `Example_Relational_DG_Demo.thy`) remain untouched
and unblocked as far as investigated; do not skip ahead to them speculatively
without first resolving the assume-edge question above, since
`Example_Interval_DG_Flagship.thy` was the explicitly assigned next step and
Interval's IP flagship almost certainly has assume/guard edges too (any
non-trivial control flow does). Do not attempt any `BLOCKED`-status row
(CallString/Ctx) until that separate key-type gap is scoped and authorized.
Same process throughout once resumed: I/Q only, incremental diagnostics
checks, full batch build polled to a real exit code, commit per completed
file, update this checklist, stop cleanly and report if runway runs out.

## Issue #81 — generic solved-node post-solution assembly (done, validated on both migrated instances)

**Migration paused for this task, per explicit instruction, before touching
Interval flagship's assume-edge question above.** Both `Exec_Sign_DG_Run.thy`
and `Example_Parity_DG_Flagship.thy` hand-rolled an equivalent ~100-150-line
`consider`/`case` split to assemble their final `part_post_solution` fact from
per-node `dep\<^sub>L`/`se_constraint_holds` facts. Issue #81 asked for a generic
theorem covering that assembly step, validated by shrinking both files, not
just one.

**What was built**, inside the `sound_dg_hooks` locale in
`src/Core/Solver/Context/DG/DG_Soundness.thy` (new subsection "Generic
post-solution assembly", right before the locale's closing `end`) — fully
generic over the locale's `edge_tree`/`combine_tree`/`enter_tree`/CFG, so
every existing and future `interpretation ... sound_dg_hooks` (Sign, Parity,
and any future instance) picks these up automatically with no restatement:

- `hook_gen_dep_and_se_entry`, `hook_gen_dep_and_se_single`,
  `hook_gen_dep_and_se_pair`: each turns an already-known `dep\<^sub>L` equation
  (empty at entry, a singleton at an ordinary edge, a pair at a join) plus
  membership fact(s) plus an `se_constraint_holds` fact into the single
  `dep\<^sub>L ... \<subseteq> vars \<and> se_constraint_holds ...` conjunct
  `part_post_solution_iff_se_constraint_holds`'s ball needs at that node.
  Proved by `auto`/`blast` off the supplied facts — no CFG- or
  domain-specific content.
- `part_post_solution_of_ball`: turns exit membership plus the whole
  ball-quantified conjunction into `part_post_solution` itself
  (`unfolding part_post_solution_iff_se_constraint_holds using ... by blast`).

**Per-example use**: each file's `X_dg_td_abs_post_solution` lemma now opens
with `proof (rule X_sound_dg_hooks.part_post_solution_of_ball)`, proves one
`have node_<name>: "... \<subseteq> nodes \<and> se_constraint_holds ..."` fact per CFG
node (each a one-line `by (rule X_sound_dg_hooks.hook_gen_dep_and_se_*, ...)`
citing that node's own pre-existing `_single_edge_dep`/`_two_edge_dep`/
`_entry_dep` fact and `_se_*` fact — these two families are unchanged,
CFG-specific content, not part of this issue's scope), then closes with a
single combining step:
`using node_a node_b ... unfolding X_nodes_def by auto`. This replaces the
former `consider (a) ... | (b) ... proof cases case a ... qed` chain entirely
— no more per-node named cases, no more nested `qed`/`next` cascade; per-node
work is still domain-specific `have`s (unavoidable — CFG shape and transfer
soundness genuinely differ per node) but the assembly into
`part_post_solution` itself is one generic theorem application plus one
`auto` call, not N repeated hand-derivations of the same conjunction shape.

**Validated deduplication, not just one file's line count**: both files were
rewired and both got shorter — `Exec_Sign_DG_Run.thy` 1028 -> 997 lines (5
nodes), `Example_Parity_DG_Flagship.thy` 1370 -> 1336 lines (9 nodes,
including the join node via `hook_gen_dep_and_se_pair`). The reduction is
modest in raw lines (per-node CFG facts dominate the lemma's size and are
untouched) but the assembly step itself shrank from ~100-155 lines of
case-split scaffolding to ~10-15 lines of flat `have`s plus one `by auto`, and
the same three node-shape lemmas now serve both files with zero restatement —
the actual point of the issue.

**Investigated and deferred, not attempted (recorded per coordinator
instruction to investigate before committing to it)**: a deeper design was
raised mid-task — redefine each example's solved-node set as (or provably
equal to) `cfg_nodes g` (`src/CFG/CFG_Def.thy`) and discharge every node's
`dep \<subseteq> nodes` obligation generically via the already-existing
`intra_endpoints_in_nodes`/`call_endpoints_in_nodes`/`cfg_entry_in_nodes`
lemmas, removing even the per-node `have`s. Checked directly: those three
CFG-well-formedness lemmas exist and are exactly the right shape, and
`cfg_nodes g` would coincide with both files' hand-enumerated node sets for
these two small, fully-reachable CFGs. But turning that into a working
dependency-closure argument needs a **new** generic bound on `dep_aux` of the
whole `side_cfg_T_eff_keyed_seed_trees` fold for an *arbitrary-length*
predecessor/combine/enter list (the existing `_single_edge`/`_two_edges`/
`_entry`/`_single_enter`/`_single_combine` family in `DG_Framework.thy` is
deliberately shape-specific per predecessor count, and the closest existing
list-induction lemma, `dep_aux_side_rhs_fold_dg_commute`
`src/Analysis/Instances/Mixed/Exec_DG_Bridge.thy`, proves a *commutation*
between two valuations, not a *subset* bound against `cfg_nodes`). That is
new framework-level proof engineering, not a rewire of existing pieces, and
risked not landing cleanly within this task's remaining scope. Deferred as a
follow-up, not attempted; the two rewired files do not depend on it. If
revisited: the target lemma is roughly `dep_aux sigma (side_cfg_T_eff_keyed_seed_trees
pred_sel gkey edge_tree combine_tree enter_tree g bot0 s0d s0g (v, ctx)) \<subseteq>
(Inl ` (fst ` set (pred_sel g v) \<union> ...)) \<union> {Inr (gkey ctx)}`, proved by
induction over `hook_trees g v`'s list (mirroring
`dep_aux_side_rhs_fold_dg_commute`'s induction shape) given per-leaf `dep_aux`
bounds on `edge_tree`/`combine_tree`/`enter_tree` (already available
generically for the placement spine's own tree shape via
`dep_aux_placed_abs_dg_edge_tree`, `Exec_DG_Bridge.thy`).

Batch build: `make build SESSION=Voblint_Examples`, see build-status line
below for this task's result. Zero `sorry`/`oops` in both touched example
files and in the `DG_Soundness.thy` addition, confirmed via
`get_sorry_positions` on each file.
