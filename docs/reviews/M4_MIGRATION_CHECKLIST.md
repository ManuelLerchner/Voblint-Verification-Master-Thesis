# M4 placement-spine migration checklist

Live, resumable tracker for migrating every D/G example off the classic
`dg_spec`/`sound_dg_spec`/`unit_dg_spec`/`dg_gen_of` spine onto the M4
placement spine (`hook_gen`/`sound_dg_hooks`/`sound_dg_hooks_ltr`/
`placed_dg_gen_of_strict`, classifier-parametric `_for` storage, independent
`keep_local`/`publish_side` placement, `dg_refines_on`/`complete_abs_on`/
`le_lift_if_dg_refines_on_and_le` transport). Background and the two-spine
situation: `docs/reviews/M4_ARCHITECTURE_PR_REVIEW.md`. Task driving this file:
the "migrate every classic-route D/G example onto the placement spine, then
retire the classic spine" instruction set.

**Hard ordering rule**: nothing gets deleted (task 5) until every in-scope
example below is migrated and green. Do not jump ahead.

**Resume protocol**: re-read this file plus `git log --oneline -20` before
continuing. Each row's Status is the source of truth, not any earlier prose in
this file.

## Progress snapshot

- Task 1 (audit): **done**, this file is the output.
- Task 2 (classic-policy adapters): **assessed, not adding new ones yet** — see
  "Task 2 findings" below.
- Task 3 (migrate examples): **not started**. Sign is already on the new route,
  but as a *standalone parallel example*, not a migration of an existing
  classic Sign flagship (see "Sign" row and "Unexpected findings" below).
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
| `src/Examples/Sign/Exec_Sign_DG_Run.thy` | classic | `dgEx_source_run_sound` | 158 | medium | TODO — **this is the real classic Sign flagship**, not `Example_Sign_Placement.thy`; see note |
| `src/Examples/Sign/CallString/Example_Sign_DG_CallString_K1.thy` | classic | `sign_nest_1_pp_abs`, `sign_nest_1_activation_collect_sound` | 536 | large (own `dg_spec` build-out) | TODO |
| `src/Examples/Sign/CallString/Example_Sign_DG_CallString_K2.thy` | classic | `sign_nest_2_pp_abs`, `sign_nest_2_activation_collect_sound`, `sign_k2_strictly_more_precise_than_k1_at_g` | 426 | large (reuses K1's `Spoly`) | TODO |
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
`Example_Interval_DG_Flagship.thy` plays for Interval — is
`src/Examples/Sign/Exec_Sign_DG_Run.thy` (its own doc comment: "matching the
pattern in `Example_Interval_DG_Flagship`"). That file, plus the Sign
CallString K1/K2 pair, are still fully on the classic spine and are **not**
superseded or made redundant by `Example_Sign_Placement.thy` — different
programs, different theorem names, no import relationship. All three remain
open migration work.

### Interval family

| File | Route | Headline theorem | Size | Difficulty | Status |
| --- | --- | --- | --- | --- | --- |
| `src/Examples/Interval/Example_Interval_Placement.thy` | new | `placement_dg_td_collect_sound` | 3114 | done | MIGRATED (already on new route; standalone, see note) |
| `src/Analysis/Instances/Interval/Interval_DG.thy` | classic | `ivl_dg_post_solution_collect_sound` (interpretation `sound_dg_spec "unit_dg_spec ivl_tf" gamma_unit is_global`) | 81 | medium | INFRA |
| `src/Examples/Interval/Example_Interval_DG_Flagship.thy` | classic | `flagship_source_run_sound`, `flagship_head_bound_proper` | 329 | large | TODO |
| `src/Examples/Interval/Example_Interval_DG_IP_Flagship.thy` | classic | `twice_collect_sound`, `twice_source_run_sound` | 323 | large (own `dg_gen_of`; baseline the Ctx/CallString family builds on) | TODO |
| `src/Examples/Interval/Ctx/Example_Interval_DG_Ctx_Sound.thy` | classic | `twice_ctx_pp_abs` | 269 | medium | TODO |
| `src/Examples/Interval/Ctx/Example_Interval_DG_Ctx_Flagship.thy` | classic | graph-inspection lemmas, own `Spoly :: (ivl exec_dg_st, ivl exec_dg_st) dg_spec` | 266 | medium-large | TODO |
| `src/Examples/Interval/Ctx/Example_Interval_DG_Ctx_Collect.thy` | classic | `twice_activation_collect_sound` | 441 | large | TODO |
| `src/Examples/Interval/Ctx/Example_Interval_DG_Ctx_Multi_Call_Regression.thy` | classic (via import) | `multi_call_naive_head_reconstruction_is_wrong_for_some_return` | 84 | small (leaf, no own `dg_spec`) | TODO |
| `src/Examples/Interval/Ctx/Example_Interval_Source_Ctx.thy` | classic (via import) | `twice_source_ctx_run_sound`, `twice_source_toplevel_at_bot` | 56 | small (thin leaf) | TODO |
| `src/Examples/Interval/CallString/Example_Interval_DG_CallString_K1.thy` | classic | `nest_1_pp_abs`, `nest_1_activation_collect_sound` | 595 | large (own `dg_spec` build-out) | TODO |
| `src/Examples/Interval/CallString/Example_Interval_DG_CallString_K2.thy` | classic | `nest_2_pp_abs`, `nest_2_activation_collect_sound` | 471 | large (reuses K1's `Spoly`) | TODO |
| `src/Examples/Interval/CallString/Example_Interval_DG_CallString.thy` | classic | `twice_cs_pp_abs`, `twice_cs_activation_collect_sound` | 605 | large | TODO |
| `src/Examples/Interval/CallString/Call_String_Solver_Refinement.thy` | classic | many per-node facts, `project_sigma_part_post_solution` | 1797 | **very large** — hand-derived per-CFG-node proof directly on `restrict_local_resolved_q`/`restrict_global_resolved_q`; likely needs a from-scratch rewrite, not a rename | TODO |
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
| `src/Examples/Parity/Example_Parity_DG_Flagship.thy` | classic | `parity_source_run_sound` | 269 | medium — Parity has **no** dedicated `Parity_DG.thy` infra file; this example builds its `unit_dg_spec`/`dg_gen_of` wiring inline, so migrating it is comparable effort to porting `Interval_DG.thy` + a flagship together | TODO |

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

- **Sign and Interval "migration" is not what it looks like from the outside.**
  Both `Example_Sign_Placement.thy` and `Example_Interval_Placement.thy` are
  *new, additional, standalone* examples proving the new architecture sound —
  not rewrites of any existing classic example. The actual classic Sign/
  Interval flagships (`Exec_Sign_DG_Run.thy`, `Example_Interval_DG_Flagship.thy`,
  `Example_Interval_DG_IP_Flagship.thy`) are fully untouched and still open
  work. Anyone reading only the top-level task framing ("Sign — already done")
  would wrongly conclude Sign requires no further work; it requires the same
  amount of work as every other family.
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
- **`Call_String_Solver_Refinement.thy` (1797 lines) is the hardest single
  file** — it hand-derives the classic per-node equation shape directly from
  `restrict_local_resolved_q`/`restrict_global_resolved_q` with no
  abstraction layer in between, unlike every other classic example which goes
  through a `dg_spec` interpretation. Expect a from-scratch rewrite rather
  than a mechanical port when its turn comes.

## Batch build status

Not run in this session (no `.thy` edits made; audit and checklist only, per
task instructions that `.thy` work happens only through I/Q and only during
actual migration work).
