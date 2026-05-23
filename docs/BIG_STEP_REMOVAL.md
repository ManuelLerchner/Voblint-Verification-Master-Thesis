# Big-Step Removal Plan

**Status:** proposed (2026-05-23).
**Predecessor:** `SMALL_STEP_MIGRATION.md` (landed 2026-05-22). That migration made small-step the operational basis and `pipeline_sound_small_step` the canonical theorem, but **kept big-step** as the spec-side predicate per Phase 5.
**This plan revisits that decision.** Goal: drop `big_step` entirely; `cfg_collect` is the spec, small-step is the operational view.

## Why revisit Phase 5

The retention argument in `SMALL_STEP_MIGRATION.md:60-72` rested on three claims:

1. **Hoare-logic comparability** — keep `(c,s) ⇒ t` for future Hoare specs.
2. **Executable interpreter** — `code_pred big_step` for demos.
3. **Spec-side readability** — exit-only corollaries read better with `⇒`.

Audit of repo state after that migration:

- **(1)** No Hoare-style proof in the repo. Solver soundness is the only correctness story. No planned Hoare extension in the roadmap.
- **(2)** `code_pred small_step` exists; small-step is equally executable. The big-step interpreter has no consumer.
- **(3)** Exit-only big-step corollaries (`pipeline_sound`, `sign_pipeline_sound_scaffold`, `ivl_pipeline_sound`) are strictly weaker than `pipeline_invariant_sound`, which is already the supervisors' requested **point-map** formulation (`Pipeline.thy:225`). The big-step exit shape is legacy framing of a theorem the analyzer already proves better.

The retention was insurance against future Hoare/extraction needs that haven't materialised. Cost of removal is now bounded and tractable; cost of keeping is ongoing cognitive load (two semantics, two specs, two corollary chains).

## Target end state

- `IMP2_Semantics.thy`: `aval`, `bval`, `small_step`, `→*`, determinism, `code_pred small_step`. No `big_step`.
- `IMP2_Collecting.thy`: `collect c S` redefined as exit-projected `cfg_collect`, **or removed entirely** if no consumer remains (see §"Open question" below).
- `CFG_Collecting.thy`: drops `big_step_cfg_path`, `compile_path_big_step`, `cfg_collect_exit_eq_collect`, plus the `WHILE compound paths` scaffolding block (lines ~867-1100). `cfg_collect` and the path/edges bridge `cfg_collect_eq_cfg_edges_collect` are the only spec-side artefacts left.
- Downstream specs (`Pipeline`, `TD_Soundness`, `Constraint_System_Sound`): hypotheses restated against small-step `→* (SKIP, t)` **or** against `cfg_collect` reachability (decision in §"Spec restatement").
- Examples: `Example_NonTerminating_Safe.thy` rewritten without `nonterm_prog_no_big_step` style lemmas (they were *demos* of small-step's superiority — self-defeating to keep when big-step is gone). `Example_CFG_Collecting_Equiv.thy` retired or restated against `cfg_collect`.

## What we lose

| Artefact | Mitigation |
|---|---|
| `big_step` executable interpreter | `code_pred small_step` covers it; remove the `code_pred big_step` demo |
| `(c,s) ⇒ t` Hoare-style spec syntax | `(c,s) →* (SKIP, t)` is one rewrite uglier; no Hoare consumer exists |
| `nonterm_prog_no_big_step` rhetorical lemmas | Restate as: no `→* (SKIP, t)` trace (same content, no extra predicate needed) |
| Big-step `pipeline_sound` exit corollary | `pipeline_invariant_sound` already gives stronger pp-wise statement |
| `cfg_collect_exit_eq_collect` (IMP↔CFG bridge theorem) | Becomes vacuous: `collect` either *is* `cfg_collect`-at-exit by definition, or no longer exists |

## What we gain

- One semantics, not two.
- ~400-500 LOC removed: `big_step` inductive (~30), `big_step_induct`+`big_step_determ` (~5), `code_pred big_step` (1), `big_to_small`+`small_to_big`+`small_step_big_step_eq` (~35, no longer needed without big-step), `big_step_cfg_path` + `compile_path_big_step` (~330 in `CFG_Collecting.thy`), `cfg_collect_exit_eq_collect` + supporting `WHILE compound paths` block (~250).
- `collect` definition becomes the CFG semantics directly — no separate IMP-level collecting + bridge.
- Downstream theorems read uniformly: every soundness claim is against `cfg_collect` reachability, the thing analyzers actually approximate.

## Open question — spec restatement style

Downstream consumers currently say `big_step (c,s) t`. Two replacement styles:

**(A) Small-step trace:** `(c, s) →* (SKIP, t)` — exit-terminating-run shape.
**(B) CFG reachability:** `t ∈ cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))` — direct.

(A) keeps the "terminating run" framing; (B) is exit-projection of the CFG semantics that the analyzer is already proved sound against. (B) makes `pipeline_sound` near-trivial (post-fixpoint soundness at the exit node), at the cost of consumers needing to know CFG syntax.

**Decision (2026-05-23):** (B) + `runs_to` abbreviation. Downstream theorems read `runs_to c s t`; CFG stays unfolded internal. Surface is source-level, but the spec IS CFG-level.

```isabelle
definition runs_to :: "com => store => store => bool" where
  "runs_to c s t == t : cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
```

Consumers say `runs_to c s t`; `unfolding runs_to_def` exposes the CFG form when needed. No CFG syntax in source-level statements; one definitional rewrite to access the analyzer-side fixpoint.

## Phase plan

### Phase 0 — branch + safety net (½ day)

1. Branch `big-step-removal` from `main`.
2. Tag current `main` as `pre-big-step-removal`.
3. Re-read `SMALL_STEP_MIGRATION.md` Phase 5 rationale; note any consumer of big-step not visible in `rg`.
4. **Sorry-count baseline**: run `rg -c "^[ ]*sorry|^[ ]*by sorry|oops" src/`; record total per file.

**Exit:** branch + tag exist; baseline recorded in `PROOF_PHASES.md`.

### Phase 1 — file split (no behaviour change) (½ day)

Cosmetic; lets later phases delete cleanly.

1. Split `IMP2_Semantics.thy` into:
   - `IMP2_BigStep.thy` — `aval`, `bval`, `big_step`, `big_step_determ`, `big_step_induct`, `code_pred big_step`, elims.
   - `IMP2_SmallStep.thy` — `small_step`, `→*`, `small_step_deterministic`, `star_seq2`, `seq_comp`, `big_to_small`, `small_to_big`, `small_step_big_step_eq`. Imports `IMP2_BigStep`.
2. `IMP2_Collecting.thy` imports `IMP2_BigStep` (for `collect_def`) and `IMP2_SmallStep` (for `collect_small_step`).
3. Update `ROOT` + every importer (`grep -l 'IMP2_Semantics'`).
4. Delete `IMP2_Semantics.thy`.
5. `make` green.

**Exit:** build green, no theorem statement changed.

### Phase 2 — restate downstream specs (1 day)

For each consumer of `big_step (c,s) t`, restate against `runs_to c s t` (see §"Open question — spec restatement style"). New `IMP2_Semantics.thy` (or wherever `runs_to` lands) exports `runs_to_def`; consumers `unfolding runs_to_def` to reach `cfg_collect`.

| File | Lemma(s) | New hypothesis |
|---|---|---|
| `Pipeline.thy:115` | `sign_pipeline_sound_scaffold` | `runs_to c s t` |
| `Pipeline.thy:172` | `ivl_pipeline_sound` | `runs_to c s t` |
| `Pipeline.thy:332-365` | `pipeline_sound` (big-step exit corollary) | **delete** — subsumed by `pipeline_invariant_sound` |
| `Pipeline.thy:374-400` | `pipeline_sound_small_step` (small-step exit corollary) | restate as `runs_to`-form corollary of `pipeline_invariant_sound` |
| `TD_Soundness.thy:38,69,107` | sign/ivl/generic analysis soundness | `runs_to c s t` |
| `Constraint_System_Sound.thy:248` | constraint system → CFG bridge | `runs_to c s t` |

Proofs after restatement should *shrink*: the `big_step_cfg_path[OF terminates]` step disappears; consumers use post-fixpoint soundness directly.

**Exit:** build green; `rg -n "big_step" src/` shows zero hits outside `IMP2_BigStep.thy` and `IMP2_SmallStep.thy` (`small_step_big_step_eq` still references it).

### Phase 3 — prune CFG bridge scaffolding (1 day)

Delete from `CFG_Collecting.thy`:

- `big_step_cfg_path` (line 1197+) — was Phase-2-era bridge.
- `compile_path_big_step` (line 1615+) — was Phase-2-era bridge.
- `cfg_collect_exit_eq_collect` (line 1983+) — bridge theorem, no consumer after Phase 2.
- `cfg_edges_collect_exit_le_collect` + `cfg_collect_exit_le_collect` + `collect_le_cfg_collect_exit` (supporting lemmas).
- `WHILE compound paths` block (line 867 — ~250 LOC of structural path lemmas only used by `compile_path_big_step`).

Each deletion: `make`, confirm nothing else used it. If something does, restore + tag `(* kept: used by X *)` and move on.

**Exit:** ~580 LOC removed from `CFG_Collecting.thy`; `make` green.

### Phase 4 — redefine `collect` or remove it (½ day)

Two sub-options:

**4a (keep `collect` as convenience):**
```isabelle
definition collect :: "com ⇒ store set ⇒ store set" where
  "collect c S = cfg_collect (to_cfg c) S (cfg_exit (to_cfg c))"
```
Structural lemmas (`collect_Seq`, `collect_If`, `collect_While`) re-proved via existing CFG decomposition (`cfg_edges_entry_exit_Seq/If/While` + `compile_*_0`). `collect_small_step` becomes a small-step characterisation of `cfg_collect` at exit — likely provable via existing path lemmas, may be deletable if no consumer.

**4b (delete `collect` entirely):**
Every consumer talks directly about `cfg_collect`. Less convenience for source-level reading, more uniformity.

**Lean 4a** for one session; if the structural lemmas don't fall out cleanly from CFG decomposition (`while_lfp_exit_collect`-equivalent is the risk), drop to 4b. Either way, `IMP2_Collecting.thy` shrinks dramatically (current `while_preserves_lfp` proof uses big-step induction — gone).

**Exit:** `IMP2_Collecting.thy` either redefined against `cfg_collect` (4a) or deleted (4b); build green.

### Phase 5 — delete big-step (½ day)

1. Delete `IMP2_BigStep.thy`.
2. Move `aval`/`bval` to `IMP2_SmallStep.thy` (or a new `IMP2_Expressions.thy` if cleaner).
3. Delete the equivalence lemma `small_step_big_step_eq` and its halves `big_to_small`/`small_to_big`.
4. Update every importer.
5. `rg -c "big_step" src/` returns 0.

**Exit:** build green; big-step gone.

### Phase 6 — examples + docs (½ day)

1. `Example_NonTerminating_Safe.thy` — replace `nonterm_prog_no_big_step` (lines ~49, 168) with a positive small-step safety property at an intermediate PP. The "no big-step exists" framing was a demo against the *predecessor* design; redundant now.
2. `Example_CFG_Collecting_Equiv.thy` — restate against `cfg_collect` directly (the equivalence it demonstrated is now definitional or vacuous). Likely shorter.
3. `Goblint_Formalization.thy:64-81` — `example_swap_terminates` + `example_swap_swaps`: restate against `cfg_collect` reachability or small-step trace.
4. Update `docs/ROADMAP.md`, `docs/PROOF_PHASES.md`, `docs/PROOF_OVERVIEW.md`, `docs/HOL_IMP_COMPARISON.md` — remove "two semantics" framing; the spec is `cfg_collect`.
5. Append entry to `docs/SMALL_STEP_MIGRATION.md` linking to this doc as "follow-up that took the next step".

**Exit:** examples build; docs reflect single-semantics design.

### Phase 7 — KB sync (½ day, KB repo)

In `~/goblint-formalization-kb/`:
1. `wiki/concepts/semantics-style-tradeoffs.md` — "both with roles" verdict replaced with "cfg_collect is the spec".
2. `wiki/concepts/collecting-semantics.md` — `cfg_collect` becomes the primary definition; big-step `collect` retired.
3. `wiki/concepts/soundness.md` — canonical statement against `cfg_collect`.
4. `wiki/research/decisions.md` — record decision to remove big-step.
5. `wiki/log.md` — entry: `## [YYYY-MM-DD] refactor | big-step removed; cfg_collect is the spec`.

**Exit:** wiki reflects landed state.

## Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| `while_preserves_lfp` / `while_lfp_exit_collect` analogues hard to prove via CFG path induction | **Medium** | Existing `cfg_path_While_loop_peel` + `cfg_path_While_split_trailing_exit` already do the CFG-side While decomposition. If structural `collect_While` is brittle, fall back to 4b (delete `collect`) |
| Supervisors want big-step retained for thesis exposition | Medium | Phase 2 spec restatement (cfg_collect vs small-step) is the only branch they should weigh in on; the technical removal stands either way. Send §"Open question" before Phase 2 |
| Hidden big-step consumer surfaces after Phase 1 | Low | Phase 0 audit + per-phase `make` green gate catches it |
| `code_pred big_step` was implicitly used by a demo not in `rg` output | Low | Search `code_thms`, `value`, `quickcheck` usages of big-step; replace with small-step equivalents |
| Removal breaks the path/edges bridge `cfg_collect_eq_cfg_edges_collect` | Low | That lemma is independent of big-step (CFG-internal); should not be affected |

## Estimated effort

| Phase | Estimate | Risk |
|---|---|---|
| 0 — prep | ½ day | none |
| 1 — file split | ½ day | none |
| 2 — restate downstream specs | 1 day | low (mechanical once style picked) |
| 3 — prune CFG bridge scaffolding | 1 day | low (deletions, gated by `make`) |
| 4 — `collect` redef or remove | ½ day | **medium** (structural lemma re-proofs) |
| 5 — delete big-step | ½ day | none |
| 6 — examples + docs | ½ day | none |
| 7 — KB sync | ½ day | none |
| **Total** | **~4.5 working days** | dominated by Phase 4 |

About half the small-step migration cost. Most of the heavy lifting (`cfg_collect`, the path/edges bridge, `pipeline_invariant_sound`) is already done.

## Definition of done

1. `rg -n "big_step" src/` returns 0.
2. `small_step_big_step_eq` removed.
3. Every soundness theorem in `Pipeline.thy`, `TD_Soundness.thy`, `Constraint_System_Sound.thy` states its hypothesis against `cfg_collect` (or small-step `→*`, per §"Open question").
4. `pipeline_invariant_sound` is the unambiguous top-level soundness theorem; exit-only corollaries either subsumed or trivially derived from it.
5. `Example_NonTerminating_Safe.thy` demonstrates intermediate-PP safety without reference to big-step.
6. `make` green; sorry count not regressed vs `pre-big-step-removal` tag.
7. Docs (`ROADMAP`, `PROOF_PHASES`, `PROOF_OVERVIEW`, `HOL_IMP_COMPARISON`, `SMALL_STEP_MIGRATION` follow-up entry) reflect single-semantics design.
8. KB pages updated.

## Non-goals

- Solver, domains, TF soundness: untouched.
- CFG construction (`to_cfg`, `compile`): untouched.
- `cfg_collect` definition or its path/edges equivalence: untouched.
- Adding new semantics (denotational, Hoare, etc.): explicitly out of scope.
