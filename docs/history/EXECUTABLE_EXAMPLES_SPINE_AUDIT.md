# Executable Sign/Interval examples: spine audit (2026-07-10)

Audit of every executable Sign and Interval example under
`src/Formalization/Examples/Executable/`: which transfer/read spine each uses, and
whether it should migrate to the canonical seeded-clean `R_read` spine
(`side_cfg_T_eff_cmp_seed_st` + `clean_ctx_collect_rread` + `point_digest`).

**Headline finding.** The examples are already partitioned by spine (the directory
layout `Core / Context / Keyed / SeededClean` *is* the spine split). Every canonical
positive precision demo already rides seeded-clean `R_read`. Every non-seeded example is
an intentional baseline, a negative counterexample, a distinct routing (entry-store
context), or base infrastructure. The only remaining legacy executable showcase in the
seeded-clean cone is the interval rehydration example, which is retained as historical /
pending migration material. The one structural change is promoting the reusable
`point_digest` library out of the examples tree into `src/Analysis`.

## Spine legend

| Spine | Marker | Read |
| --- | --- | --- |
| Core | base solver run, no context | `local` |
| Context (entry-store) | `Spec.context = entry store`; `Exec_Ctx_Bridge` | `Obs` (`local ⊔ global`) |
| Keyed Obs | value-keyed global; `route_read_cmp` via `TD_Side_Eff_Cmp_Sound` | `Obs` (`local ⊔ keyed-global`) |
| Retain | keyed + local retains flow-sensitive global | `Obs` |
| Value-digest | digest-filtered read | `vd_obs` / `mode_obs` |
| Seeded-clean `R_read` | `side_cfg_T_eff_cmp_seed_st` + seed | `R_read` (`local` only) |

## Classification table

### Sign

| File | Spine | Migration verdict | `point_digest` premise |
| --- | --- | --- | --- |
| `Core/Exec_Sign_Run` | Core | base infra — nothing to migrate | N/A (no routing) |
| `Context/Exec_Sign_Ctx_Run` | Context (entry-store) | retained — distinct route (entry-state context) | N/A (routes on entry store, not value digest) |
| `Context/Exec_Sign_Ctx_Gen_Run` | Context (entry-store) | retained — distinct route | N/A |
| `Context/Exec_Sign_Ctx_Seeded_Run` | Context (entry-store, ⊆) | retained — shipped active route (§19 REQUIRED) | N/A (subseteq route, not `=`-digest) |
| `Keyed/Exec_Sign_Cmp_Keyed_DG_Run` | Keyed Obs | current DG baseline | reads the keyed DG solution directly |
| `Keyed/Exec_Sign_Cmp_Keyed_Gen_Run` | Keyed Obs (generator) | retained baseline | fails: `kgen_slot_merged = SNonNeg` |
| `Keyed/Exec_Sign_Cmp_Keyed_Retain_Run` | Retain | **retained** (task-mandated retain example) | fails: `retain_keyed_merged_G = SNonNeg` |
| `Keyed/Exec_Sign_Cmp_Keyed_Retain_EnterMono` | Retain (negative) | **retained counterexample** — refutes ENTER_MONO over Obs | **refuted**: `enter_mono_read_not_point` |
| `Keyed/Exec_Sign_Mode_Value_Run` | Value-digest | retained — active value-digest track | N/A (digest read, not point routing) |
| `SeededClean/Exec_Sign_Cmp_RRead_Split` | comparison | retained — pins `Obs = R_read ⊔ G_read` | N/A (decomposition lemma) |
| `SeededClean/Exec_Sign_Cmp_Seed_Enter` | seeded-clean | **already migrated** | (feeds the sound run) |
| `SeededClean/Exec_Sign_Cmp_Seed_Sound` | seeded-clean | **already migrated** (canonical positive) | holds |
| `SeededClean/Exec_Sign_Seed_EnterMono` | seeded-clean | **already migrated** — reuses `point_digest` | **proved**: `seed_slots_point` |

### Interval

| File | Spine | Migration verdict | `point_digest` premise |
| --- | --- | --- | --- |
| `Core/Exec_Ivl_Run` | Core | base infra (loop/widening probe) — nothing to migrate | N/A |
| `Context/Exec_Ivl_Ctx_Run` | Context (entry-store) | retained — distinct route | N/A |
| `Context/Exec_Ivl_Ctx_Gen_Run` | Context (entry-store) | retained — distinct route | N/A |
| `SeededClean/Exec_Ivl_Cmp_Seed_Sound` | seeded-clean | **already migrated** (kernel obligations) | holds |
| `SeededClean/Exec_Ivl_Cmp_Seed_Clean_Run` | seeded-clean | deleted | retired canonical positive; replaced by the DG-native seeded-enter probe and shared support |
| `SeededClean/Exec_Ivl_Cmp_Seed_Clean_Derived_Run` | seeded-clean | deleted | retired derived-global showcase |
| `SeededClean/Exec_Ivl_Cmp_Seed_Rehydrate_Run` | seeded-clean | deleted | return rehydration on the `R_read` spine; readback crossed a combine |
| `SeededClean/Exec_Ivl_Seed_EnterMono` | seeded-clean | deleted | replaced by the DG-native seeded-enter probe and shared support |

### Common

| File | Role | Action |
| --- | --- | --- |
| `Common/Exec_Context_Run_Common` | executable-run glue (imports `Exec_St` + TD) | stays in examples |
| `Common/Seed_EnterMono_Lift` | reusable theorem library (`point_digest` locale) | **promote to `src/Analysis`** (see below) |

## Before / after precision (already coexisting in-repo)

The seeded-clean spine's precision gain over the Obs baseline is already materialized as a
pair of theories over the same Sign program family (`kgen_cfg`):

| Metric | Keyed Obs baseline | Seeded-clean `R_read` | Source of the gain |
| --- | --- | --- | --- |
| per-context caller local, site 4 | `SZero` (`kgen_slot_zero_precise`) | `SZero` (`kgen_seed_clean_caller_locals`) | — |
| per-context caller local, site 7 | `SNonNeg` (merged, `kgen_slot_merged`) | `SPos` (`kgen_seed_clean_caller_locals`) | seed delivers caller's precise global into callee-entry local; clean read never rejoins the coarse published slot |
| join-all global | `SNonNeg` (`kgen_join_materialised_slots`, `slot_join_all`) | two separated points | value-keyed `Spec.context` + `R_read` |
| ENTER_MONO routing | **refuted** (`enter_mono_read_not_point`) | **proved** (`seed_enter_mono_call_sites`) | routing slot is a point (γ-exact) |

Interval mirrors this: the seeded-clean run keeps each call-site routing slot a point
(`iseed_caller_locals_points`: `[0,0]` at site 4, `[10,10]` at site 7), and
`iseed_enter_mono_call_sites` discharges ENTER_MONO — versus the Obs read whose
`local ⊔ global` join would widen a shared-context global to a proper range
(`non_point_ivl_splits`).

The comparison is theorem-level on both sides (the merged/point slot values are `by eval`
supporting evidence under named lemmas; the ENTER_MONO proved/refuted split is
theorem-level). No migration is needed to produce it — the baseline and the positive are
deliberately separate theories on the same program.

## Why the remaining split stays

1. **Canonical positives already ride seeded-clean.** The remaining canonical interval
   seeded-clean positives use the shared support and the DG probe; they discharge
   `clean_ctx_collect_rread`, with ENTER_MONO via `point_digest`.
2. **Keyed Obs examples are the baseline the spine improves on.** Migrating them would
   erase the "before" side of the comparison. Their routing slot is non-point by design
   (`kgen_slot_merged = SNonNeg`), so `point_digest` genuinely fails there — migration is
   *invalid*, not merely neutral.
3. **Context examples route on the entry store, not a value digest.** They demonstrate a
   distinct, shipped Goblint routing (`Spec.context = entry state`); `point_digest` does
   not apply (no value-digest projection). `Exec_Sign_Ctx_Seeded_Run` is a shipped active
   route (§19 REQUIRED).
4. **Retain / value-digest / RRead-split are counterexamples or characterisations** the
   task mandates keeping (one Obs baseline, one retain, the explicit non-point
   counterexamples: `non_point_sign_splits`, `non_point_ivl_splits`,
   `enter_mono_read_not_point`).
5. **Core theories are base infrastructure** with no context routing.
6. **The rehydration showcase is distinct.** It demonstrates return rehydration on the
   `R_read` spine and still relies on the legacy executable combine path.

The deleted base/derived/seeded-enter-mono interval files remain deleted.

## Organization audit

- **Demo-only witnesses already live under `Examples/`.** No executable witness needs
  moving *into* the examples area.
- **One reusable library sits in the wrong place.** `Seed_EnterMono_Lift` (the
  `point_digest` locale + generic `enter_mono_point`) is a pure theorem library — its only
  dependency is `Voblint_Analysis.Clean_RRead_Sound`, and it is consumed by two example
  theories (`Exec_Sign_Seed_EnterMono`, `Exec_Ivl_Seed_EnterMono`). By the "reusable
  infrastructure and theorem libraries under `src/Analysis`" principle it belongs next to
  `Clean_RRead_Sound` in `src/Analysis/Generic/Solver/Context/`, not in the examples'
  `Common/` folder. It is already a clean split (no executable/example content), so the
  move needs no lemma extraction.
- **No mixed theory needs splitting** before moving; `Exec_Context_Run_Common` (the other
  `Common/` theory) is executable-run glue and correctly stays in the examples tree.

## Deliverables summary

- **Migrated:** the DG-native seeded-enter probe and the shared interval executable
  support split.
- **Retained:** baselines (Keyed Obs), retain example, negative counterexample
  (`Retain_EnterMono`), entry-store context route, value-digest track,
  RRead-split characterisation, Core infra, and the canonical SeededClean
  positives.
- **Moved:** `Seed_EnterMono_Lift` → `src/Analysis/Generic/Solver/Context/` (session
  `Voblint_Formalization` → `Voblint_Analysis`).
- **Deleted:** `Exec_Ivl_Cmp_Seed_Clean_Run`, `Exec_Ivl_Cmp_Seed_Clean_Derived_Run`,
  `Exec_Ivl_Cmp_Seed_Rehydrate_Run`, `Exec_Ivl_Seed_EnterMono`.
- **Precision regressions:** none. **Failed premises:** none newly introduced; the
  documented `point_digest` failures at Obs/retain slots are the intended negative results.
- **Final structure:** the `point_digest` capability library sits with the kernel it
  serves under `src/Analysis`; the examples import it session-qualified. The seeded-clean
  interval cone is split between canonical DG-native positives and deleted legacy
  rehydration support.
