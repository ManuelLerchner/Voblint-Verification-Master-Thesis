# Keyed / context-sensitive analysis: migration onto the DG spine

> **Status:** IN PROGRESS. Phase 1 (one executable analysis migrated) + Phase 2
> (routing/read backbone) + a Phase-5 **backbone unification** DELIVERED and
> batch-green. Phases 3–4 (remaining example migration, homogeneous-kernel
> deletion) open. No homogeneous theory deleted yet — every consumer still lives.

## Backbone unification (Phase-5, delivered)

`src/Analysis/Generic/Solver/Context/Ctx_Collect_Backbone.thy` (new) holds the
**single canonical** context-sliced trace induction, carrier-agnostic over an opaque
meaning `M :: pp x 'c => store set` and a routing read `rd`:

* `trace_ctx_sound_meaning` — the trace backbone (was duplicated as the homogeneous
  `post_fixpoint_sound_at_ctx_semantic_generic` and my DG `trace_ctx_sound_meaning`).
* `collect_ctx_sound_meaning` — its `cfg_collect_ctx` wrapper.

Both spines now **derive** from it:

* homogeneous `post_fixpoint_sound_at_ctx_semantic_generic`
  (`TD_Side_Eff_Cmp_Sound`) is now a corollary: `M (p,c) = [[renv sigma (p,c)]]` — the
  ~65-line induction collapsed to a 10-subgoal `rule` application;
* DG `sound_dg_spec.dg_collect_ctx_sound` (`DG_Route_Soundness`) instantiates
  `M (p,c) = gammaDG (dg_D_c sigma c p) (dg_G_c sigma c)`.

Import shape (no cycle — the backbone imports only `Voblint_CFG.CFG_Collect_Trace`,
the shared ancestor of both towers):

```
CFG_Collect_Trace
    |
Ctx_Collect_Backbone   (canonical trace backbone, opaque M)
   /                 \
TD_Side_Eff_Cmp_Sound   DG_Route_Soundness
(homogeneous M=[[.]])    (DG M=gammaDG)
```

### Key architectural finding (affects Phases 3–4)

The endpoint the ~15 seeded-clean/digest consumers actually ride is
`sound_transfer.clean_ctx_collect_rread` (+ `_head`, `_bound`, `clean_cfg_collect_rread`,
five `clean_rread_*`). It reads **only the local slot** `[[sg (Inl u)]]` and deliberately
never joins the published global — a **single-domain** read discipline. Re-expressing it
over the two-gamma DG carrier would be **false abstraction** (an unused `G` slot;
Kappelmann audit item 3). The correct consolidation is what was done here: unify at the
**backbone**, keeping the clean/cmp readers as single-gamma `M` instances. So the goal's
"migrate every consumer onto the DG carrier" over-reaches for the clean family; "one
canonical spine" is achieved at the backbone, with `unit`/single-gamma and two-gamma DG
both as `M`-instances.

Follows the feasibility slice (`DG_KEYED_CONTEXT_FEASIBILITY.md`, conditional GO).
The objective is a single canonical DG context-sensitive proof spine, retiring the
homogeneous CMP/Ctx kernel once every consumer migrates.

## Phase 2 — routing/read backbone (DELIVERED)

`src/Analysis/Generic/Solver/Context/Goblint/DG/DG_Route_Soundness.thy`.

The homogeneous `context_analysis_soundness.collect_sound` trace induction
(`post_fixpoint_sound_at_ctx_semantic_generic`) never inspects the abstract-state
structure of a read — only the *meaning set* `[[renv sigma (v, ctx)]]` at each
(point, context). So it factors through an opaque meaning `M :: pp x 'c => store set`:

| Name | Statement | Role |
| --- | --- | --- |
| `trace_ctx_sound_meaning` | trace backbone with meaning abstracted to `M`, routing read to `rd` | carrier-agnostic core (line-for-line port of the homogeneous generic) |
| `collect_ctx_sound_meaning` | `... ==> cfg_collect_ctx dg cmp g S v ctx <= M (v, ctx)` | carrier-agnostic form of `context_analysis_soundness.collect_sound` |
| `sound_dg_spec.dg_collect_ctx_sound` | same eight obligations over `gammaDG`; `M (v, ctx) = dg_gamma_c sigma ctx v`, routing read `dg_D_c` | **the DG replacement** for `side_cfg_T_eff_cmp_collect_ctx_sound_semantic` |

The homogeneous `side_cfg_T_eff_cmp_collect_ctx_sound_semantic` is now recoverable as
the `M (v, ctx) = [[side_env_cmp gcmp sigma (v, ctx)]]` instance of the same backbone
(not yet re-derived — the homogeneous theorem still stands on its own proof).

Routing read: `dg_D_c` (the local slot's Answer) is used directly rather than a
separate `dg_route` constant — a locale `definition` added in `DG_Route_Soundness`
does not propagate to the `sign_dg` interpretation declared earlier in `Sign_DG`, so
the endpoint reads through `dg_D_c` (defined in `DG_Context_Soundness`, which the
interpretation sees).

The general-`gcmp` join tier was **not** built — no migrated consumer needs it (all
use `gcmp = (=)`, own-slot).

## Phase 1 — one executable analysis migrated (DELIVERED)

`src/Formalization/Examples/Executable/Sign/Keyed/Exec_Sign_Cmp_Keyed_DG_Run.thy` —
the DG migration of `Exec_Sign_Cmp_Keyed_Run`. Imports only `Sign_DG` +
`DG_Route_Soundness`: the homogeneous context-soundness stack is dropped.

| Homogeneous (`Exec_Sign_Cmp_Keyed_Run`) | DG (`Exec_Sign_Cmp_Keyed_DG_Run`) | Note |
| --- | --- | --- |
| `kw_sig :: ... => sign abs_state` | `kw_dg :: ... => (sign abs_state, sign abs_state) dg_state` | keyed slots as a DG solution |
| `[[side_env_cmp (=) kw_sig (p, ctx)]]` | `sign_dg.dg_gamma_c kw_dg ctx p` | **`dg_meaning`: provably equal** to `[[kw_loc p ⊔ kw_slot ctx]]` — same store set, theorem strength preserved |
| `senv`, `glob_read` | `dg_D_val`, `dg_G_val`, `dg_meaning` | reads |
| `local_post` + `cmp_sound` → `comb_bound`, `comb_sound` (via `combine_read_cmp_le` / `combine_case_cmp_sound`) | `kw_res_le` → `dg_combine_obligation` (via `sound_dg_spec.combine_sound`) | switching combine, **no `combine_read_cmp` plumbing** |
| `LOCAL_POST_inst` / `CMP_SOUND_inst` | `dg_COMB_premise` | the endpoint's `COMB` premise in exact shape |
| `derived_ctx`, `route_*` | `derived_ctx`, `route_*` (through `dg_D_c`) | routing precision |
| `merge_join_all`, `contexts_separated` (`by eval`) | `merge_join_all`, `contexts_separated` | **identical executable precision** — `by eval` preserved |

Executable comparison: `merge_join_all` (`(kw_slot False ⊔ kw_slot True) ''G'' =
SNonNeg`) is proved `by eval` in both — same underlying slots, same result. The keyed
reads separate the two contexts (`contexts_separated`) identically.

### Friction encountered
* `sign_dg.dg_route` unusable (interpretation predates the definition) → route through
  `dg_D_c`; the endpoint follows suit.
* I/Q stale constant table: after deleting a `definition`, textual references still
  resolved against the cached constant; only purging every reference and reprocessing
  surfaced the real errors. Batch build is the gate.
* Numeral `Suc 0` vs `1` blocked a combine `simp`; resolved in-proof.
* `\<^const>` antiquotation fails on locale *facts* (assumptions/lemmas), fine on locale
  *constants* — text uses plain cartouches for the former.

## Phase 3 — replacement matrix (partial)

| Homogeneous theorem | DG replacement | Migrated consumers | Old still needed? |
| --- | --- | --- | --- |
| `side_cfg_T_eff_cmp_collect_ctx_sound_semantic` | `sound_dg_spec.dg_collect_ctx_sound` | `Exec_Sign_Cmp_Keyed_DG_Run` (witness-level) | **yes** — homogeneous keyed/digest examples below still consume it |
| `post_fixpoint_sound_at_ctx_semantic_generic` | `trace_ctx_sound_meaning` | (endpoint) | yes |
| `context_analysis_soundness.collect_sound` | `collect_ctx_sound_meaning` | (endpoint) | yes |
| `combine_read_cmp_le` + `combine_case_cmp_sound` | `sound_dg_spec.combine_sound` (locale) | `Exec_Sign_Cmp_Keyed_DG_Run` | yes |

Remaining homogeneous consumers (must migrate before any deletion):
`Exec_Sign_Cmp_Keyed_Run`, `Exec_Sign_Cmp_Keyed_Retain_EnterMono`,
`Exec_Sign_Cmp_RRead_Split`, `Exec_Sign_Cmp_Seed_Sound`, `Exec_Sign_Seed_EnterMono`,
`Exec_Ivl_Cmp_Seed_Sound`, `Exec_Ivl_Cmp_Seed_Rehydrate_Run`,
`Example_Finite_Sign_Context_Analysis`, `Example_Entry_Store_Context_Precision`,
`Example_Interval_Recursion_Rehydrate`, plus the Analysis-side support tower
(`TD_Side_Eff_Ctx_Sound`, `TD_Side_Eff_Cmp_Sound`, `Clean_RRead_Sound`,
`Seeded_*`, `Digest_*`, `Activation_*`).

## Phases 4–5 — open

* Migrate the remaining keyed Sign analyses, then digest/context examples, then
  Interval, keeping every session green.
* Delete the homogeneous CMP/Ctx kernel only after every consumer above is migrated
  and the replacement matrix shows zero remaining references.

## Proof-size

* New: `DG_Route_Soundness.thy` ~227 lines (backbone + endpoint);
  `Exec_Sign_Cmp_Keyed_DG_Run.thy` ~200 lines.
* The within-context tier is proved once (`collect_ctx_sound_meaning`) and reused;
  `combine_read_cmp` / `route_read_cmp` plumbing is replaced by one `combine_sound`
  locale call.

## Dependency shift

Before: keyed examples → `TD_Side_Eff_Cmp_Sound` → `TD_Side_Eff_Ctx_Sound` +
`Global_Cmp_Read` + `Context_Domain` (the homogeneous kernel).

After (migrated example): `Exec_Sign_Cmp_Keyed_DG_Run` → `Sign_DG` +
`DG_Route_Soundness` → `DG_Context_Soundness` → `DG_Soundness`. No homogeneous
context-soundness dependency.
