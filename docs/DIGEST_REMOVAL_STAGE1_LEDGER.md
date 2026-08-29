# Digest-Spine Removal — Stage 1 Dependency & Theorem Ledger

Status: **All stages complete (0–5).** The relational trace/digest spine is
removed; full build green, 0 `sorry`, 0 `oops`. Outcome record in
`docs/history/DIGEST_SPINE_REMOVAL_PLAN.md`. This ledger is retained as the working
record of the dependency analysis that guided the removal.

Status (original): **Stage 1 complete (read-only).** No theory deleted, renamed, or edited.
Companion to `docs/history/DIGEST_SPINE_REMOVAL_PLAN.md` (authoritative) and
`docs/history/DIGEST_SPINE_REMOVAL_HANDOFF.md`.

Baseline: branch `cleanup-after-trace-semantric`, HEAD `4779e90f`. Archive tag
`archive/relational-digest-experiment` → `4779e90f`. `src/` has **0 `sorry`**.

All facts below were checked against the working tree; recheck after edits.

---

## Headline result of Stage 1

The removal has **no abort condition on the core soundness path**, and the two
risks the handoff flagged both dissolve:

1. **Retained core rides the `cmp` generator, but only functionally.**
   `DG_Framework` and `Exec_DG_Bridge` (Category A) directly import
   `TD_Side_Eff_Cmp_Gen`. Its generator `side_cfg_T_eff_cmp` is **already
   functional** — parameters `gkey` (functional context key) and `cmb`
   (combine), no relation in the body. The load-bearing theorem
   `side_cfg_T_eff_cmp_collect_sound_gen` **concludes over plain `cfg_collect`**:

   ```isabelle
   shows "cfg_collect g S v0 ≤ ⟦side_env_cmp gcmp σ (v0, ctx)⟧"
   ```

   `cmp`/`gcmp` appears only as an **abstract-read filter** (`side_env_cmp gcmp`,
   premise `reads: gcmp ctx (gkey ctx)`), never on the concrete collecting side.
   Discharge it with exact-key equality (`gcmp = (=)`, read-at-ctx returns
   `gkey ctx`). The `_cmp` naming is legacy; there is no relational concrete
   compatibility to preserve.

2. **Activation flagship is already clean.**
   `Example_Interval_DG_Ctx_Collect` mentions only `cfg_collect_ctx_act`; it has
   **zero** occurrences of `cfg_collect_ctx`, `cfg_collect_trace`,
   `trace_witness`, `cmp`, or `gcmp`. `Interval_Point_Digest` — despite its name
   — contains only interval point-value helpers (`gamma_ivl_point`,
   `ivl_decode_gamma`, `ivl_is_point_decode`); no digest semantics. The import is
   a misnomer, not a dependency.

The genuine work therefore concentrates in three places, none of which need
relational concrete semantics:

* the **DG generic read tower** (`TD_Side_Eff_Cmp_*`, `Ctx_Collect_Backbone`,
  `Digest_Global_Read`) — collapse `cmp`/`gcmp` read filter to exact-key equality;
* the **Category-B examples** on `cfg_collect_trace` — restate over `cfg_collect`;
* **relocating shared defs out of `CFG_Collect_Trace`** — the retained
  `LTR_Def` imports it (see §4).

---

## 1. Symbol load (whole-tree occurrence counts)

| Symbol | `src/` occurrences | Meaning |
| --- | ---: | --- |
| `trace_witness` | 227 | flat-trace inductive (remove) |
| `cmp` | 267 | relational context compatibility (remove; abstract-read filter → equality) |
| `gcmp` | 181 | relational global-read filter (remove → equality) |
| `cfg_collect_trace` | 109 | flat-trace collector (remove) |
| `cfg_collect_ctx` | 93 | relational digest collector (remove) |
| `proc_entry` | 50 | modular trace seed constructor (remove) |
| `cfg_collect_ctx_act` | 36 | **functional activation collector (retain)** |
| `alpha_ctx` | 7 | flat digest context map (remove) |

This is a large migration, not a delete — the counts confirm the staged approach.

---

## 2. Direct + transitive importers of the ten Stage-1 target theories

Computed from parsed `imports` clauses (short-name graph over `src/**/*.thy`).

| Target theory | Direct importers | Transitive count |
| --- | --- | ---: |
| `CFG_Collect_Trace` | LTR_Def, Compile_Invariants, Constraint_System_Sound, Ctx_Collect_Backbone, Example_Trace_Digest_Combine, Example_Trace_Digest_ReachingCompat, Sign_Exec_Sound, Trace_Analysis_Sound, Voblint | **86** |
| `Ctx_Collect_Backbone` | DG_Route_Soundness, TD_Side_Eff_Cmp_Sound | 39 |
| `TD_Side_Eff_Cmp_Gen` | **DG_Framework**, **Exec_DG_Bridge** | 32 |
| `TD_Side_Eff_Cmp_Sound` | Clean_RRead_Sound, Digest_Global_Read, TD_Side_Eff_Cmp_Pull | 38 |
| `DG_Route_Soundness` | Exec_Sign_Cmp_Keyed_DG_Run, Local_DG | 7 |
| `Clean_RRead_Sound` | Seed_EnterMono_Lift | 4 |
| `Seed_EnterMono_Lift` | Interval_Point_Digest | 3 |
| `Digest_Global_Read` | Value_Digest_Reader | 3 |
| `Value_Digest_Reader` | Value_Digest_Read | 2 |
| `Interval_Point_Digest` | Example_Interval_DG_Ctx_Collect | 2 |

The `CFG_Collect_Trace` transitive fan-out of 86 is dominated by placement
imports (see §4), not semantic use.

---

## 3. Category-D theorem-level classification (the "split before deciding" set)

Classification key: **D1** generic generator infra (retain, rename); **D2**
functional activation/keyed-read (restate over `cfg_collect`/`cfg_collect_ctx_act`);
**D3** relational digest (delete); **D4** dead compatibility wrapper (delete after
call sites move).

### `TD_Side_Eff_Cmp_Gen` (42 decls) — **mostly D1**

The generator DG_Framework rides. Body is functional (`gkey`, `cmb`); `cmp`/`gcmp`
enter only via the read side.

| Decl(s) | Class | Action |
| --- | --- | --- |
| `side_cfg_T_eff_cmp`, `side_cfg_T_eff_cmp_seed`, `eq_*`, `traverse_*`, `pull_gk`, `sides_*`, `side_rhs_fold` lemmas, `*_edge_le`, `*_enter_le*`, `*_combine_le` | D1 | retain, drop `_cmp` from names; keep functional `gkey`/`cmb` |
| `side_env_pull_gk_le_cmp`, `side_env_pull_gk_eq_cmp`, `s0_le_side_env_cmp_entry`, `restrict_global_traverse_side_rhs_fold_ctx_le` | D2 | restate the read bound with `gcmp = (=)` |
| `switching_combine_sound(_le)`, `fixed_combine_satisfies_*` | D1 | retain (combine soundness predicate) |
| `side_cfg_T_eff_cmp_collect_sound_gen(_le)` | D1/D2 | **canonical retained theorem**; replace `reads: gcmp ctx (gkey ctx)` premise with exact-key equality; conclusion already `cfg_collect ≤ ⟦side_env σ (v0,ctx)⟧` |

### `TD_Side_Eff_Cmp_Pull` (9 decls) — **D2**

`pull_cmp`, `post_fixpoint_sound_at_cmp_pull`, `cmp_edge_sound`, `cmp_entry_sound`.
Read-pull soundness at a cmp-compatible context. Restate over exact key; the
`cmp` here is the read filter, not concrete.

### `TD_Side_Eff_Cmp_Sound` (15 decls) — **D2 + D3 split**

| Decl(s) | Class | Action |
| --- | --- | --- |
| `head_digest`, `head_digest_DG_*`, `bind_formals_local_invariant` | D2 | retain (call/return realization + formals invariant) |
| `route_read_cmp`, `combine_read_cmp`, `combine_collect_read_cmp*`, `combine_*_cmp_sound`, `*_cmp_le` | D2 | restate over `cfg_collect_ctx_act`; drop `cmp` filter |
| `side_cfg_T_eff_cmp_collect_ctx_sound_semantic`, `collect_ctx_sound_route` | D3-adjacent | these conclude over `cfg_collect_ctx`; **restate over `cfg_collect_ctx_act`** or delete if the activation path already covers them |

### `Clean_RRead_Sound` (20 decls) — **D2, mostly retain**

| Decl(s) | Class | Action |
| --- | --- | --- |
| `clean_edge_tree`, `clean_etf_of_transfer`, `clean_*_eq`, `apply_etf_clean*`, `clean_rread_{nop,assign,assume,assume_not,enter}`, `clean_edge_collect_rread`, `clean_cfg_witness_rread` | D1/D2 | retain (clean-edge read algebra) |
| `clean_cfg_collect_rread(_bound)` | D2 | **retain** — concludes over plain `cfg_collect` (per-key DG plain endpoint material) |
| `clean_ctx_collect_rread(_bound)`, `clean_ctx_collect_rread_head(_bound)` | D2 | restate `cfg_collect_ctx` → `cfg_collect_ctx_act` |

### `Seed_EnterMono_Lift` (3 decls) — **D2, retain**

`enter_mono_point`, `point_route_eq`, `seed_glob_from_point_route`. Functional
enter monotonicity + point routing. No `cmp` in the interface. Feeds the
activation flagship chain; keep, rename theory to a neutral seed/enter home.

### `Digest_Global_Read` (19 decls) — **D3 (delete), one D2 to salvage**

| Decl(s) | Class | Action |
| --- | --- | --- |
| `obs_digest`, `obs_digest_*`, `glob_env_cmp_*`, `combine_*_obs*`, `obs_digest_collect_ctx_sound(_bot)`, `obs_digest_recovers_cmp_collect` | D3 | delete — relational global-read filtering / value-history obs digest |
| `fold_sup_bot_at`, `obs_digest_collapse_shape` | D1? | check for a functional user before deleting; if `fold_sup_bot_at` is pure lattice algebra, move to a neutral lemma home |

---

## 4. `CFG_Collect_Trace` — placement vs semantic importers

Fan-out is 86 transitively but the **direct** importers split cleanly:

| Direct importer | Uses flat-trace symbols? | Verdict |
| --- | --- | --- |
| `Compile_Invariants` | no digest symbols itself, **but re-exports `edge_step`** | **structural re-export dependency** (not placement-only) — see §4a; `Located_Reaches` reaches `CFG_Collect_Trace` only through it. Import restored; relocate `edge_step` in Stage 3. |
| `Constraint_System_Sound` | no digest symbols, **but uses `edge_step`** | **structural shared-def dependency** (not placement-only) — see §4a; relocate `edge_step` first, then retarget |
| `LTR_Def` (retained core) | **yes** — `imports CFG_Collect_Trace` | **structural** — relocate the shared def it consumes (`path`/`cfg_witness`/`alpha_last`) to a neutral home before deletion |
| `Sign_Exec_Sound` | yes (Category B) | Stage 2 rebase to `cfg_collect` |
| `Trace_Analysis_Sound` | yes (Category B, digest + non-digest) | Stage 2 split |
| `Ctx_Collect_Backbone` | yes | folded/deleted in Stage 5 |
| `Example_Trace_Digest_Combine`, `Example_Trace_Digest_ReachingCompat` | yes (Category C) | delete Stage 5 |
| `Voblint` (aggregate) | import list | Stage 6 |

**Action:** the retained `LTR_Def → CFG_Collect_Trace` edge is the single
structural blocker for deleting `CFG_Collect_Trace`. Stage 5 must first inventory
what `LTR_Def` pulls from it and move only the live shared definitions.

### 4a. `edge_step` — shared non-digest helper (relocated to `CFG_Collect` in Stage 3)

**Stage 3 done.** `edge_step` and `edge_collect_single` were moved from
`CFG_Collect_Trace` into `CFG_Collect` (beside `edge_collect`/`edge_collect_member`,
before `edges_collect`). `CFG_Collect` already reached every dependency
(`VIMP_Proc`/`Expr`/`Globals`, `edge_action`), so no cycle. `CFG_Collect_Trace`
re-imports `CFG_Collect` and keeps its digest theorems unchanged.
`Constraint_System_Sound` and `Compile_Invariants` dropped their
`CFG_Collect_Trace` imports; `Located_Reaches`/`Located_LTR` now get `edge_step`
from `CFG_Collect` (full build exit 0). `LTR_Def` keeps its
`CFG_Collect_Trace` import for the trace-specific `call_enter_store`, but its
`edge_step` now resolves to `CFG_Collect` — a candidate follow-up (`call_enter_store`
relocation) noted, out of Stage-3 scope.

Historical context (the pre-Stage-3 situation):

`edge_step` (`edge_action ⇒ store ⇒ store option`, the store-singleton companion
of `edge_collect`) and its bridge `edge_collect_single` lived in
`CFG_Collect_Trace` but are **not** digest machinery. Two retained theories
depended on them:

* **`Constraint_System_Sound`** — its `edge_of_bound` lemma uses `edge_step`
  directly.
* **`Compile_Invariants`** — does *not* use `edge_step` itself, but is the sole
  transitive path by which **`Located_Reaches`** (which proves
  `edge_step_mem_edge_collect` / `cfg_collect_edge_step`) reaches
  `CFG_Collect_Trace`. Dropping the import passed I/Q on `Compile_Invariants`
  (it uses none of those symbols) but **broke the batch build** at
  `Located_Reaches`/`Located_LTR`. Lesson: an import can be a load-bearing
  re-export even when the file itself uses nothing from it — only the full build
  catches this. Import restored; revisit at Stage 3.

Detail on the `Constraint_System_Sound` use — its `edge_of_bound` lemma consumes
`edge_step`:

```text
Constraint_System_Sound
    └── needs edge_step
            └── currently located in CFG_Collect_Trace
```

`edge_step` is the **generic single-edge concrete transfer** (`edge_action ⇒
store ⇒ store option`), the store-singleton companion of `edge_collect`. It is
*not* digest machinery: it does not touch `trace_witness`, `cfg_collect_trace`,
`cfg_collect_ctx`, `cmp`, or digest semantics. So this is a **structural
shared-definition dependency**, not an abort condition and not a digest coupling.

| Field | Value |
| --- | --- |
| previous classification | placement-only (incorrect) |
| corrected classification | structural shared-definition dependency |
| consumed symbol | `edge_step` (+ `edge_collect_single` bridge lemma) |
| semantic role | generic single-edge concrete transfer relation |
| action | move `edge_step` and its non-trace lemmas to `CFG_Collect` (near `edge_collect`/`cfg_witness`), then retarget `Constraint_System_Sound`'s import |
| stage | Stage 3 shared-infrastructure extraction, before deleting `CFG_Collect_Trace`; do **not** create a new theory for one def unless the move into `CFG_Collect` would introduce an import cycle |

---

## 5. Category A / B / C confirmation (files exist on disk)

* **Category C deletion candidates present:** `Example_Trace_Digest_Combine`,
  `Example_Trace_Digest_Precision`, `Example_Trace_Digest_ReachingCompat`,
  `Exec_Sign_Cmp_Keyed_DG_Run`, `DG_Route_Soundness`, `Value_Digest_Reader`.
* **Category B present:** `Example_Proc_Call`, `Example_Side_Branch_Calls`,
  `Example_Mixed_Flow_Sign`, `Example_Interval_Loop_Coverage`,
  `Example_IMP2_Coverage`, `Sign_Exec_Sound`, `Mixed_Flow_Sound`,
  `Trace_Analysis_Sound`.

---

## 6. Preservation ledger (named endpoints that must survive)

| Guarantee | Current theorem | Post-migration form |
| --- | --- | --- |
| plain collecting soundness | `side_cfg_T_eff_cmp_collect_sound_gen` (concl. `cfg_collect ≤ …`) | same theorem, `gcmp` premise → exact-key equality, `_cmp` renamed |
| executable Sign plain | `Exec_Sign_DG_Run.dgEx_collect_sound` (`cfg_collect ⊆ sign_dg_gamma`) | unchanged endpoint; imports re-pointed |
| executable interval flagship | `Example_Interval_DG_Flagship.flagship_collect_sound` (`cfg_collect ⊆ ivl_dg_gamma`) | unchanged endpoint |
| per-key DG plain endpoint | `dg_postfix_c_collect_sound` (`cfg_collect g S0 v ⊆ dg_gamma_c σ ctx v`) | **direct functional replacement required** — keyed D/G view covers plain collecting, non-digest name |
| activation collecting | `cfg_collect_ctx_act … v c ⊆ γ(meaning_ctx σ v c)` (via `Activation_Backbone`) | unchanged — already functional |
| solver chain | computed → partial/post → abstract post → collecting | unchanged |
| call/return | functional callee ctx, caller restore, param transfer, destination-aware returns | unchanged |

---

## 7. Stage-2 slices — status and order

**Slice 1 (commit `06aeb6ed`, partially reverted):**

* `Compile_Invariants` — import drop **reverted** (§4a): it re-exports `edge_step`
  to `Located_Reaches`; the batch build caught the break. Restore is committed.
* `Example_IMP2_Coverage` — `loop_head_x_pos` rebased off `cfg_collect_trace`
  onto plain `cfg_collect` via `post_fixpoint_sound`; `Trace_Analysis_Sound`
  import dropped; store conclusion preserved.
* `Constraint_System_Sound` — **held**: genuine `edge_step` dependency (§4a),
  deferred to the Stage-3 shared-def extraction rather than expanded into here.

**Slices 2–4 (done):**

* `Example_Interval_Loop_Coverage` (`235e0e7c`) — `loop_head_x_bounded` → `cfg_collect`
  via `post_fixpoint_sound` (`ivl_sound_tf`); import + comments updated.
* `Example_Proc_Call` (`966c669d`) — `main_prog_interval_analysis` → `cfg_collect`;
  interprocedural `combines` handled by `is_post_fixpoint`, no witness structure.
* `Example_Side_Branch_Calls` (`4cd0d5a3`) — redundant trace corollary
  `ec_certified_sound_trace` replaced by store-level `ec_certified_sound_store`
  over `cfg_collect` (derived from the pre-existing `ec_certified_sound`).
  `Sign_Exec_Sound` import retained (its own trace dependency is item 5).

**`Example_Mixed_Flow_Sign` — deferred (coupled to item 6).** Its two corollaries
wrap `mixed_flow_analysis_sound` / `mixed_flow_analysis_optimal` (in
`Mixed_Flow_Sound`), which are stated over `cfg_collect_trace` + `last tr` but
**already prove the pure bound `cfg_collect g S (cfg_exit g) ≤ ⟦side_env σ …⟧`
internally** (`Mixed_Flow_Sound.thy:49/89`) before wrapping it in `alpha_last`
trace phrasing. Clean rebase = promote that internal `cfg_collect` bound to the
theorem statement, then re-point the example. This is generic-soundness work:
migrate item 4 **together with** item 6, not before it.

**Established rewrite pattern** for remaining Category-B users:

```text
tr ∈ cfg_collect_trace g S v   ⊢  P (last tr)
    ↓  (drop the trace; take the reaching store directly)
s ∈ cfg_collect g S v          ⊢  P s
    ↓  (discharge via)
sound_transfer.post_fixpoint_sound  →  cfg_collect g S v ≤ ⟦env v⟧
    ↓  unfolding gamma_state_def
per-variable gamma membership
```

**Remaining order (leaf examples first, generic soundness last):**

1. ~~`Example_Interval_Loop_Coverage`~~ — done (`235e0e7c`)
2. ~~`Example_Proc_Call`~~ — done (`966c669d`)
3. ~~`Example_Side_Branch_Calls`~~ — done (`4cd0d5a3`)
4. `Example_Mixed_Flow_Sign` — **deferred**, migrate with item 6
5. `Sign_Exec_Sound` (generic)
6. `Mixed_Flow_Sound` (generic; expose internal `cfg_collect` bound) + `Example_Mixed_Flow_Sign`
7. split `Trace_Analysis_Sound` (generic)

Each edit: I/Q inner loop, empty error diagnostics per file; full build only at
the Stage-2 gate. Leave `edge_step` relocation for Stage 3, not mixed into
Category-B rebasing.

---

## 9. Stage-4 audit — `cmp`/`gcmp` functional-extraction census

**Headline: the retained analysis path is already functional.** The
executable/DG/activation soundness path carries **no live relational `cmp`/`gcmp`
interface**. Verified:

* `DG_Framework` and `DG_Soundness` contain **0** `gcmp`/`side_env_cmp` references.
* The retained DG generator is `side_cfg_T_eff_cmp` / `side_cfg_T_eff_cmp_seed_dg`,
  parameterised by `gkey` (functional context key) and `cmb` (combine) — **no `cmp`
  parameter**. The `_cmp` in the name is legacy, not a relation.
* Flagships chain through DG-native endpoints (`ivl_dg_post_solution_collect_sound`,
  `flagship_collect_sound`), never a relational theorem.
* `DG_Context_Soundness` / `Sign_DG` mention `gcmp` only in **comments** (the
  `gkey=id, gcmp=(=)` diagonal is implemented functionally).

**Classification of the entire relational `cmp`/`gcmp` surface** (all in the
deletion cluster — none on the retained path):

| Item | Location | Class | Fate |
| --- | --- | --- | --- |
| `side_cfg_T_eff_cmp_collect_sound_gen`, `_sound`, `_sound_eq`, `_ctx_sound` | `TD_Side_Eff_Cmp_Gen` | **dead relational scaffolding** — no rule-level users anywhere | delete with the relational cluster (Stage 5) |
| `side_cfg_T_eff_cmp_collect_ctx_sound_semantic` + `route_read_cmp`/`combine_read_cmp` | `TD_Side_Eff_Cmp_Sound` | relational, feeds Category-C digest reads | Stage 5 |
| `pull_cmp`, `post_fixpoint_sound_at_cmp_pull`, `cmp_edge_sound`, `cmp_entry_sound` | `TD_Side_Eff_Cmp_Pull` | relational support for the above | Stage 5 |
| `glob_env_cmp`, `side_env_cmp` (defs) + `read` lemmas | `Global_Cmp_Read` | relational read defs; used only by digest + the dead theorems | Stage 5 |
| `obs_digest*`, `glob_env_cmp_*` | `Digest_Global_Read` | Category-C digest | Stage 5 |
| `read_ctx_*`, `ln (=) …` reads | `Example_Global_Ctx_Read_Precision` | Category-C digest example | Stage 5 |

**Functional core to retain** (already used by `DG_Framework`, no `cmp`): the
generator algebra in `TD_Side_Eff_Cmp_Gen` — `side_cfg_T_eff_cmp`,
`side_cfg_T_eff_cmp_seed`, `side_cfg_T_eff_cmp_seed_dg`, `pull_gk`, the
`traverse`/`sides`/`side_rhs_fold` lemmas, `*_edge_le`/`*_enter_le`/`*_combine_le`,
`switching_combine_sound`. `TD_Side_Eff_Cmp_Gen` is therefore a **mixed file**
(functional generator + dead relational theorems).

**Part-C decision (no code change made):** the functional extraction the goal
envisioned is already realised in-tree — the retained path is functional and
exposes no `cmp`/`gcmp` parameter. The only residual is splitting the *dead*
relational scaffolding out of the mixed `TD_Side_Eff_Cmp_Gen`. That split is
large, touches a core file feeding every DG flagship, and the scaffolding is dead
* Category-C-coupled, so it is safest performed **as part of the Stage-5 deletion**
of the relational/digest cluster rather than as a speculative Stage-4 refactor.
Renaming the functional generator off `_cmp` is likewise best done at that point
(one mechanical rename, all callers updated together). No retained flagship needs
either change to be `cmp`-free today.

## 8. Open items for the next stage

* Confirm exactly which definition `LTR_Def` consumes from
  `CFG_Collect_Trace` (§4) — read via I/Q before Stage 5. **(Done in Stage 4A:
  it was `call_enter_store`, now relocated to `CFG_Collect`; `LTR_Def`
  no longer imports `CFG_Collect_Trace`.)**
* Verify `dg_postfix_c_collect_sound` has a functional keyed replacement path
  before deleting `DG_Route_Soundness` / the relational `Local_DG` endpoint.
* Decide neutral destination-theory names for the D1/D2 extractions
  (plan suggests `Functional_Context_Read`, `TD_Side_Keyed_Gen`,
  `TD_Side_Keyed_Sound`, `Seed_Enter_Lift`, `Activation_Read_Sound`).
