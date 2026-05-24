# Post-Migration Cleanup Plan

> **Landed 2026-05-24** on branch `post-migration-cleanup`. Prior items (deleted
> `Direct_Equations`, `TD_Total`, AST `collect`, premise rephrasing to `cfg_collect`)
> were already on `main`. This pass: **CFG_Collecting split**, **Phase 3 partial
> option (c)** (`terminates_to` removed; direct `small_step_preserves_runs_to`;
> `runs_to_*` intro rules kept), **Phase 4 partial** (`to_cfg_mk`,
> `cfg_path_sub_offset_into`, `edges_collect_memberE`, `cfg_path_NilE`/`ConsE`,
> apply→`by` in Path / Collecting_Core / Edges_Collect / Path_Bridge).
> **HOL_IMP_Countable:** kept separate (arity-fact clash if folded into `IMP2_Syntax`).
>
> **Current architecture:** `docs/PROOF_OVERVIEW.md`.

**Status:** Phases 0–3 partial + Phase 4 partial landed; Phase 5 docs mostly synced;
Phase 6–7 optional. `edges_collect_append [simp]` and `to_cfg_simps` bundle deferred
(batch loop / syntax).
**Branch:** `post-migration-cleanup`.
**KB mirror:** [`goblint-formalization-kb` → `wiki/concepts/spec-architecture.md`](https://github.com/ManuelLerchner/goblint-formalization-kb/blob/main/wiki/concepts/spec-architecture.md) (locked architecture + thesis sentence).
**Predecessor:** [`BIG_STEP_REMOVAL.md`](BIG_STEP_REMOVAL.md) (landed 2026-05-24 on `main`). With big-step gone, the residual cost is file layout, an oversized `CFG_Collecting.thy`, and proof boilerplate that automation should absorb. This plan trims ~900 LOC and aligns the API with the long-term architecture below.

### Locked decisions (2026-05-24)

| Topic | Decision |
|---|---|
| **Spec architecture** | **`cfg_collect` is the only spec.** Canonical soundness: `pipeline_invariant_sound` (all program points) and `pipeline_sound_path` (path-shaped, no termination). **`runs_to` is definitional exit sugar** (`runs_to_def`), not a second operational semantics. Small-step is the human/executable view; link once via `runs_to_iff_small_step`. |
| `HOL_IMP_Countable.thy` | **Delete.** Fold upstream `Countable` instances into `IMP2_Syntax` (or drop if unused after audit). |
| Reverse bridge (Phase 3) | **Try option (c) first:** direct `small_step → cfg_collect` induction, deleting `terminates_to` + all seven `runs_to_*` intro rules. **Fallback:** keep the current bridge unchanged if (c) fails after a bounded spike (~1 day). Do **not** maintain parallel `runs_to_*` intro algebra alongside compound `cfg_path_*_iff` work. |
| `collect` API | **Delete** (`collect`, `collect_empty`, `collect_mono`, `runs_to_iff_mem_collect`) unless a paper explicitly needs set-valued AST collecting. |
| Examples | Keep all; operational reasoning stays `→*` then `small_step_runs_to`. |
| Spec / headline theorems | **No renames** on the soundness chain (`pipeline_invariant_sound`, `pipeline_sound_path`, `pipeline_sound_runs_to`, `goblint_sign_sound`, `runs_to_iff_small_step`). Premises in `TD_Soundness` / `Constraint_System_Sound` may be rephrased to `cfg_collect` (equivalent by `runs_to_def`) in Phase 6. |
| Big-step | **Do not resurrect.** No new inductive `runs_to`; abbreviation + one bridge only. |

## Context: what the small-step migration bought us

Concrete gains from the small-step + `runs_to` switch (now landed):

1. **One semantics, not two.** Big-step inductive + `code_pred` + `big_step_determ` + `big_to_small` / `small_to_big` / `small_step_big_step_eq` bridge all gone. ~400–500 LOC removed across deleted `IMP2_Semantics.thy`, deleted `IMP2_Collecting.thy`, and the `big_step_cfg_path` / `compile_path_big_step` / `cfg_collect_exit_eq_collect` scaffolding in `CFG_Collecting.thy`.
2. **The spec is what the analyzer approximates.** `runs_to c s t` ≡ `t ∈ cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))`. Soundness theorems no longer need a separate big-step → `cfg_collect` bridge — `pipeline_sound_runs_to` is a definitional unfold of `pipeline_invariant_sound`.
3. **Non-termination is expressible.** Big-step cannot observe diverging programs; the `(c,s) ⇒ t` premise vacuously discharges everything. Small-step `→*` + per-pp `pipeline_sound_path` gives genuine safety at intermediate points of infinite loops — `Example_NonTerminating_Safe.thy` proves `x = 10` after `x := 10; while True do …` despite the program never returning.
4. **Per-pp is the canonical theorem; exit-only is the corollary.** `pipeline_invariant_sound` and `pipeline_sound_path` are primary; `pipeline_sound_runs_to` is a short definitional corollary.
5. **`runs_to` names exit-projected `cfg_collect`, not big-step.** Downstream theorems still *read* IMP-shaped (`runs_to c s t`), but the mathematical spec is CFG collecting. Phase 6 aligns proof obligations with that story.

**Cost paid:** the small-step → `runs_to` reverse bridge (`small_step_runs_to` via `terminates_to`) — ~570 LOC of structured operational scaffold at the tail of `CFG_Collecting.thy`. Phase 3 deletes most of it; Phase 6 stops treating `runs_to` as the spine of the soundness chain.

**What did not change:** CFG construction, the path/edges bridge, solver, domains, transfer-function soundness.

This cleanup plan addresses the *residual* cost: dead files, the elephant file, manual proof boilerplate, and API framing that still looks like a second (big-step-shaped) semantics.

---

## Long-term architecture (locked)

**Thesis sentence (use in overview / supervision):**

> Soundness is stated against CFG collecting semantics at **every** program point (`cfg_collect`). The analyzer's post-fixpoint soundly over-approximates that semantics. Terminating IMP runs correspond to exit reachability (`runs_to` / small-step to `SKIP`); partial and non-terminating behaviour is covered by the path-based theorem without a final store.

### Layering

```text
┌─────────────────────────────────────────────────────────────┐
│  Soundness chain (primary)                                   │
│    cfg_collect (to_cfg c) S v   —  all program points v      │
│    cfg_path + edges_collect     —  path-shaped membership    │
│    pipeline_invariant_sound, pipeline_sound_path,            │
│    post_fixpoint_sound, td_analyse_post_fixpoint             │
└─────────────────────────────────────────────────────────────┘
         ▲                              ▲
         │ runs_to_def                  │ compile_path_small_step,
         │                              │ path_sound_cfg_collect
┌────────┴────────┐            ┌────────┴────────┐
│  Sugar (exit)   │            │  Operational    │
│  runs_to c s t  │◄──────────►│  (c,s) →*       │
│  (definitional) │  runs_to_  │  (SKIP,t)       │
│                 │  iff_small_│                 │
│                 │  step once │                 │
└─────────────────┘            └─────────────────┘
         ▲
         │ examples, prose, pipeline_sound_runs_to,
         │ goblint_sign_sound (exit-shaped headline OK)
```

| Layer | Role | Where it lives |
|---|---|---|
| **Spec** | What Goblint approximates | `cfg_collect`, `cfg_edges_collect`, `cfg_path` + `edges_collect` |
| **Soundness** | Post-fixpoint ⊆ γ ∘ env at every `v` | `pipeline_invariant_sound`, `Constraint_System_Sound.post_fixpoint_sound` |
| **Path soundness** | Per-pp, **no** termination premise | `pipeline_sound_path`, `Example_NonTerminating_Safe` |
| **Operational** | Human / executable semantics | `IMP2_SmallStep`, `code_pred small_step` |
| **Bridge** | One pack, proved once | `runs_to_small_step`, `small_step_runs_to`, `runs_to_iff_small_step` |
| **Sugar** | Source-level exit wording | `runs_to` definition; `pipeline_sound_runs_to` as corollary |

### Use `runs_to` / do not use `runs_to`

| **Use `runs_to`** | **Do not use `runs_to` as primary premise** |
|---|---|
| Examples: prove `→*`, apply `small_step_runs_to` | Core proofs of `pipeline_invariant_sound`, `pipeline_sound_path` |
| Thesis prose: "program terminates in store `t`" | `TD_Soundness` / `Constraint_System_Sound` (Phase 6: `cfg_collect` or `runs_toD` at proof start) |
| `pipeline_sound_runs_to`, `goblint_sign_sound` (exit headline OK) | New structured `runs_to_Seq` / `runs_to_While` intro rules after Phase 3 |
| Sanity checks (`Example_CFG_Collecting_Equiv`) | Second operational semantics (no inductive `runs_to`) |

### What we explicitly reject long term

- **Big-step** or any duplicate IMP-level collecting semantics + bridge.
- **Exit-only as the default mental model** — same blind spot as `(c,s) ⇒ t`; use `pipeline_sound_path` for loops.
- **`(c,s) →* (SKIP,t)` as the main soundness premise everywhere** — correct operationally, but noisy; one equivalence pack to `cfg_collect` suffices.
- **Parallel proof worlds** — compound work on `cfg_path_*_iff` (see `PROOF_SIMPLIFICATION.md`, rebased on small-step) **plus** `runs_to_*` intro algebra.

### Mapping to phases

| Architecture item | Phase |
|---|---|
| Delete `collect` API, dead lemmas | 1 |
| Thin reverse bridge (option c) | 3 |
| Automation on CFG path layer | 4 |
| Docs: one diagram, thesis sentence | 5 |
| Demote `runs_to` in TD / Constraint premises | 6 |
| Compound `cfg_path_*_iff` (optional follow-up) | 7 or post-cleanup issue |

---

## Baseline (measured 2026-05-24, `main`)

```
total tracked LOC     7435  (32 .thy files under src/)
on soundness chain    ~5500 (~75%)
sorries               15 — Direct_Equations 7, TD_Total 8; 0 on main chain
largest file          CFG_Collecting.thy = 2142 LOC, 79 declarations (4× next-largest)
apply scripts         52 total — IMP2_to_CFG 15, CFG_Collecting 14, IMP2_SmallStep 13, Sign_Domain 3
automation attrs      sparse in CFG layer — CFG_Collecting has 4 [simp] lemmas; CFG_Path has 11 tagged rules
build time            ~22s (warm AFP heaps)
session imports       Direct_Equations (umbrella only); TD_Total orphaned (not imported anywhere)
ROOT drift            ROOT lists `Scratch` theory but `src/Scratch.thy` is not tracked — fix in Phase 1
```

### LOC by layer

| Layer | Files | LOC | Necessity |
|---|---|---|---|
| IMP2 (`Syntax`, `SmallStep`) | 2 | 272 | **core** — AST + small-step (`HOL_IMP_Countable` deleted in Phase 1) |
| CFG (`Def`, `Path`, `IMP2_to_CFG`, `Collecting`, `GraphViz`) | 5 | 3024 | **core** — `Collecting` dominates |
| Domains (`Abstract`, `Sign`, `Interval`) | 3 | 1013 | **core** (Sign) + **stretch** (Interval) |
| Equations (`Constraint_System`, `Constraint_System_Sound`, `Direct_Equations`) | 3 | 952 | **core** (952−280) + **quarantine** (Direct_Equations 280) |
| Solver (`TD_Interface`, `TD_Soundness`, `TD_Total`) | 3 | 769 | **core** (622) + **orphan** (TD_Total 147) |
| Pipeline | 1 | 420 | **core** |
| Examples | 5 | 829 | **keep all** (user instruction) |
| Umbrella (`Goblint_Formalization.thy`) | 1 | 139 | **core** |

### `CFG_Collecting.thy` internal seam (line ranges)

| Block | Lines | ~LOC | Content |
|---|---|---|---|
| `edge_collect` / monotonicity | 1–141 | 141 | fundamental collecting fold |
| `cfg_edges_collect` + path↔lfp | 142–1199 | 1060 | Seq/If/While structural path lemmas; densest block |
| `compile_path_small_step` | 1200–1523 | 324 | CFG-path → small-step (forward bridge) |
| `runs_to` interface | 1524–1572 | ~35 | `runs_to_def`, `runs_to_small_step` (collect API deleted Phase 1) |
| Reverse bridge + intro algebra | 1573–2142 | 570 | `runs_to_*` intro rules, `terminates_to`, `small_step_runs_to` |

Natural split boundaries: after line 141, after 1199, after 1523, after 1572 (or after Phase 3 thinning).

---

## Goals

1. **Lock the architecture** — `cfg_collect` primary; `runs_to` sugar; one small-step bridge (see § Long-term architecture).
2. **Delete everything not used today** — including `HOL_IMP_Countable.thy`, `collect` API, quarantined theories (examples kept).
3. Split `CFG_Collecting.thy` along its natural seam.
4. **Replace the reverse bridge (option c):** prove `small_step_runs_to` by direct `small_step → cfg_collect` induction; delete `terminates_to` and all seven `runs_to_*` intro rules. Fall back to the current bridge if the spike fails.
5. **Automation sweep:** declare missing `[simp]` / `[intro]` / `inductive_cases` rules, replace repeated boilerplate with helper combinators.
6. **Align downstream API (Phase 6):** soundness-chain premises state `cfg_collect` where possible; keep theorem names and mathematical content.

Non-goal: renaming headline theorems; resurrecting big-step or Direct_Equations.

## Target end state

- **Documentation and comments** state clearly: spec = `cfg_collect`; `runs_to` = exit projection; canonical soundness = `pipeline_invariant_sound` + `pipeline_sound_path`.
- `CFG_Collecting.thy` ≤ ~700 LOC; structural compound-path lemmas and reverse-bridge scaffold in separate files.
- `Direct_Equations.thy` and `TD_Total.thy` deleted; "Route B" framing gone from the umbrella.
- `ROOT` no longer references missing `Scratch` theory.
- `HOL_IMP_Countable.thy` deleted; upstream `Countable` instances live in `IMP2_Syntax` (or are gone if nothing needs them).
- **`collect` API removed**; only `runs_to` (+ `runs_to_def`) as optional exit sugar.
- Reverse bridge: either **~50 LOC direct induction** (option c landed) or **unchanged ~570 LOC scaffold** (fallback). In both cases `small_step_runs_to` and `runs_to_iff_small_step` survive at the theorem level.
- `terminates_to`, `runs_to_*` intro rules, and `runs_to_imp_path` deleted if option c lands.
- `TD_Soundness` / `Constraint_System_Sound`: terminating-run premises use `cfg_collect` membership (or `runs_toD` once at proof start), not a parallel operational story.
- `pipeline_sound_runs_to` remains a **short corollary** of `pipeline_invariant_sound` (definitional unfold only).
- `to_cfg_compile` used consistently via a `to_cfg_simps` bundle + path-lifting combinators.
- `Goblint_Formalization` session builds in ≤ current 22s with the same exit criteria as today.
- `isabelle build` green; **0 sorries** on any tracked file.

## Audit summary (consumer scan)

| File / artefact | Importers | Verdict |
|---|---|---|
| `IMP2/HOL_IMP_Countable.thy` (21 LOC) | `IMP2_Syntax` | **delete** — two `instance … countable` lines for upstream `AExp.aexp`/`BExp.bexp`. Relocate into `IMP2_Syntax` after importing `"HOL-IMP.AExp"` / `"HOL-IMP.BExp"` directly (drop the separate-theory import). If Isabelle reports the documented arity-fact name clash (`arity_countable_aexp`), try: (i) instances before our `datatype aexp` block, (ii) `instantiation` with fully qualified type names, (iii) ask whether upstream instances are still needed — our `aexp`/`bexp`/`com` instances may suffice and the upstream ones can go entirely. Build gate in Phase 1. |
| `Equations/Direct_Equations.thy` (280 LOC, 7 sorries) | umbrella only ("Route B") | **delete** — no proven theorem, no downstream consumer; `direct_eq_cfg_analyse` still `sorry` |
| `Solver/TD_Total.thy` (147 LOC, 8 sorries) | **none** | **delete** — orphan; not in umbrella, not imported anywhere |
| `runs_to_*` intro rules (7 rules, ~420 LOC) + `terminates_to` (~105 LOC) | reverse bridge only | **delete** if option (c) lands (Phase 3); keep if fallback |
| `mem_collect_iff_runs_to` | **none** (defined, never referenced) | **delete** in Phase 1 |
| `collect`, `collect_empty`, `collect_mono`, `runs_to_iff_mem_collect` | **none** in `src/` proofs | **delete** in Phase 1 — redundant with `runs_to_def` |
| `cfg_collect_le_edges_collect` | internal (`CFG_Collecting:1187`) | **keep** — used in path↔lfp bridge |
| `runs_to_imp_path` | intro algebra only (6 call sites) | **delete** if option (c) lands; keep if fallback |
| `CFG/CFG_GraphViz.thy` (118 LOC) | `Goblint_Formalization`, `Example_GraphViz` | **keep** — backs an example |
| `Examples/*` | — | **keep all** (user instruction) |

---

## Automation audit

The dominant cost driver is **repeated manual unpacking**, not hard mathematical content. Measured hotspots:

### Current automation surface

| Mechanism | Count | Where |
|---|---|---|
| `[simp]` / `[intro]` / `[elim]` in CFG layer | 20 tagged lemmas total | `CFG_Path` 11, `CFG_Def` 5, `CFG_Collecting` 4 |
| `inductive_cases` | 6 rules | `CFG_Path.stepE`; `IMP2_SmallStep` Skip/Assign/Seq/If/While |
| `apply` scripts | 52 lines | see baseline |
| Manual `by (rule to_cfg_compile)` | **17 sites** | `CFG_Collecting` (compile_path + intro rules) |
| Manual `by (simp add: edges_collect_append)` | **12+ sites** | `CFG_Collecting` — lemma exists but is **not** `[simp]` |
| Manual `cfg_path_append[OF cfg_path_append[OF …]]` | **6 nested chains** | intro rules + `compile_path_small_step` |
| Manual `cfg_path_mono_edges` + subset proof | **7 sites** | every compound intro rule |

Note: `to_cfg_compile` already exists as an `obtains` lemma (`CFG_Collecting.thy:211–218`). Phase 4 does **not** need to invent it — it needs to stop re-proving the same four equations at every call site.

### Priority automation targets

#### A. Missing attributes (add one at a time; watch build time)

| Lemma | File | Current | Proposed | Manual use count |
|---|---|---|---|---|
| `edges_collect_append` | Collecting | none | `[simp]` (confirm direction; no loop) | 12+ |
| `edges_collect_mono_strong` | Collecting | none | `[mono_set]` | several |
| `edge_collect_mono` | Collecting | none | `[mono_set]` | several |
| `cfg_collect_F_mono` / `cfg_collect_mono_S` | Collecting | none | `[mono]` | lfp proofs |
| `cfg_path_append` | Path | none | `[intro]` | 6 nested chains |
| `cfg_path_mono_edges` | Collecting | none | `[intro]` | 7 sites |

#### B. Missing `inductive_cases`

Only `cfg_path.stepE[elim]` exists for `cfg_path`. Add:

```isabelle
inductive_cases cfg_path_NilE[elim!]:  "cfg_path g v [] u"
inductive_cases cfg_path_ConsE[elim]:    "cfg_path g v ((a, w) # es) u"
```

Expected effect: `cases rule: cfg_path.cases` blocks in `cfg_path_Seq_split` and friends shrink to `auto elim: cfg_path_ConsE`.

For `small_step`, shape-pinned elim rules are safe where branching rules are not:

```isabelle
inductive_cases SeqSkipSE[elim!]: "(SKIP ;; c2, s) \<rightarrow> ct"
```

(`SeqSE` / `WhileSE` stay `[elim]` — they branch.)

#### C. `to_cfg_simps` bundle

Collect `to_cfg_def`, `cfg_entry_mk_cfg`, `cfg_exit_mk_cfg`, `edges_mk_cfg`, `compile.simps` into a named simpset. Use `from c to_cfg_compile obtain …` at intro-rule heads instead of repeating four equations. **17 call sites** → one-liner pattern.

#### D. Compound-CFG path lifting combinators

Package the repeated ritual:

```isabelle
have "edges (to_cfg c_sub) \<subseteq> edges (to_cfg c_compound)" …
hence "cfg_path (to_cfg c_compound) …" using cfg_path_mono_edges …
```

into one lemma per shape (`cfg_path_into_Seq_left`, `_Seq_right`, `_If_then`, `_If_else`, `_While_body`). Expected saving: ~15 LOC × 7 intro rules + ~10 LOC × 4 `compile_path_small_step` cases ≈ **145 LOC**.

#### E. Apply-script conversion

Files with apply blocks that are already one-liner `by auto` candidates:

| File | apply count | Action |
|---|---|---|
| `IMP2_to_CFG.thy` | 15 | convert to `by (induction …) auto` where possible |
| `CFG_Collecting.thy` | 14 | same |
| `IMP2_SmallStep.thy` | 13 | same |
| `Sign_Domain.thy` | 3 | same |

Target: apply count ≤ 5 session-wide.

---

## Phase plan

### Phase 0 — branch + baseline (½ day)

1. Branch **`post-migration-cleanup`** from `main` (big-step removal already merged).
2. Record baseline: `wc -l`, sorry inventory, build time — **done in this doc**.
3. Confirm consumer table above; capture drift.

**Exit:** branch exists; baseline committed in this doc.

### Phase 1 — delete unused (½ day)

1. **Delete `Solver/TD_Total.thy`** — no importers; 8 sorries.
2. **Delete `Equations/Direct_Equations.thy`** — only the umbrella imports it; remove import from `Goblint_Formalization.thy`; 7 sorries gone.
3. **Delete `IMP2/HOL_IMP_Countable.thy`** — remove import from `IMP2_Syntax.thy`; relocate or drop the two upstream `instance … countable` declarations (see audit table). Update the comment block at `IMP2_Syntax.thy:64–69`.
4. **Update `Goblint_Formalization.thy` header comment** — strip "Route B Direct" framing and `direct_eq_cfg_analyse` reference.
5. **Fix `ROOT`** — remove `Scratch` entry (theory file not tracked).
6. **Sweep on-disk junk:** `find src -name '*~' -delete`; `find src -name '#*#' -delete`.
7. **Delete dead lemmas:** `mem_collect_iff_runs_to`, `collect` / `collect_empty` / `collect_mono`, `runs_to_iff_mem_collect` (zero proof consumers; see architecture §).
8. **Comment pass on `CFG_Collecting.thy` header** — spec = `cfg_collect`; `runs_to` = exit sugar (not operational semantics).

**Exit:** `rg -c '^\s*sorry' src/` returns **0**; ~490 LOC gone; build green.

### Phase 2 — split CFG_Collecting.thy (1 day)

Split `CFG_Collecting.thy` (2142 LOC) along the seam in the table above:

```
CFG_Edges_Collect.thy          ~ 250 LOC
  edge_collect / edges_collect fold, monotonicity, offset/append lemmas

CFG_Collecting.thy             ~ 280 LOC
  cfg_collect lfp + monotonicity in cenv and S
  runs_to definition + runs_to_def (no collect API)
  cfg_edges_collect, path↔lfp equivalence helpers

CFG_Compound_Paths.thy         ~ 800 LOC
  Seq / If / While structural path lemmas
  cfg_path_Seq_split, cfg_path_If_split, cfg_path_While_loop_peel, etc.

CFG_Path_Bridge.thy            ~ 350 LOC
  cfg_collect_eq_cfg_edges_collect
  compile_path_small_step
  path_sound_cfg_collect

CFG_Runs_To_Bridge.thy         ~ 50–200 LOC (after Phase 3)
  runs_to_small_step, small_step_runs_to, runs_to_iff_small_step
  option (c): direct small_step → cfg_collect proof (~50 LOC)
  fallback: terminates_to + bridge proof (~200 LOC, current scaffold minus intro rules)
```

Import chain: `Edges_Collect → Collecting → Compound_Paths → Path_Bridge → Runs_To_Bridge`.

Mechanical cut+paste at `paragraph`/`subsection` boundaries; build after each split.

**Exit:** five files; no file > 1000 LOC; no theorem rename; build green.

### Phase 3 — reverse bridge spike: option (c) (1 day, bounded)

**Goal:** replace the ~570 LOC scaffold (`runs_to_*` intro rules + `terminates_to` + `terminates_to_imp_runs_to`) with a **direct proof** of:

```isabelle
lemma small_step_runs_to:
  "(c, s) \<rightarrow>* (SKIP, t) \<Longrightarrow> runs_to c s t"
```

by induction on the small-step star (or on `small_step` with a star wrapper), unfolding `runs_to_def` to show `t ∈ cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))`.

**Approach sketch:**

1. Induction on `(c,s) \<rightarrow>* (SKIP, t)` (or rule induction on `star`).
2. Base: `c = SKIP`, `t = s` — trivial path at entry.
3. Step: one small-step transition; use **`compile_path_small_step`** (forward bridge, already proved) to get a CFG path fragment, then **`path_sound_cfg_collect`** / membership in the collecting semantics.
4. **WHILE case** is the risk: needs a peel lemma relating one loop iteration to a CFG path segment. Reuse **`cfg_path_While_loop_peel`** from the compound-paths block rather than rederiving from scratch.
5. IF / SEQ cases should compose via existing path append infrastructure.

**Delete on success:**

- `paragraph "Structured intro rules for runs_to"` (lines ~1608–2032): all seven `runs_to_*` lemmas
- `paragraph "Internal evaluation predicate"` (lines ~2035–2127): `terminates_to` inductive + helpers
- `terminates_to_imp_runs_to`, `runs_to_imp_path`, and related proof-only lemmas

**Keep unchanged at theorem level:** `small_step_runs_to`, `runs_to_small_step`, `runs_to_iff_small_step`.

**Fallback (explicit):** if WHILE or compound-command cases do not close within the bounded spike (~1 day), **revert Phase 3 on the branch** and keep the current bridge verbatim. Do not ship a partial bridge. Record outcome in this doc (`option c: landed | fallback`).

| Outcome | LOC removed | `CFG_Runs_To_Bridge.thy` size |
|---|---|---|
| Option (c) lands | ~525 | ~50 |
| Fallback | 0 | ~200 (current, possibly split only) |

**Exit (either outcome):** `small_step_runs_to` and `runs_to_iff_small_step` proved; build green; `Example_NonTerminating_Safe` and `Goblint_Formalization.example_swap_runs_to` still check.

### Phase 4 — automation sweep (1 day)

Execute targets A–E from the automation audit above. Order:

1. Add `inductive_cases` for `cfg_path` (low risk).
2. Add `[simp]`/`[intro]`/`[mono]` attributes one at a time; `-v -v` build per add.
3. Declare `to_cfg_simps`; collapse 17 `to_cfg_compile` call sites.
4. Introduce path-lifting combinators; refactor **`compile_path_small_step`** (and intro rules **only if Phase 3 fallback**).
5. Convert remaining apply scripts.

**Exit:** `CFG_Compound_Paths.thy` shrinks ~150 LOC; apply count ≤ 5. Intro-rule LOC target applies only on fallback — if option (c) lands, skip step 4 intro-rule refactor.

### Phase 5 — wire docs (½ day)

1. `isabelle build` green within ≤ 25s.
2. Sorry count = 0.
3. Headline lemma names unchanged: `pipeline_invariant_sound`, `pipeline_sound_path`, `pipeline_sound_runs_to`, `goblint_sign_sound`, `runs_to_iff_small_step`.
4. Update `docs/PROOF_OVERVIEW.md`: CFG layer spans 5 files; architecture diagram (§ Long-term architecture); Direct_Equations route gone; **no big-step / `pipeline_sound`**.
5. Update `docs/PROOF_PHASES.md`: drop Direct_Equations / TD_Total / Scratch; canonical theorems = invariant + path.
6. Update `docs/OPEN_PROBLEMS.md`: mark P10 abandoned; remove TD_Total from P6 gate; rebase stale `pipeline_sound` refs.
7. Rebase `docs/PROOF_SIMPLIFICATION.md` on small-step (`compile_path_small_step`, not `big_step_cfg_path`).
8. CLAUDE.md / AGENTS.md "CFG path infrastructure": new file split + thesis sentence.
9. Mark this plan **landed** with per-phase outcomes (including Phase 6–7 status).

**Exit:** build green; docs synced; plan landed.

### Phase 6 — demote `runs_to` in the soundness API (½ day)

Align proof obligations with § Long-term architecture. **Theorem names unchanged**; statements equivalent by `runs_to_def` / `runs_to_iff_small_step`.

1. **`Constraint_System_Sound.exit_sound`** — replace `assumes terminates: "runs_to c s t"` with
   `t ∈ cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))` (or keep `runs_to` and add a one-line comment that it is exit-projected `cfg_collect`).
2. **`TD_Soundness.sign_analysis_sound` / `interval_analysis_sound`** — same for the terminating-run premise; proofs unfold `runs_to_def` at most once.
3. **`Pipeline.thy`** — ensure `pipeline_sound_runs_to` is visibly a corollary (few lines); trim `sign_pipeline_invariant_sound` if still unused in `src/` (keep if thesis names it).
4. **`Goblint_Formalization.goblint_sign_sound`** — may keep `runs_to` in the statement for readability; proof via `pipeline_sound_runs_to` or `pipeline_sound_path` at exit.
5. **Examples** — unchanged pattern: `→*` then `small_step_runs_to`.

**Exit:** no soundness-chain theory treats `runs_to` as anything other than `runs_to_def`; `rg 'assumes.*runs_to' src/` only in Pipeline corollaries / examples / optional exit headlines.

### Phase 7 — compound `cfg_path_*_iff` (optional, post-cleanup)

Not required for architecture lock. See `docs/PROOF_SIMPLIFICATION.md` §2 (rebased on small-step): one `cfg_path_Seq_iff` / `If_iff` / `While_iff` per construct to shrink `CFG_Compound_Paths.thy` (~300–450 LOC). Track as a GitHub issue if not done on this branch.

**Exit:** issue filed or refactor landed; no new `runs_to_*` intro rules introduced.

---

## Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| Splitting `CFG_Collecting.thy` exposes hidden dependencies | Medium | Per-split build; cycles surface immediately |
| Deleting `Direct_Equations` upsets supervisors who wanted both routes | Medium | Route was never finished (7 sorries); resurrect from git if asked |
| New `[simp]` causes a simp loop | Medium | One attribute at a time; `isabelle build -v -v` per-command timings |
| Option (c) WHILE case does not close | Medium | Bounded 1-day spike; fallback to current bridge; no partial merge |
| Deleting `HOL_IMP_Countable` triggers arity-fact clash | Medium | Try direct import in Syntax; if clash persists, drop upstream instances if unused; last resort: 5-line inline theory |
| Inlining intro algebra (Phase 3b) makes the bridge proof ugly | Low | **N/A if option (c) lands.** If fallback, optional (b) is a follow-up, not default |
| Path-lifting combinators introduce off-by-one in offsets | Low | Existing intro proofs are the regression test |
| Automation sweep changes proof scripts without changing theorems | Low | No spec/theorem renames; build is the gate |

## Definition of done

1. **0 sorries** across the entire `src/` tree (current: 15).
2. No file > 1000 LOC.
3. `Goblint_Formalization` builds green in ≤ 25s (current 22s).
4. No **theorem rename** on the soundness chain; `runs_to_def` and `runs_to_iff_small_step` unchanged.
5. **Architecture:** docs + comments state `cfg_collect` as spec; `pipeline_invariant_sound` + `pipeline_sound_path` named as canonical; Phase 6 complete.
6. Compound-shape proof LOC drops by ≥ 50% on average **if fallback**; option (c) removes the intro rules entirely.
7. Apply-script count ≤ 5 session-wide.
8. `docs/PROOF_OVERVIEW.md`, `docs/PROOF_PHASES.md`, `docs/OPEN_PROBLEMS.md`, `PROOF_SIMPLIFICATION.md`, `CLAUDE.md` reflect the new layout and thesis sentence.

## Non-goals

- **Renaming** `runs_to`, `cfg_collect`, or headline theorems.
- **Changing mathematical content** of soundness (premise rephrasing via `runs_to_def` is OK in Phase 6).
- Making `(c,s) →* (SKIP,t)` the default premise on every theorem.
- Solver core, transfer-function proofs, domain case analysis: untouched except import/premise wording.
- Interval / Octagon stretch: independent track.
- Resurrecting big-step, inductive `runs_to`, or Direct_Equations.

## Estimated effort

| Phase | Effort | LOC delta |
|---|---|---|
| 0 baseline | ½ day | 0 |
| 1 delete unused (+ HOL_IMP_Countable, collect API) | ½ day | −490 |
| 2 split Collecting | 1 day | 0 (reorg) |
| 3 option (c) spike | 1 day | −525 if landed; 0 if fallback |
| 4 automation | 1 day | −150 (proof shrink) |
| 5 docs | ½ day | 0 |
| 6 API demotion (`runs_to` → `cfg_collect` premises) | ½ day | ~0 (comments + assumes) |
| 7 compound `iff` (optional) | 1–2 days | −300–450 if done |
| **Total (c lands, no Ph7)** | **~5 days** | **~1165 net** |
| **Total (fallback, no Ph7)** | **~5 days** | **~640 net** |
