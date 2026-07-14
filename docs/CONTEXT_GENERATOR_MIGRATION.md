# Migration to the Goblint-Aligned Analysis Architecture

Historical note: the `TD_Side_Eff_Ctx_Sound` / `side_env_ctx` spine discussed below has been deleted. Shared helpers now live in `TD_Side_Eff_Ctx_Shared`.

**Status:** Implemented 2026-07-12. See *Implementation Findings & Corrections* below — the
original plan mis-stated the dependency graph and has been corrected to match the code.

**Objective:** Consolidate the formalization around the Goblint-style context-seeded (CMP/seed-based) generator architecture. Standardize the thesis on the seed-based strategy, delete the query-based *executable* path and its examples, and keep the shared context-indexed soundness substrate that the CMP path is proven on.

---

## Implementation Findings & Corrections (2026-07-12)

The aspirational body below (written before implementation) assumed **CMP soundness is
standalone and the three "CTX core" theories are used only by CTX examples**. The actual
import graph contradicts this. The corrections here are authoritative; where the body
disagrees, the body is historical.

### The real dependency graph

The canonical CMP path is **layered on top of** the context-indexed soundness core, not a
competing sibling:

- `TD_Side_Eff_Cmp_Sound` **imports** `TD_Side_Eff_Ctx_Sound` and reuses its theorems
  (`post_fixpoint_sound_at_ctx_semantic`, `combine_case_ctx_sound`, `side_env_ctx`,
  `cfg_collect_ctx`, `semantic_entry_store_ctx_analysis_sound`) — dozens of references.
- `TD_Side_Eff_Cmp_Gen` is defined over `side_rhs_fold_ctx` / `side_acc_ctx` /
  `side_cfg_T_eff_ctx` from `TD_Side_Tree`.
- `Exec_Cmp_Bridge` **imports** `Exec_Ctx_Bridge` and uses `unit_combine_tree_ctx_st`.
- `Seeded_Clean_Ctx_Collect` is **imported by** `Seeded_Activation_Sound` (activation spine),
  so it is not orphaned.

**Consequence:** the CMP soundness spine (`... -> Analysis_Sound`) transitively depends on the
"CTX core." By the migration's own rule — *delete only when the dependency cone is empty* —
these theories must be **RETAINED**. Deleting them would require re-proving CMP soundness from
scratch, which is an explicit non-goal (*"Rewrite all soundness proofs"*). No CTX/CMP
equivalence is proved or needed; the CMP path simply *builds on* the shared context-indexed
soundness, which is retained infrastructure rather than a deletable rival.

The label "Ctx" in these theory names denotes **context-indexed** collecting soundness (shared
by both enter strategies), not the query-based *enter* strategy. The genuinely query-specific
surface is the **executable** enter-query generators and their examples.

### Corrected classification

**DELETE (empty cone — genuinely query-executable demo surface):**

| Theory | Reason |
|--------|--------|
| `Canonical_Generator.thy` | Broken prototype; never in any ROOT. |
| `Analysis_Configuration.thy` | Premature locale with no consumer; CMP generators already take `gkey`/`cmb`/`frame_seed` as explicit arguments. Locale-parameterizing them is out-of-scope re-proof. |
| `Exec_Sign_Ctx_Run` | eval-only precision regression on the enter-query scaffold; CMP Keyed/SeededClean demos cover it. |
| `Exec_Sign_Ctx_Gen_Run` | executable `side_cfg_T_eff_ctx_st` witness; `Exec_Sign_Cmp_*` cover the executable-soundness demonstration. |
| `Exec_Sign_Ctx_Seeded_Run` | **unsound-by-construction** illustration; sound counterpart retained as `Example_Global_Ctx_Read_Precision`. |
| `Exec_Ivl_Ctx_Run`, `Exec_Ivl_Ctx_Gen_Run` | interval analogues; `Exec_Ivl_Cmp_Seed_*` cover them. |
| `Exec_Context_Run_Common` | shared scaffold imported only by the two `_Ctx_Run` examples → orphan after their deletion. |
| exec defs `side_cfg_T_eff_ctx_st`, `side_cfg_T_eff_ctx_seeded_st` | dead once the examples are gone (only a comment reference remains). |

**RETAIN (shared substrate — non-empty cone):**

| Theory / definition | Depended on by |
|---------------------|----------------|
| `TD_Side_Eff_Ctx_Sound` | `TD_Side_Eff_Cmp_Sound` (CMP spine) |
| `Exec_Ctx_Bridge` | `Exec_Cmp_Bridge` (CMP spine) |
| `Seeded_Clean_Ctx_Collect` | `Seeded_Activation_Sound` (activation spine) |
| `TD_Side_Tree` CTX generators (`side_cfg_T_eff_ctx*`, `unit_combine_tree_ctx`) | CMP_Gen, CMP_Sound, Ctx_Sound |
| `Example_Global_Ctx_Read_Precision` | context-precision witness over the retained `glob_env_cmp` read layer (no CTX generator) |
| `Example_Entry_Store_Context_Precision` | witnesses the retained `semantic_entry_store_ctx_analysis_sound` |

### Phase-1 audit documents

The body claims `CTX_DEPENDENCY_AUDIT.md`, `STRUCTURAL_AUDIT.md`,
`ENTER_DIVERGENCE_TRACE.md`, `GENERATOR_INVENTORY_BEFORE_MIGRATION.md` exist. **They do not.**
A real dependency-cone audit is produced during implementation and archived, together with a
copy of this corrected document, under `docs/architecture/history/`.

### Net effect

CMP is the sole *supported* context-sensitive strategy: the query-based executable generators
and their examples are removed. The context-indexed soundness core they shared with CMP is
retained (it *is* the CMP proof substrate). Headline "one generator / one soundness spine"
figures in the body are aspirational and not achieved by this migration, because collapsing
the generators would demand the out-of-scope re-proof.

---

## Motivation and Architectural Direction

### Problem Statement

The formalization currently contains two distinct call-entry strategies:

1. **Query-Based (CTX path):** Explicit `QueryL` equations for enter edges; dynamic caller state access
2. **Context-Based (CMP path):** Static frame-seed injection; context pre-computed to encode caller state

While both strategies are mathematically sound, maintaining both creates:
- 8+ generator variant definitions (code duplication)
- Repeated soundness theorems per variant
- Architectural confusion (which strategy is canonical?)
- Proof maintenance burden
- Divergence from Goblint (which uses the seed-based approach exclusively)

### Strategic Decision: Thesis Goal is Goblint Alignment

This thesis formalizes an analysis framework aligned with **Goblint's architecture**. The CMP/seed-based architecture more closely matches Goblint's specification-driven context handling (contexts pre-encode caller information; entry state is seeded, not queried dynamically).

**Therefore:** The formalization consolidates on the seed-based (CMP) approach and migrates away from the query-based (CTX) path, which was developed during earlier architectural experimentation. This is not a compromise; it is architectural clarity.

### Goals

1. **Consolidate around CMP/seed-based strategy:** Make CMP the only supported context-sensitive generator path
2. **Extract and sharereusable infrastructure:** Combine tree builders, global routing, trace-context framework
3. **Eliminate CTX duplication:** Migrate required proofs and examples to CMP; delete CTX-specific theories
4. **One soundness spine:** Unified proof of CMP soundness parameterized by analysis configuration
5. **Architectural alignment with Goblint:** Formalization matches Goblint's calling convention and context strategy
6. **Reduced codebase:** ~50% fewer generator definitions; cleaner dependency structure

### Success Criteria

- ✅ **One supported generator family:** CMP/seed-based only (no query-based fallback)
- ✅ **One canonical soundness spine:** Parameterized by analysis configuration; CMP instances as interpretations
- ✅ **Shared infrastructure retained:** Abstract domain, context policy, combine builders, global routing
- ✅ **CTX path fully migrated or deleted:** No orphaned query-based generators or soundness theorems
- ✅ **Examples ported to CMP:** Sign and Interval analyses use CMP generators exclusively
- ✅ **Thesis results reproducible:** All key findings (precision, soundness) demonstrated via CMP
- ✅ **Zero theorem duplication:** One proof of generator soundness; variants become corollaries

---

## Current Architecture (To Be Refined)

### Generator Landscape

**Query-Based Path (CTX — To Be Migrated/Deleted):**
- `side_cfg_T_eff_ctx`, `side_cfg_T_eff_ctx_seeded` (abstract, TD_Side_Tree.thy)
- `side_cfg_T_eff_ctx_st`, `side_cfg_T_eff_ctx_seeded_st` (executable, Exec_Ctx_Bridge.thy)
- Soundness: `TD_Side_Eff_Ctx_Sound`
- Examples: `Exec_Sign_Ctx_*`, `Exec_Ivl_Ctx_*`, `Example_Global_Ctx_Read_Precision`

**Context-Based Path (CMP — To Be Canonical):**
- `side_cfg_T_eff_cmp`, `side_cfg_T_eff_cmp_seed` (abstract, TD_Side_Eff_Cmp_Gen.thy)
- `side_cfg_T_eff_cmp_st`, `side_cfg_T_eff_cmp_seed_st` (executable, Exec_Cmp_Bridge.thy)
- Soundness: `TD_Side_Eff_Cmp_Sound`, `TD_Side_Eff_Cmp_Pull`
- Examples: `Exec_Sign_Cmp_*`, `Exec_Ivl_Cmp_*`

**Shared Infrastructure:**
- `abstract_domain` (type class for lattice domains)
- `context_domain` (context policy: start_context, ctx_sel, entdg, cmp, prep)
- Combine tree builders (`unit_combine_tree_ctx`, `switching_combine`, `kgen_combine_rread`, etc.)
- Global routing infrastructure (`map_gtree`, `pull_gk`, `gkey`)
- Trace-context framework (`dg_intra`, `dg_return`, `dg_callee`, etc.)

### Duplication Inventory

| Category | CTX | CMP | Total | After Migration |
|----------|-----|-----|-------|-----------------|
| Generator definitions | 4 | 4 | 8 | 1 canonical + interpretations |
| Soundness theorems | 1 main | 1 main | 2 | 1 parameterized |
| Executable variants | 2 | 2 | 4 | 1 + reusable wrappers |
| Example theories | 5+ | 5+ | 10+ | 5+ (CMP only) |

**Target:** All generators and soundness reduced to interpretations of one parameterized base.

---

## Target Architecture

### Core Strategy: Seed-Based Context (CMP)

The canonical architecture standardizes on the context-seeded (CMP) strategy:

- **Context:** Pre-computed to encode caller state (via `entdg` and `ctx_sel`)
- **Entry:** Seeded with `frame_seed c` (static injection, not dynamic query)
- **Globals:** Routed to keyed slots via `gkey`
- **Combine:** Supplied as parameter (`cmb` tree builder)

This matches Goblint's calling convention and eliminates the architectural complexity of two competing strategies.

### Layer 1: Abstract Domain (Shared)

```isabelle
class abstract_domain = sound_domain + widening
```

Unchanged. Provides lattice structure.

### Layer 2: Context Policy (Shared)

```isabelle
locale context_domain =
  fixes start_context :: 'c
    and ctx_sel :: pp → 'c → 'a abs_state → 'c
    and entdg :: store → 'c
    and cmp :: 'c → 'c → bool
```

**Refinement from current:** Remove `prep` (not generator-critical; combine builders handle it locally if needed).

### Layer 3: Generator Configuration (New)

```isabelle
locale generator_configuration =
  abstract_domain +
  fixes cmb :: 'c → pp → pp → (pp × 'c, 'g, 'a abs_state) strategy_tree
    and gkey :: 'c → 'g
    and frame_seed :: 'c → 'a abs_state
  (* No assumptions — pure reusable interface *)
```

**Contains:** Only parameters used directly by equation generation.

### Layer 4: Analysis Configuration (Combines Layers 1–3)

```isabelle
locale analysis_configuration =
  abstract_domain +
  context_domain +
  generator_configuration
```

**Contains:** All reusable parameters for the CMP path. No soundness assumptions.

### Layer 5: Canonical Seed-Based Generator

```isabelle
definition side_cfg_T_eff_cmp_seed ::
  cfg
  → (unit, 'a::abstract_domain) effectful_domain_transfer
  → 'a abs_state → 'a abs_state
  → (pp × 'c, 'g, 'a abs_state) eqsT
  (parameterized by: cmb, gkey, frame_seed inside analysis_configuration)
```

**Single definition** covering all CMP variants (seeded and non-seeded via `frame_seed = λ_. ⊥`).

Existing CMP generators recover as interpretations:
- `side_cfg_T_eff_cmp` = instantiation with constant `frame_seed`
- `side_cfg_T_eff_cmp_seed` = instantiation with context-dependent `frame_seed`

### Layer 6: Soundness (Parameterized)

```isabelle
theorem context_generator_sound [OF analysis_configuration]:
  "part_post_solution (side_cfg_T_eff_cmp_seed g etf bot0 s0) σ vars
   ⟹ cfg_collect_ctx dg cmp g S v ctx ⊆ ⟦renv σ (v, ctx)⟧"
```

**One theorem**, parameterized by `analysis_configuration`. All domain instances (Sign, Interval, etc.) prove concrete soundness via interpretation.

### Layer 7: Solver (Unchanged)

Uses CMP generator output; no changes needed.

### What Disappears

- Query-based generator family (CTX)
- CTX soundness theorems and bridges
- Historical documentation of two strategies as alternatives

---

## Dependency Cone: What Moves, What Stays

Based on complete audit of CTX imports:

### DELETE: CTX-Specific Core Theories

> **Superseded — see *Implementation Findings & Corrections* above.** Items 1–3 below are
> NOT CTX-only: the CMP soundness spine and the activation spine import them, so they are
> **retained**. Only item 4 (`Canonical_Generator.thy`) is deleted from this list; the real
> deletions are the query-executable examples and their dead generator defs.

These three theories are CTX-only; no code depends on them except examples.

1. **TD_Side_Eff_Ctx_Sound** (`src/Analysis/Generic/Solver/Context/TD_Side_Eff_Ctx_Sound.thy`)
   - Provides: pullback reduction from context-indexed to monovariant
   - Users: Only CTX examples and documentation
   - **Action:** Delete after examples migrate

2. **Exec_Ctx_Bridge** (`src/Analysis/Generic/Solver/Exec/Exec_Ctx_Bridge.thy`)
   - Provides: executable mirrors of CTX generators
   - Users: Only CTX examples
   - **Action:** Delete after examples migrate

3. **Seeded_Clean_Ctx_Collect** (`src/Analysis/Generic/Solver/Context/Seeded_Clean_Ctx_Collect.thy`)
   - Provides: collecting semantics for CTX path
   - Users: None currently (orphaned)
   - **Action:** Delete immediately

4. **Canonical_Generator.thy** (from earlier prototype work)
   - Status: Incomplete, incorrect prototype
   - **Action:** Delete; replace with refined approach

### MIGRATE: CTX Examples → CMP Equivalents

Seven theories must be ported from CTX to CMP:

| Theory | Location | Action |
|--------|----------|--------|
| `Exec_Sign_Ctx_Gen_Run` | Sign/Context | Port to `Exec_Sign_Cmp_Seed_*` |
| `Exec_Sign_Ctx_Run` | Sign/Context | Port to CMP or verify redundant with seeded |
| `Exec_Sign_Ctx_Seeded_Run` | Sign/Context | Port to CMP (likely already exists) |
| `Exec_Ivl_Ctx_Gen_Run` | Interval/Context | Port to `Exec_Ivl_Cmp_Seed_*` |
| `Exec_Ivl_Ctx_Run` | Interval/Context | Port to CMP or verify redundant |
| `Example_Global_Ctx_Read_Precision` | Digest | Migrate or document as CTX-only insight |
| `Example_Entry_Store_Context_Precision` | Digest | Evaluate; migrate if CMP doesn't subsume |

**Criteria:** CMP equivalent must demonstrate the same precision or the insight must be retained in documentation before deletion.

### RETAIN: Shared Infrastructure

These remain unchanged and are used by both paths (during migration) and CMP (after):

| Infrastructure | Location | Used By | Action |
|---|---|---|---|
| `context_domain` | Context_Domain.thy | Soundness, config | Keep; refine docs |
| `TD_Side_Tree` | Core/TD_Side_Tree.thy | Both generators | Keep; extract shared layer |
| CFG enter/non-enter predicates | CFG_Def.thy | Both paths | Keep; essential |
| Combine tree builders | Various | Both paths | Keep; generalized |
| Global routing infrastructure | TD_Side_Eff_Cmp_Gen.thy | Both paths | Keep |
| Trace-context framework | TD_Side_Eff_Cmp_Sound.thy | Soundness | Keep |
| `abstract_domain`, domain instances | Domain/*.thy | Both | Keep |

---

## CMP as Canonical

**What stays and becomes the sole supported path:**

- `side_cfg_T_eff_cmp` (keyed-globals without seeding)
- `side_cfg_T_eff_cmp_seed` (keyed-globals with seeding) — **PRIMARY**
- `side_cfg_T_eff_cmp_seed_st` (executable seeded variant) — **PRIMARY**
- `TD_Side_Eff_Cmp_Sound` (soundness theorem)
- All CMP examples (`Exec_Sign_Cmp_*`, `Exec_Ivl_Cmp_*`)

These are the implementation blueprint. All domain instances use these going forward.

---

## Migration Phases: CTX → CMP Consolidation

The migration strategy treats CTX as scaffolding for understanding the formalization, not as a permanent architectural choice. The goal is to migrate all thesis-relevant results to CMP and delete CTX.

### Phase 1: Audit & Planning (Completed)

> **Correction:** the named audit files were never created (see *Implementation Findings*).
> The real dependency-cone audit was produced at implementation time and archived under
> `docs/architecture/history/`.

**Deliverables:**
- Complete dependency cone audit (`docs/architecture/history/CTX_DEPENDENCY_AUDIT.md`)
- Classification: DELETE (prototype + 5 query examples + orphan scaffold + dead defs), RETAIN (context-indexed soundness substrate + 2 precision witnesses)
- This corrected migration document

**Exit gate:** Audit complete; migration sequence clear.

### Phase 2: Extract Shared Infrastructure

**Objective:** Identify and clarify reusable components independent of enter strategy.

**Scope:**
- Document the shared layer: combine builders, global routing, trace framework, context policy
- Create/refine `generator_configuration` locale (cmb, gkey, frame_seed)
- Verify CMP generators can reference shared infrastructure directly
- No deletion of CTX yet; shared layer is used by both during transition

**New files:**
- Update `src/Analysis/Generic/Solver/Context/Analysis_Configuration.thy` (if exists) or create it
- Add documentation of shared layer

**Exit gate:** Shared infrastructure is explicit and reusable.

### Phase 3: Migrate CTX Examples to CMP

**Objective:** Port all required proofs and examples from CTX to CMP equivalents.

**Scope:**
1. **Port Sign examples:**
   - `Exec_Sign_Ctx_Gen_Run` → update to use `side_cfg_T_eff_cmp_seed_st`
   - `Exec_Sign_Ctx_Seeded_Run` → merge with CMP or verify redundancy
   - Verify results match or improve

2. **Port Interval examples:**
   - `Exec_Ivl_Ctx_Gen_Run` → update to use CMP
   - Verify soundness and precision preserved

3. **Migrate digest examples:**
   - `Example_Global_Ctx_Read_Precision` → port or document as CMP-inaccessible
   - `Example_Entry_Store_Context_Precision` → evaluate and migrate

**Success criteria:**
- All thesis-relevant results reproducible via CMP
- Precision metrics maintained or improved
- Zero `sorry` statements

**Exit gate:** All required examples run on CMP; no thesis results depend on CTX.

### Phase 4: Consolidate CMP Generators

**Objective:** Establish CMP as canonical; clean up CMP soundness hierarchy.

**Scope:**
- Ensure `side_cfg_T_eff_cmp_seed` is the primary generator
- Verify `side_cfg_T_eff_cmp` recovers as `side_cfg_T_eff_cmp_seed` with `frame_seed = λ_. ⊥`
- Consolidate soundness under one parameterized theorem
- Update documentation to make CMP canonical

**No new code;** primarily documentation and reorganization.

**Exit gate:** CMP soundness is single spine; all variants are interpretations.

### Phase 5: Delete CTX Core

**Objective:** Remove CTX-specific theories; clean up imports.

**Scope:**
1. Delete:
   - `TD_Side_Eff_Ctx_Sound`
   - `Exec_Ctx_Bridge`
   - `Seeded_Clean_Ctx_Collect`
   - `Canonical_Generator.thy` (prototype)

2. Verify no remaining imports of deleted theories

3. Update any documentation or comments referencing CTX path

**Exit gate:** No CTX theories remain; codebase builds with CMP as only path.

---

## Non-Goals

This migration explicitly does **not** aim to:

- **Prove CTX and CMP equivalent:** The audit shows they differ architecturally. No equivalence proof is necessary or attempted.
- **Preserve historical implementations:** CTX and related theories are removed, not maintained for backward compatibility.
- **Optimize both architectures simultaneously:** The thesis standardizes on one architecture; the other is not tuned.
- **Introduce richer Goblint manager/query support:** Potential extensions (e.g., cross-analysis context queries) are future work, not part of this refactoring.
- **Rewrite all soundness proofs:** CMP soundness already exists. This migration validates CMP adequacy for thesis results; it doesn't reprove CMP.

**Scope:** Migration is focused on architectural consolidation, not on enhancement or extension.

---

### Phase 6: Final Cleanup & Documentation

**Objective:** Streamline codebase; document architectural decisions.

**Scope:**
- Archive old generator inventory in `docs/CONTEXT_GENERATOR_MIGRATION_ARCHIVED.md`
- Update README and architecture docs to reflect CMP-only design
- Add architectural rationale: "Why seed-based context?"
- Simplify generator selection guidance (now: just use CMP)

**Exit gate:** Codebase is lean; architecture is clear; thesis is architecturally aligned with Goblint.

---

## Rollback Strategy

**If Phase 3 (example migration) fails:**

- Determine why CMP cannot express needed behavior
- If CMP is genuinely insufficient, revert to status quo and document limitation
- Otherwise, debug example port and retry

**If Phase 5 (CTX deletion) fails:**

- Identify any unexpected CTX dependencies
- Migrate those dependencies
- Retry deletion

**Key principle:** Each phase is reversible. Migration does not delete CTX until Phase 5; Phase 3 can succeed without Phase 4 or 5.

---

## Risks: Migration-Focused

### Risk 1: Hidden CTX Dependencies

**Issue:** Unexpected code outside CTX core depends on `TD_Side_Eff_Ctx_Sound` or `Exec_Ctx_Bridge`.

**Mitigation:** Thorough grep in Phase 1 audit. Any new dependencies block Phase 5 deletion and must be migrated first.

**Severity:** Medium. Identified in Phase 1; does not compromise migration if handled sequentially.

### Risk 2: Example Migration Reveals Incompleteness in CMP

**Issue:** CTX examples demonstrate precision or behavior CMP cannot replicate.

**Mitigation:**
- Understand why CTX is more precise (likely enter query strategy)
- Evaluate if insight is thesis-critical
- If yes: document, keep as CTX-only result, do not delete
- If no: enhance CMP if feasible, or accept loss of exploratory result

**Severity:** Medium-high. Blocks full migration; may require architectural reconsideration.

**Mitigation example:** If CTX dynamic caller querying is essential, refactor to make CMP context selection richer rather than keeping two generators.

### Risk 3: Soundness Proof Migration Complexity

**Issue:** CTX soundness uses pullback reduction (`pull_ctx`) that CMP soundness doesn't reference. Reprov through CMP may be complex.

**Mitigation:** Both paths already have independent soundness proofs. CMP soundness (`TD_Side_Eff_Cmp_Sound`) is standalone. No reproof necessary; just validate CMP examples.

**Severity:** Low. CMP soundness exists; no reproof needed.

### Risk 4: Combine Tree Builder Incompleteness

**Issue:** Some combine trees (e.g., `unit_combine_tree_ctx`) are CTX-specific and don't port to CMP.

**Mitigation:** Generalize combine trees to work with both strategies OR migrate to strategy-specific wrappers.

**Severity:** Medium. Affects example portability; solvable with refactoring.

---

## What This Migration Does NOT Risk

- **Soundness of CMP:** CMP path is already proven sound independently.
- **Existing CMP results:** No changes to CMP generators or soundness theorems (only documentation and deletion of CTX).
- **Thesis conclusions:** All results are demonstrated via CMP; CTX deletion does not weaken claims.
- **Goblint alignment:** CMP is already Goblint-aligned; CTX deletion improves alignment.

---

## Success Criteria: CMP-Canonical Architecture

### Phase 1: Audit & Planning
- [x] CTX dependency cone fully mapped
- [x] 3 theories classified for deletion
- [x] 7 examples classified for migration
- [x] 5+ infrastructure components identified for retention
- [x] Migration sequence determined

### Phase 2: Shared Infrastructure
- [ ] `generator_configuration` locale clearly separates reusable parameters (cmb, gkey, frame_seed)
- [ ] `context_domain` documented as orthogonal to generator choice
- [ ] Combine tree builders identified as generic (not strategy-specific)
- [ ] Global routing infrastructure (gkey, map_gtree) documented as shared
- [ ] No circular dependencies; shared layer can stand alone

### Phase 3: Example Migration
- [ ] `Exec_Sign_Ctx_Gen_Run` ported to CMP or verified as redundant
- [ ] `Exec_Sign_Ctx_Seeded_Run` ported to CMP
- [ ] `Exec_Ivl_Ctx_Gen_Run` ported to CMP
- [ ] `Example_Global_Ctx_Read_Precision` migrated or documented as CTX-only insight
- [ ] All thesis-critical results reproducible via CMP
- [ ] Precision metrics maintained or improved
- [ ] Zero regressions; all examples execute

### Phase 4: CMP Consolidation
- [ ] CMP soundness (`TD_Side_Eff_Cmp_Sound`) is the sole soundness spine
- [ ] `side_cfg_T_eff_cmp_seed` is the primary generator
- [ ] `side_cfg_T_eff_cmp` recovers as interpretation with `frame_seed = λ_. ⊥`
- [ ] Documentation clearly identifies CMP as canonical
- [ ] No competing generator strategies mentioned in new docs

### Phase 5: CTX Deletion
- [ ] `TD_Side_Eff_Ctx_Sound` deleted; no imports remain
- [ ] `Exec_Ctx_Bridge` deleted; no imports remain
- [ ] `Seeded_Clean_Ctx_Collect` deleted
- [ ] `Canonical_Generator.thy` prototype deleted
- [ ] No CTX-related code remains in production
- [ ] Build clean without deprecation warnings

### Phase 6: Final Cleanup
- [ ] Repository has one supported context-sensitive generator family (CMP/seed-based)
- [ ] One soundness theorem (parameterized by analysis_configuration)
- [ ] Shared infrastructure retained and documented
- [ ] Architecture docs clarify thesis as Goblint-aligned
- [ ] Codebase is lean, clear, and maintainable
- [ ] Duplication reduced from 8+ variants to 1 canonical + interpretations

---

## Proof Strategy: Consolidate on CMP

### Current State (Dual Strategies)

Two competing call-entry mechanisms create soundness duplication:

```isabelle
-- Query-based (CTX):
theorem side_cfg_T_eff_ctx_sound := ...
theorem side_cfg_T_eff_ctx_seeded_sound := ...

-- Context-based (CMP):
theorem side_cfg_T_eff_cmp_sound := ...
theorem side_cfg_T_eff_cmp_seed_sound := ...
```

Each maintains separate soundness arguments, even though the obligations are almost identical.

### CMP-Canonical Approach

One soundness theorem, parameterized by generator configuration:

```isabelle
-- Unified soundness
theorem context_generator_sound :
  "analysis_configuration σ ⟹ 
   part_post_solution (side_cfg_T_eff_cmp_seed g etf bot0 s0) σ →
   cfg_collect_ctx dg cmp g S v ctx ⊆ ⟦renv σ (v, ctx)⟧"

-- Domain instances inherit
theorem Sign_cmp_seed_sound := (Sign_analysis_configuration.context_generator_sound)
theorem Interval_cmp_seed_sound := (Interval_analysis_configuration.context_generator_sound)
```

**Result:** One proof (parameterized); all generators are interpretations.

### Migration: No Reproof Needed

CTX deletion does not require reproof of CMP. CMP soundness already exists and is independent.

**Example:**
- `TD_Side_Eff_Cmp_Sound` is already complete
- Delete CTX theories without touching CMP soundness
- CMP examples remain sound throughout migration

---

## Cleanup Plan (Phases 5–6)

### What to Delete

**CTX-specific theories:**
1. `TD_Side_Eff_Ctx_Sound` — CTX soundness backbone (unused after CMP consolidation)
2. `Exec_Ctx_Bridge` — CTX executable variants (replaced by CMP)
3. `Seeded_Clean_Ctx_Collect` — CTX collecting semantics (orphaned)
4. `Canonical_Generator.thy` — Prototype (incomplete, incorrect)

**CTX examples (after migration to CMP):**
- Old `Exec_Sign_Ctx_*` files (if replaced by CMP equivalents)
- Old `Exec_Ivl_Ctx_*` files (if replaced by CMP equivalents)

**Documentation:**
- Archive old generator inventory in `docs/CONTEXT_GENERATOR_MIGRATION_ARCHIVED.md`
- Deprecate old generator-selection guidance

### What to Retain

**Core infrastructure:**
- `abstract_domain` class
- `context_domain` locale (context policy)
- `generator_configuration` locale (reusable generator parameters)
- Shared combine tree builders
- Global routing infrastructure

**CMP path:**
- `side_cfg_T_eff_cmp`, `side_cfg_T_eff_cmp_seed` (canonical generators)
- `side_cfg_T_eff_cmp_st`, `side_cfg_T_eff_cmp_seed_st` (executable variants)
- `TD_Side_Eff_Cmp_Sound` (soundness)
- All CMP examples

**Domain instances:**
- Sign, Interval, etc. (using CMP exclusively)

### Documentation Updates

**Add to repository:**
- Architecture rationale: "Why seed-based context?"
- Goblint alignment notes: "How formalization mirrors Goblint"
- Migration log: what was deleted and why

**Archive (docs/architecture/history/):**
- This migration plan (`MIGRATION_TO_GOBLINT_ALIGNED_ARCHITECTURE.md`)
- Structural audit documents (`CTX_DEPENDENCY_AUDIT.md`, `STRUCTURAL_AUDIT.md`, `ENTER_DIVERGENCE_TRACE.md`)
- Old generator inventory (`GENERATOR_INVENTORY_BEFORE_MIGRATION.md`)
- Lessons learned: why two strategies differed architecturally

These documents explain the *why* behind the refactoring and serve as historical evidence for future developers wondering about the design choices.

**Clarify:**
- Generator selection: "Use CMP/seed-based for all new work"
- Interface stability: "analysis_configuration will be extended for richer Goblint-style contexts"

---

## Success Metrics: Consolidation and Alignment

| Aspect | Current | Target | Notes |
|--------|---------|--------|-------|
| **Generators** | 8+ variants | 1 CMP + interpretations | Eliminate duplication |
| **Soundness theorems** | 2+ branches (CTX, CMP) | 1 parameterized | One proof per analysis |
| **Supported strategies** | 2 (query-based, seed-based) | 1 (seed-based) | Goblint-aligned |
| **Call-entry approach** | Dynamic query OR static seed | Static seed only | Simplified architecture |
| **Architectural clarity** | "Which is canonical?" | "Use CMP seed-based" | Clear guidance |
| **Code duplication** | ~500 LOC | Substantially reduced | Remove CTX-specific code |
| **CTX-specific code** | 4 core + 7 examples | 0 | Complete migration |
| **Example theories** | 10+ (CTX + CMP) | 5+ (CMP only) | No redundancy |
| **Goblint alignment** | Dual strategies (confusing) | Single strategy (aligned) | Direct correspondence |

---

## Execution Checklist

**Before starting migration:**
- [ ] This document approved
- [ ] `CTX_DEPENDENCY_AUDIT.md` reviewed
- [ ] Team agrees on CMP-canonical direction

**During migration:**
- [ ] Phase 2: Shared infrastructure documented
- [ ] Phase 3: All examples successfully ported to CMP
- [ ] Phase 4: CMP consolidation complete
- [ ] Phase 5: CTX deletion complete; no imports remain
- [ ] Phase 6: Documentation updated; archive created

**After completion:**
- [ ] Build clean with CMP only
- [ ] Tests pass; no regressions
- [ ] All thesis results reproducible via CMP
- [ ] Goblint alignment documented
- [ ] Future extensions can build on CMP foundation

---

## Architectural Rationale: Why Seed-Based, Not Both?

### The CTX and CMP Families Differ Architecturally

The structural audit revealed that CTX and CMP differ in a fundamental way:

1. **Query-Based (CTX):**
   - Generates explicit `QueryL` equations for enter edges
   - Dynamically accesses caller state at fixpoint time
   - Context parameter is generic; can be instantiated with any type

2. **Seed-Based (CMP):**
   - Injects static `frame_seed c` into accumulator at initialization
   - Assumes context is pre-computed to encode caller state
   - Enter edges are implicit; handled via context pre-selection

Although a sufficiently parameterized generator could encode both strategies, the thesis intentionally standardizes on the CMP architecture to match Goblint and reduce architectural complexity. The two families are **not parameter variations** of the same design; they reflect **different assumptions about when and how call-entry information enters the equation system**:

- CTX: Generator plus solver together resolve enter constraints
- CMP: Context selection pre-computes enter information; generator just injects seed

### Goblint's Architecture and Seed-Based Contexts

Goblint's implementation uses seed-based context handling:

1. **Specification-driven:** Goblint's `Spec.enter` is a context-to-state function; contexts pre-encode caller information
2. **Efficiency:** Pre-computed contexts avoid dynamic equation queries; simpler solver loop
3. **Modularity:** Context selection is a separate plugin; the solver operates over fixed context instances
4. **Extensibility:** Rich context domains (e.g., flow-sensitive return values) integrate naturally as "just another context type"

### Why Thesis Should Standardize on Seed-Based

1. **Alignment:** Formalization should match Goblint's architecture
2. **Clarity:** One strategy is clearer than two; architects and maintainers understand the design
3. **Duplication:** Maintaining both creates no benefit; the strategies are not interchangeable
4. **Extensibility:** CMP naturally extends to richer contexts; CTX doesn't
5. **Proof hygiene:** One soundness proof is cleaner than maintaining two separate proofs

### What CTX Contributed

Query-based exploration was valuable for understanding the design space. But the thesis's goal is to formalize a specific analyzer (Goblint-style). That analyzer uses seed-based contexts. Thesis should reflect that choice.

**Conclusion:** Delete CTX not because it's wrong, but because it's not Goblint's strategy. The thesis proves the chosen strategy sound; it doesn't need to prove alternative strategies equally.

---

## Audit Documents (Archived After Migration)

- **Dependency Audit:** `docs/architecture/history/CTX_DEPENDENCY_AUDIT.md` — the real
  dependency-cone analysis and the delete/retain classification produced during
  implementation.
- **Migration Plan:** this document, kept at `docs/CONTEXT_GENERATOR_MIGRATION.md` as the
  updated record of what was planned and what was actually done.

The `STRUCTURAL_AUDIT.md`, `ENTER_DIVERGENCE_TRACE.md`, and
`GENERATOR_INVENTORY_BEFORE_MIGRATION.md` referenced earlier in this file never existed and
are not archived.

---

## Conclusion

The formalization will consolidate around the CMP/seed-based generator architecture, eliminating the historical CTX path. This improves code clarity, reduces duplication, and aligns the thesis with Goblint's proven design. All thesis-critical results will be demonstrated via CMP; the architecture will be clean and maintainable.

---

## Implementation Log (2026-07-12)

What was actually done, as small verified commits:

1. **docs(ctx-migration): correct dependency cone** — added the *Implementation Findings*
   section; recorded that the CMP soundness spine imports `TD_Side_Eff_Ctx_Sound`, the CMP
   executable bridge imports `Exec_Ctx_Bridge`, and `Seeded_Activation_Sound` imports
   `Seeded_Clean_Ctx_Collect`, so those three are retained substrate rather than CTX-only
   deletables.
2. **delete prototype scaffolding** — removed `Canonical_Generator.thy` (broken, never in any
   ROOT) and `Analysis_Configuration.thy` (unused locale; CMP generators already take
   `gkey`/`cmb`/`frame_seed` directly).
3. **refactor: delete query-executable CTX examples; repoint CMP deps** — removed
   `Exec_Sign_Ctx_Run`, `Exec_Sign_Ctx_Gen_Run`, `Exec_Sign_Ctx_Seeded_Run`,
   `Exec_Ivl_Ctx_Run`, `Exec_Ivl_Ctx_Gen_Run`, and the orphaned `Exec_Context_Run_Common`
   (ROOT + files). Repointed the two retained CMP examples that imported CTX examples only
   for transitive deps (`Exec_Sign_Cmp_Keyed_Gen_Run` → `Sign_Exec_Sound`;
   `Exec_Ivl_Cmp_Seed_Clean_Run` → `Exec_Ivl_Run`). Reworded prose naming deleted theories.
   `Voblint_Formalization` build green.
4. **refactor: drop dead executable CTX generators from `Exec_Ctx_Bridge`** — removed the two
   now-unreferenced executable generators `side_cfg_T_eff_ctx_st` / `side_cfg_T_eff_ctx_seeded_st`
   and their transport clusters (~590 lines), keeping the shared executable helpers
   (`side_rhs_fold_ctx_st`, `unit_combine_tree_ctx_st`, `st_of_abs`) that `Exec_Cmp_Bridge`
   consumes. Fixed a `\<^const>` antiquotation in `Exec_Sign_Cmp_Keyed_Gen_Run`. Full
   Analysis + Formalization build green.
5. **docs: archive audit + update READMEs** — added
   `docs/architecture/history/CTX_DEPENDENCY_AUDIT.md` (the real cone audit) and this
   document; updated the Exec and Common READMEs.

### CMP canonical status (no code change needed)

The abstract CMP generator is already single and canonical: `side_cfg_T_eff_cmp`
(`TD_Side_Eff_Cmp_Gen`), with seeding supplied as the `fresh_frame` argument. The seeded
abstract generator `side_cfg_T_eff_cmp_seed` and executable `side_cfg_T_eff_cmp_seed_st` exist
in `Exec_Cmp_Bridge`, and the unseeded executable generator already reduces to the seeded one
with a constant seed:

```isabelle
lemma seed_generalises:
  "side_cfg_T_eff_cmp_st gkey cmb g etf ff bot0 s0
     = side_cfg_T_eff_cmp_seed_st gkey cmb (\<lambda>_. ff) g etf bot0 s0"
```

### Retained vs. deleted (final)

- **Deleted:** `Canonical_Generator`, `Analysis_Configuration`, five CTX examples,
  `Exec_Context_Run_Common`, and the two executable CTX generators inside `Exec_Ctx_Bridge`.
- **Retained substrate:** `TD_Side_Eff_Ctx_Sound`, `Exec_Ctx_Bridge` (shared helpers),
  `Seeded_Clean_Ctx_Collect`, the `TD_Side_Tree` CTX generators, and the two context-precision
  witnesses (`Example_Global_Ctx_Read_Precision`, `Example_Entry_Store_Context_Precision`).

### Deviations from the original plan

- The three "CTX core" theories are **not** deleted — they are the proof substrate the CMP
  path is built on. Deleting them would need an out-of-scope re-proof of CMP soundness.
- No parameterized "one soundness theorem" was introduced; CMP soundness already exists and is
  retained unchanged.
- The named Phase-1 audit files never existed; a single real `CTX_DEPENDENCY_AUDIT.md` was
  produced instead. `STRUCTURAL_AUDIT.md` / `ENTER_DIVERGENCE_TRACE.md` /
  `GENERATOR_INVENTORY_BEFORE_MIGRATION.md` are not created (they never existed to archive).
