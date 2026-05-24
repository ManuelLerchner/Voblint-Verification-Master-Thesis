# Proof Simplification Notes

**Rebased 2026-05-24 (small-step migration).** The monolithic `CFG_Collecting.thy` is
split across `CFG_Edges_Collect` … `CFG_Runs_To_Bridge` (import `CFG_Runs_To_Bridge` for the full chain).
Forward bridge: **`compile_path_small_step`** (CFG path → small-step star). Big-step
`compile_path_big_step` / `big_step_cfg_path` are **gone**. Reverse bridge: direct
`small_step_preserves_runs_to`; optional follow-up is deleting the seven `runs_to_*`
intro rules (Phase 3 full in `docs/POST_MIGRATION_CLEANUP.md`).

The notes below still describe compound-path duplication (~900 LOC in
`CFG_Compound_Paths.thy`); targets are unchanged but line numbers refer to the **old**
monolith unless updated per file.

---

Snapshot after closing `cfg_collect_exit_eq_collect` (May 2026). The CFG-collecting layer works but the compound block is still heavy: two long directions and three nearly-parallel compound splitters. Below are concrete simplification opportunities, ranked by likely payoff vs. risk.

## Progress log

| Pass                                                                                                                                                            | LOC saved | Resulting size | Notes                                                                        |
| --------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------: | -------------- | ---------------------------------------------------------------------------- |
| baseline                                                                                                                                                        |        -- | 2,396          | after closing equivalence                                                    |
| dropped `cfg_path_While_loop_peel_length` wrapper (trivial)                                                                                                     |        22 | 2,374          | inlined `length` derivation                                                  |
| dropped `compile_path_big_step_while_rest`; fused into `compile_path_big_step`                                                                                  |        96 | 2,278          | one fewer exported lemma, removes universal-body API trap                    |
| dropped dead helpers `cfg_path_If_in_c1`, `cfg_path_If_in_c2`                                                                                                   |       146 | 2,132          | zero use sites                                                               |
| dropped dead Seq helpers (`cfg_edges_compile_Seq_E{1,2}_subset`, `seq_comp_entry_ne_exit`, `Seq_edge_cross_bridge`, `path_collect_via_append`, `Seq_en2_ge_n1`) |        71 | 2,061          | zero use sites                                                               |
| factored `cfg_path_singleton_edge` lemma; rewrote SKIP/Assign cases of both direction proofs                                                                    |       -12 | 2,073          | net +12 LOC (new helper) but replaces 4 giant `metis` blocks with clean Isar |
| **subtotal**                                                                                                                                                    |   **323** | **2,073**      | item 1 + dead-sweep + SKIP/Assign cleanup done                               |

---

## Size audit

| Lemma                                 | Lines | Role                       |
| ------------------------------------- | ----: | -------------------------- |
| `big_step_cfg_path`                   |   427 | big-step → exists CFG path |
| `compile_path_big_step`               |   340 | CFG path → big-step        |
| `cfg_path_If_split`                   |    94 | If compound path splitter  |
| `compile_path_big_step_while_rest`    |    93 | helper: loop iterations    |
| `cfg_path_If_in_c2` / `_c1`           |   ~75 | If sub-path lifters        |
| `cfg_path_If_factor_c2` / `_c1`       |   ~70 | If sub-path factorers      |
| `cfg_path_Seq_split` / `_in_c2`       |   ~70 | Seq splitter/lifter        |
| `cfg_path_While_u_body_to_zero_split` |    67 | While splitter             |

~1,500 of the 2,396 lines are these structurally similar proofs.

---

## Key isolations (ranked)

### 1. **Drop `compile_path_big_step_while_rest`; merge into `compile_path_big_step`**
*Payoff: ~100 lines, removes a subtle universal-body API trap.*

The helper exists only because the `compile_path_big_step` `While` case needs path-length induction. After the May-2026 fix the body assumption is universal over the start state i.e. the helper is essentially a second copy of the `While` IH. Rewrite the top-level proof's induction to:

```isabelle
proof (induction "(c, length es)" arbitrary: c es s t S rule: ...)
```

or carry an inner `induction "length es_rest" rule: less_induct` directly in the While branch. Either kills the helper.

### 2. **Single compound-CFG structure lemma per construct, replacing the splitter / factorer / lifter triples**
*Payoff: ~400 lines across If + While; modestly less for Seq.*

Today, each compound `c ∈ {Seq, If, While}` has 2–5 ad-hoc splitter lemmas: `in_c1`, `in_c2`, `factor_c1`, `factor_c2`, `split`, `u_body_to_zero_split`, ... Each repeats: classify edges by source, induct on the path, peel a bridge edge, recurse.

Replace with **one bidirectional characterization per construct**:

```isabelle
lemma cfg_path_Seq_iff:
  "cfg_path (to_cfg (c1;;c2)) en1 es (ex20 + n1)
   ↔ (∃es1 es2. es = es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2 ∧
                cfg_path (to_cfg c1) en1 es1 ex1 ∧
                cfg_path (to_cfg c2) en20 es2 ex20)"
```

(Analogous for If and While.) Both proof directions then reduce to a one-line `rule cfg_path_Seq_iff.subst` instead of bespoke pattern-matching. The compound-edge classification helpers (`compound_*_edge_src_*`) become local proofs of the `iff` lemma and don't need names downstream.

### 3. **Single "edge ↔ IMP step" bridge file**
*Payoff: ~150 lines distributed across both directions.*

The action enum (`EA_Assign`, `EA_Assume`, `EA_AssumeNot`, `EA_Nop`) interpretation is currently re-derived inline in both `big_step_cfg_path` and `compile_path_big_step`. Hoist into `CFG_Edges.thy` (or a section of `CFG_Path.thy`):

```isabelle
lemma edge_step_Assign: "(c = x ::= a) ⟹ edge_collect (EA_Assign x a) {s} = {s'} ⟹ (c, s) ⇒ s'"
lemma edge_step_Assume: "edge_collect (EA_Assume b) {s} ≠ {} ⟹ bval b s"
...
```

plus the converses. The two direction-proofs then chain these as `rule` applications, killing the per-case `metis` blasts.

### 4. **Bridge `cfg_path_collect = cfg_collect` once, work in path-collect terms downstream**
*Payoff: simpler statement of `cfg_collect_exit_eq_collect`'s consumers.*

Currently three collecting views co-exist:
- `path_collect` (fold over action list)
- `cfg_path_collect` (union over CFG paths to a point)
- `cfg_collect` (lfp of CFG transformer)

`cfg_path_collect_exit_le_collect` proves one direction at exit. Prove **`cfg_collect = cfg_path_collect` at every point** (already half-done: `cfg_collect_le_path_collect` exists at L275). Then downstream lemmas in `Constraint_System_Sound` can pick whichever side is easier; we don't have to translate between two views per consumer.

### 5. **Drop `edge_collect`; inline as a one-clause `path_collect`**
*Payoff: ~20 lines, one fewer simp rule to keep in mind.*

`edge_collect a S = path_collect [(a, undefined)] S`. The `pp` second component of `path_collect`'s pair is unused by `edge_collect`. Two paths:
- (a) Remove `edge_collect`, use `path_collect [(a, 0)] S` directly.
- (b) Or change `path_collect` to fold over `edge_action list` (drop the `pp` annotation entirely from path types), since the destination `pp` of each edge is recoverable from the CFG edge predicate.

(b) is more invasive but removes a recurring source of confusion in compound-CFG offsets.

### 6. **Trim `big_step_cfg_path`'s `Skip` / `Assign` cases**
*Payoff: ~30 lines, mechanical.*

The `Skip` and `Assign` cases each manually unfold `compile` and `cfg_path.cases` before producing a witness via `metis` with 5+ arguments. After change (3), these collapse to one-liners from `edge_step_*`.

---

## What NOT to refactor

- The big-picture pipeline (`AST → CFG → eqsys → solver`). It's right.
- The split between `IMP2_Collecting` and `CFG_Collecting`. Clean boundary.
- `cfg_path` carrying actions. Necessary for transfer-function composition.
- `offset_edges` / `offset_path`. Inherent to compound CFG indexing.

---

## Suggested order

1. **Item 1** (drop `_while_rest`) local, isolated, immediate.
2. **Item 5** (`edge_collect` cleanup) small mechanical pass.
3. **Item 3** (edge-step bridge file) enables 2 and 6.
4. **Item 6** (Skip/Assign trims) falls out from 3.
5. **Item 2** (compound `_iff` lemmas) biggest payoff, biggest churn. Do per construct: Seq first (simplest), then If, then While.
6. **Item 4** (`cfg_collect = cfg_path_collect` global) last; touches downstream.

Each item is independent enough to commit on its own. Do not bundle.

---

## Risk register

- Item 2 risks introducing a spurious `iff` that holds only in one direction (e.g., uniqueness of decomposition). Smoke-test by proving the existing splitter lemmas as one-line corollaries.
- Item 4 risks subtle changes in simp-rule firing order downstream. Keep the old lemmas as aliases for one commit cycle.
- Item 6 (and 3) require sledgehammer / `metis` re-discovery on small goals after refactor budget time.
