# Activation Spine Consolidation

Status: **COMPLETED historical consolidation** (2026-07-17, branch `activation-consolidation`, batch-green).
It records the current implemented `trace_witness_act` spine. The planned semantic endpoint is
[`ACTIVATION_LOCAL_TRACE_CONVERGENCE.md`](ACTIVATION_LOCAL_TRACE_CONVERGENCE.md): `valid_ltr`
becomes the concrete foundation while this document's public DG path is retained.
Enabler: `DG_Ctx_Activation` (commit `b9156f2`, on `main`) — the DG-native
discharge of the activation obligations, now the canonical context-sensitive
proof path.

## Outcome

Executed in four independently batch-green commits:

| Stage | Commit | What |
| --- | --- | --- |
| 1 — extract backbone | `7f5c925` | new `Activation_Backbone.thy` holding `activation_trace_sound` + `activation_collect_sound` (same names/statements); `Seeded_Activation_Sound` and the DG flagship repointed to it |
| 2 — delete probe cluster | `8dbe4be` | removed the 5 SeededClean runs, `Twfr_Reach_Read`, and `Example_Seed_Clean_Context` (a sibling `twfr` probe the original map missed), their empty dirs, ROOT entries, and doc references |
| 3 — delete terminal witnesses | `c9810e6` | removed `Activation_Domain_Instances` + ROOT entry |
| 4 — delete plain family | `129e0b1` | removed `Seeded_Activation_Sound`, `Seeded_Activation_Reach`, `Activation_Witness_From` + ROOT entries; updated `PROOF_OVERVIEW`, `OPEN_PROBLEMS` |
| 5 — delete orphaned kernel | (this commit) | removed `Seeded_Clean_Ctx_Collect` (orphaned by Stage 4) + ROOT entry + doc references |

Net: **~1,900 `.thy` lines removed across 12 files**; one ~155-line backbone
added. Full `Voblint_Soundness` build green after each stage.

Map corrections found during execution:

- `Example_Seed_Clean_Context` (under `Interprocedural/`) was a further `twfr`
  probe sibling not in the original list; folded into Stage 2.
- `Example_Rdiv_Twfr_Sound` (cited in the old `PROOF_OVERVIEW` chain) had already
  been deleted in a prior commit (`9c229ddf`), so it was not a live consumer.
- `Seeded_Clean_Ctx_Collect` was orphaned by Stage 4 (its only consumer was the
  deleted `Seeded_Activation_Sound`): zero importers, its 8 exported lemmas used by
  no surviving theory. Confirmed dead by `git grep Seeded_Clean_Ctx_Collect` /
  `git grep seeded_clean_` (only the theory + ROOT), then **deleted in Stage 5**.
  The live digest base `Clean_RRead_Sound` (imported by `Seed_EnterMono_Lift`, cited
  by `Local_DG`) is unaffected and retained.

Branch for execution: `activation-consolidation`.

## Goal

Collapse the repository onto a **single canonical context-sensitive activation
path** and delete the parallel plain-`abs_state` activation architecture that
predates it.

Implemented end state of this consolidation:

```
CFG_Collect_Activation        (cfg_collect_ctx_act, trace_witness_act)
        |
        v
Activation_Backbone   (NEW slim ~90L: activation_trace_sound + activation_collect_sound)
        |
        v
DG_Ctx_Activation     (locale dg_ctx_activation: dg_ctx_act_edge / dg_ctx_act_comb_covered)
        |
        v
Example_Interval_DG_Ctx_*     (real TD solver, whole-run soundness at every
                               program point vs cfg_collect_ctx_act)
```

Everything in the plain activation + from-node-witness + SeededClean-probe
cluster is removed. Net removal: **~1,500 `.thy` lines across 10 files** (after
retaining the ~90-line backbone).

## Why the plain family goes

The plain family exposes three things; none is load-bearing.

1. **Shared backbone** — `activation_trace_sound` + `activation_collect_sound`
   (`Seeded_Activation_Sound` lines 43–117). Domain- and generator-agnostic;
   uses only `trace_witness_act`. **Kept**, extracted to a slim theory. The DG
   flagship rides it.
2. **Whole-run cover packaging** — `seeded_activation_collecting_sound`,
   `_cover`, `cover_seed`, `seeded_activation_edge`/`seeded_activation_seed`.
   Superseded by `DG_Ctx_Activation`. Only consumer is the terminal
   `Activation_Domain_Instances` witnesses. `cover_seed` also forces callee-entry
   locals to `top` (universal-coverage seed), so it cannot express the precise
   demand-driven context routing the DG spine uses — see
   `DG_Ctx_Activation.thy` header.
3. **From-node returning witness** — `twf`/`twf_sound`/`twf_combine_reuses`
   (entirely dead: `twf.start` used nowhere), `twfr`/`twfr_nonempty` (only in
   hand-built probes), `twfr_sound_seeded` (only terminal witnesses).

### Consumer classification

| Artifact | Lines | Classification |
| --- | --- | --- |
| `Activation_Witness_From` (`twf`, `twf_sound`, `twf_combine_reuses`) | of 214 | dead |
| `Activation_Witness_From` (`twfr`, `twfr_sound_seeded`) | of 214 | obsolete |
| `Seeded_Activation_Reach` | 440 | obsolete (support for `twfr_sound_seeded`) |
| `Activation_Domain_Instances` | 49 | obsolete compatibility artifact (terminal) |
| `Twfr_Reach_Read` | 91 | redundant scaffolding (3-line combinator + `gk` family) |
| `Exec_Ivl/Sign_Cmp_Seed_Enter` | 148+139 | redundant examples (hand-built `twfr`, no solver) |
| `Exec_Ivl/Sign_Cmp_Seed_Sound` | 85+26 | redundant digest-kernel re-exports |
| `Exec_Ivl_Cmp_Seed_..._Keyed_DG_Run` (interval, SeededClean) | 62 | redundant hand-built DG separation probe |
| plain content of `Seeded_Activation_Sound` | ~280 of 395 | obsolete (superseded by `DG_Ctx_Activation`) |

### Findings that justify the cut

- **`Exec_Ivl/Sign_Cmp_Seed_Enter`** demonstrate a `twfr` from-node
  reach-and-read on a **hand-built** witness (`seed_dg` + a two-store trace
  `[gk 0, gk 1]` via `twfr.start`/`twfr.intra`), checked so
  `last tr ''G'' in gamma(slot)`. No TD solver, no `part_post_solution`, no
  invocation of `twfr_sound_seeded`/`twf_sound`. A shape/API probe.
- **Covered elsewhere.** The solver-backed context-sensitive result
  `twice_ctx_collect_ctx_act_sound` (`Example_Interval_DG_Ctx_Collect`, vs
  `cfg_collect_ctx_act` at every program point, real TD post-solution) subsumes
  and exceeds the probes on its own. That result is what supersedes them; it does
  **not** require source-level coverage. The from-node *shape* is not reproduced,
  but nothing real needs it. See "Source-bridge status" below — do not cite a
  source lift for the context-sensitive result.
- **`twf`/`twfr` are not used for current work** — only the two probes and the
  terminal witnesses.
- **A DG-native returning witness would be ~50–80 lines** (a from-node
  induction feeding EDGE/SEED_G/COMB from the `_dg` post-solution, reusing
  `dg_ctx_act_edge`/`dg_ctx_act_comb_covered`) — but it would have no consumer,
  so it is **not built**. Deleting the from-node path changes no theorem anyone
  depends on.

## Retained boundary (NOT this cut)

The live **digest base** `Clean_RRead_Sound` and the **DG-route**
(`DG_Context_Soundness`, `DG_Route_Soundness`) are woven into live generic infra
(`Local_DG`, `Seed_EnterMono_Lift`) and the domain interpretations
(`Interval_DG` / `Sign_DG`, which supply the `ivl_dg` interpretation the DG
flagship needs). They are a *retained spine*, not a parallel one.

(`Seeded_Clean_Ctx_Collect` was originally listed here as retained kernel, on the
assumption it was live infra. Stage 4 removed its only consumer
(`Seeded_Activation_Sound`), leaving it orphaned; Stage 5 deleted it. The
assumption was wrong — it was not woven into anything live.)

Do **not** touch:

- `Exec_Sign_Cmp_Keyed_DG_Run` (`Sign/Keyed/`) — uses the *retained*
  `DG_Route_Soundness`.
- `Exec_Interval_Run` — shared base run.

## Migration steps

Five stages, each a standalone batch-green commit; order matters (extraction
first, orphaned kernel last).

**Stage 1 — extract backbone.** New `Activation_Backbone.thy` (imports only
`Voblint_CFG.CFG_Collect_Activation`) holding `activation_trace_sound` +
`activation_collect_sound`, same names and statements. Make
`Seeded_Activation_Sound` import `Activation_Backbone` and drop its own copies
(single definition, no ambiguity). Repoint `Example_Interval_DG_Ctx_Collect` to
import `Activation_Backbone`. Add to `src/Analysis/ROOT`. Build green.

**Stage 2 — delete obsolete probe/example theories.** Remove the 5 SeededClean
files + `Twfr_Reach_Read` + their `ROOT` entries. Build green. (Lowest risk —
pure example removal.)

**Stage 3 — delete terminal witnesses.** Remove `Activation_Domain_Instances` +
`ROOT` entry. Build green.

**Stage 4 — delete plain family.** Remove `Activation_Witness_From`,
`Seeded_Activation_Reach`, and the remaining `Seeded_Activation_Sound` +
`ROOT` entries. Full batch build + grep for dangling imports, theorem references,
and obsolete terminology.

**Stage 5 — delete orphaned kernel.** Stage 4 orphaned `Seeded_Clean_Ctx_Collect`
(its only consumer was `Seeded_Activation_Sound`). Objective check
(`git grep Seeded_Clean_Ctx_Collect` / `git grep seeded_clean_`: only the theory +
ROOT) confirmed it dead; remove it + its `ROOT` entry + doc references. Build green.

## Files / lines removable

~1,500 `.thy` lines, 10 files:

- `src/Analysis/Generic/Solver/Context/Goblint/Routing/Support/Activation/Activation_Witness_From.thy` (214)
- `src/Analysis/Generic/Solver/Context/Goblint/Routing/Support/Activation/Seeded_Activation_Reach.thy` (440)
- `src/Analysis/Generic/Solver/Context/Goblint/Routing/Support/Activation/Seeded_Activation_Sound.thy` (395, minus ~90 extracted)
- `src/Analysis/Instances/Tooling/Activation_Domain_Instances.thy` (49)
- `src/Soundness/Examples/Executable/Common/Twfr_Reach_Read.thy` (91)
- `src/Soundness/Examples/Executable/Interval/SeededClean/*.thy` (3 files, 295)
- `src/Soundness/Examples/Executable/Sign/SeededClean/*.thy` (2 files, 165)

## Proof risks

Low throughout.

- **Backbone extraction (step 1):** pure move of two theorems with no digest
  dependencies; the example's `activation_collect_sound[OF …]` call is
  unchanged. Only risk is the import repoint.
- **Deletions (steps 2–4):** mechanical, but each must update every `ROOT` and
  leave no dangling import. Reverse deps were grepped: the only non-family
  consumer of anything deleted is the example, and only of the backbone.
  `Interval_DG`/`Sign_DG` import `DG_Context_Soundness`, not the plain family —
  unaffected.

## Splittable into safe green commits?

Yes — the four steps above, in order, each `isabelle build` green
independently. Batch-green is the gate for each commit (not the I/Q checker
alone).

## Source-bridge status (do not overstate)

Two distinct DG results exist; neither connects source runs to the
context-sensitive collecting semantics:

- `twice_ctx_collect_ctx_act_sound` (`Example_Interval_DG_Ctx_Collect`):
  **context-sensitive**, vs `cfg_collect_ctx_act` at every program point,
  solver-backed. **No source-run connection.**
- `twice_source_run_sound` (`Example_Interval_DG_IP_Flagship`): a **source-run
  lift**, but only against the **monovariant** `cfg_collect` — context-insensitive.

The source -> `trace_witness_act` / `cfg_collect_ctx_act` bridge is **missing**:
no theory links `psteps` / `concrete_program_match` to `cfg_collect_ctx_act`
(grep confirmed empty). Building it is a separate feature (a source-to-activation
simulation), tracked apart from this consolidation. The probes are superseded by
the solver-backed context-sensitive result alone; source coverage is not claimed.

## Decisions on record

- **Delete, do not port**, the from-node returning-witness path: no real
  consumer, and a DG re-implementation would serve none.
- **Keep the digest kernel + DG-route** — they are live infra, not a parallel
  architecture. Revisit in a separate Phase 2.
- **A single canonical activation path** is the end state:
  `cfg_collect_ctx_act` -> `activation_collect_sound` -> `dg_ctx_activation` ->
  real solver examples.
