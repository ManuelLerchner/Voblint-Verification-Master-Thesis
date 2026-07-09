# M2 seeded-clean example migration — report

Per-example evaluation of whether each executable example should move to the
certified **seeded-clean (R_read)** spine (`Exec_Sign_Cmp_Seed_Sound`), or stay on
its current routing. No mechanical replacement was done; each example was judged on
whether it models Goblint's sequential `D/G/C` semantics.

## Executive summary

**Zero pre-existing examples were migrated.** None of them model the sequential
`D/G/C` caller-local-seeding architecture the seeded-clean spine implements: the
context-keyed sign examples each deliberately study a *different* architecture axis
(a `side_env_cmp` obstruction, digest-keyed writes, the global read layer), and the
remaining examples have no context dimension to key (flat IP / intra) or use a
domain the certified clean spine does not yet cover (interval). The seeded-clean
spine's dedicated example, `Example_Seed_Clean_Context`, was added in the prior
slice and is the Goblint-faithful default going forward.

Three keyed-sign examples received **documentation cross-references** marking them as
retained baselines and pointing to the seeded-clean default; one also got a
disambiguating note (see "Proof / doc changes"). All are pure `text` additions — no
proof changed, full `Voblint_Analysis` + `Voblint_Formalization` green.

## All examples inspected

| Example | Spine / mechanism | Models sequential D/G/C? | Decision |
| --- | --- | --- | --- |
| `Example_Seed_Clean_Context` | seeded-clean (R_read) | **yes** | already on new spine (prior slice) |
| `Example_Finite_Sign_Context_Analysis` | keyed `side_env_cmp` + `fctxu` value-refined ctx | no — obstruction study | **retain** + cross-ref |
| `Example_Sign_Mode_Digest` | keyed vs digest-keyed *writes* | no — digest-writer study | **retain** + cross-ref |
| `Example_Global_Ctx_Read_Precision` | `glob_env_cmp` read layer | no — read-layer witness | **retain** + disambig note |
| `Example_Mode_Value_Digest_Showcase` | value-carried digest read (interval) | no — digest-reader, interval | retain (interval) |
| `Example_Interval_Mode_Digest` | interval digest context | no — interval | retain (interval) |
| `Example_Interval_Recursion_Digest` | interval recursion digest | no — interval | retain (interval) |
| `Example_Interval_Recursion_Origin` | interval per-origin widening | no — interval | retain (interval) |
| `Example_Interval_Side_Proc_Global` | interval IP side | no — interval | retain (interval) |
| `Example_Inc_Proc` | CFG collecting runs | no — collecting level | n/a (no abstract spine) |
| `Example_Side_Proc_Global` | `side_analyse_eff` (flat IP) | no — monovariant IP | n/a (no context) |
| `Example_Side_Execute` | `sign_exec` (intra) | no — intra | n/a (no context) |
| `Example_Side_Branch_Calls` | `sign_exec` (intra) | no — intra | n/a (no context) |
| `Example_Mixed_Flow_Sign` | `side_analyse_eff` / `side_cfg_T_eff` | no — flat IP | n/a (no context) |
| `Example_Proc_Call` | interval IP + graphviz | no — interval | retain (interval) |
| `Example_Proc_GraphViz` | CFG rendering | no — rendering | n/a |
| `Example_Digest_Pipeline_Showcase` | pipeline/graphviz showcase | no — rendering/showcase | n/a |
| `Example_Entry_Store_Context_Precision` | entry-store context (graphviz) | no — entry-store scheme | n/a |
| `Example_Sign_Mode_Digest` (dup above) | — | — | — |
| `Example_Trace_Digest_Precision` | trace collecting | no — collecting level | n/a |
| `Example_Trace_Digest_Combine` | trace collecting | no — collecting level | n/a |
| `Example_Trace_Digest_ReachingCompat` | trace collecting | no — collecting level | n/a |
| `Example_IMP2_Coverage` | interval coverage | no — interval | retain (interval) |
| `Example_Interval_Loop_Coverage` | interval loop coverage | no — interval | retain (interval) |
| `Example_Guard_Refinement` | interval guard refinement | no — interval | retain (interval) |

## Which examples were migrated

None of the pre-existing examples. `Example_Seed_Clean_Context` (added in the prior
slice) is the seeded-clean spine's example and remains the Goblint-faithful default.

## Which were intentionally left, and why

**Keyed-sign examples — different architecture axis (comparison baselines):**

* **`Example_Finite_Sign_Context_Analysis`** — an *obstruction study* of the keyed
  flow-insensitive global: it proves `ENTER_MONO` unprovable because the observation
  read `side_env_cmp = local ⊔ global` pins `G` to `SNonNeg`, then prototypes a
  *value-refined caller context* fix (`fctxu`, an intra-edge context update).
  Migrating would delete the obstruction study that motivates the fix. The
  seeded-clean spine is the Goblint-faithful *alternative* resolution of the same
  obstruction (seed the callee local, read only R_read); the `fctxu` value-refined
  contexts are an orthogonal finite-context axis. Cross-reference added.

* **`Example_Sign_Mode_Digest`** — a before/after study of two keyed-global *write*
  disciplines (context-keyed vs digest-keyed, Goblint's `sideg (G, Digest.compute
  d)`). This is the digest-writer axis, distinct from caller-local D/G/C seeding.
  The before/after is its pedagogical content. Cross-reference added.

* **`Example_Global_Ctx_Read_Precision`** — a *read-layer* witness for
  `glob_env_cmp` (the cmp-filtered global read, G_read). It uses no generator run at
  all — a hand-built `wsig` isolates the read discipline. Not a spine candidate.
  Disambiguating note added (below).

**Interval examples** — the certified clean spine is currently **sign-only**
(`sign_etf_clean_st`, `kgen_combine_rread`). No interval seeded-clean transfer is
proved, so interval examples cannot migrate without new soundness work. Left as-is.

**Flat-IP / intra examples** (`Example_Side_*`, `Example_Inc_Proc`,
`Example_Mixed_Flow_Sign`, `Example_Side_Execute`) — use `side_analyse_eff` /
`side_cfg_T_eff` / `sign_exec`, which are **monovariant** (no `(node, context)`
dimension). There is no context to key, so the seeded-clean context-keyed generator
does not apply.

**Trace / rendering examples** — operate at the collecting-semantics or GraphViz
level, below/beside any abstract routing choice.

## Proof / doc changes required

No proof changed. Three `text`-block documentation additions:

1. `Example_Finite_Sign_Context_Analysis` — architecture note: retained as the
   `side_env_cmp` obstruction study; seeded-clean is the D/G/C-faithful alternative.
2. `Example_Sign_Mode_Digest` — architecture note: retained as the digest-writer
   study; seeded-clean is the sequential model.
3. `Example_Global_Ctx_Read_Precision` — **disambiguation** (the one potential
   confusion): the example's "the seeded caller-local split is unsound" claim refers
   to `Exec_Sign_Ctx_Seeded_Run`, which seeds from the caller **local**
   (`restrict_local_st`, erased by `enter_state`) → genuinely unsound. The certified
   *seeded-clean* spine seeds from the caller **global** (`restrict_global_st`,
   preserved by `enter_state`) → sound (`clean_ctx_collect_rread`). The note pins
   this distinction so the unsoundness claim is not over-read as applying to the
   seeded-clean spine.

## Examples whose behavior changed

None. All edits are documentation. Executable witnesses and `by eval` results are
byte-for-byte unchanged; the full build is green.

## Remaining reliance on `side_env_cmp` routing

`side_env_cmp` (the Obs read `local ⊔ global`) remains the **sound conservative
baseline** and is still used by, intentionally:

* the certified keyed/retain soundness stack — `TD_Side_Eff_Cmp_Sound`
  (`post_fixpoint_sound_at_ctx_semantic_cmp*`), `TD_Side_Eff_Cmp_Gen`,
  `TD_Side_Eff_Cmp_Pull`, `Global_Cmp_Read`, `Digest_Global_Read`,
  `Value_Digest_Reader`;
* the retain run files — `Exec_Sign_Cmp_Keyed_*`, `Exec_Sign_Ctx_Seeded_Run`,
  `Exec_Sign_Mode_Value_Run`;
* the three keyed-sign examples above, as documented baselines.

These are not migration debt: the seeded-clean spine is the Goblint-faithful spine
for the *sequential* model, while `side_env_cmp` is the correct read for the keyed
flow-insensitive (earlyglobs / multithreaded-style) global, which Goblint also has.
Both are kept. The seeded-clean spine is the default for new sequential D/G/C
examples; `side_env_cmp` stays where the flow-insensitive keyed global is the
intended model or the conservative comparison.
