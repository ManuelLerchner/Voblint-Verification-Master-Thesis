# M2 seeded-clean example migration — report

Per-example evaluation of whether each executable example should move to the
certified **seeded-clean (R_read)** spine (`Exec_Sign_Cmp_Seed_Sound`), or stay on
its current routing. No mechanical replacement was done; each example was judged on
whether it models Goblint's sequential `D/G/C` semantics.

## Executive summary

**One example was migrated** (additively): `Example_Finite_Sign_Context_Analysis`.
Its program `fctx_prog` (`f() { GH := G }`, called twice under distinct globals) is a
Goblint sequential `D/G/C` scenario. The seeded-clean (R_read) spine was run on it as
the certified primary resolution — `GH` splits `SZero`/`SPos` per context, and the
caller read of `G` is a *point* (`SZero`/`SPos`) strictly below the `SNonNeg` the
`side_env_cmp` observation read is stuck at. The prior `side_env_cmp` obstruction
study and the `fctxu` value-refined-context prototype are **preserved as the
conservative baseline and comparison**.

The other keyed-sign examples were **not** migrated — they model *different*
architecture axes (digest-keyed writes, the global read layer), and the remaining
examples have no context dimension to key (flat IP / intra) or use a domain the
certified clean spine does not yet cover (interval). `Example_Seed_Clean_Context`
(prior slice) remains the seeded-clean spine's dedicated demonstration.

Two keyed-sign examples received **documentation cross-references** marking them as
retained baselines and pointing to the seeded-clean default; one got a disambiguating
note (see "Proof / doc changes"). Full `Voblint_Analysis` + `Voblint_Formalization`
green after every step.

## All examples inspected

| Example | Spine / mechanism | Models sequential D/G/C? | Decision |
| --- | --- | --- | --- |
| `Example_Seed_Clean_Context` | seeded-clean (R_read) | **yes** | already on new spine (prior slice) |
| `Example_Finite_Sign_Context_Analysis` | keyed `side_env_cmp` + `fctxu` + **seeded-clean** | **yes** (`fctx_prog`) | **MIGRATED** (additive; baselines kept) |
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

**`Example_Finite_Sign_Context_Analysis`** — migrated *additively*. Its program
`fctx_prog` is a Goblint sequential D/G/C scenario (a procedure reads a global under
two calling contexts). A new **Migration** section runs the certified seeded-clean
spine on it (`side_cfg_T_eff_cmp_seed_st id kgen_combine_rread restrict_global_st
fctx_cfg sign_etf_clean_st …`):

* `fctx_seed_clean_runs` — the spine solves the program (side solver).
* `fctx_seed_clean_split` (`by eval`) — context `{G:SZero}` → `GH = SZero`, `{G:SPos}`
  → `GH = SPos`: the same precise separation the `fctxu` prototype achieves, now on
  the spine whose soundness is *proved* (`clean_ctx_collect_rread`), not prototyped.
* `fctx_seed_clean_caller_G_exact` (`by eval`) — the caller read of `G` is the point
  `SZero` at call 4, `SPos` at call 7.
* `fctx_seed_clean_strictly_sharper` — those points are **strictly below** the
  `SNonNeg` the `side_env_cmp` observation read is pinned to
  (`fctx_caller_read_G_imprecise`): a strict precision improvement, and exactly the
  `ENTER_MONO`-enabling exactness the obstruction study identified as missing.

The prior `side_env_cmp` obstruction study and the `fctxu` value-refined-context
prototype are preserved unchanged as the conservative baseline and the comparison.
`Example_Seed_Clean_Context` (prior slice) remains the seeded-clean spine's
standalone demonstration.

## Which were intentionally left, and why

**Keyed-sign examples — different architecture axis (comparison baselines):**

* **`Example_Sign_Mode_Digest`** — a before/after study of two keyed-global *write*
  disciplines (context-keyed vs digest-keyed, Goblint's `sideg (G, Digest.compute
  d)`). This is the digest-writer axis, distinct from caller-local D/G/C seeding.
  The before/after is its pedagogical content. Cross-reference added.

* **`Example_Global_Ctx_Read_Precision`** — a *read-layer* witness for
  `glob_env_cmp` (the cmp-filtered global read, G_read). It uses no generator run at
  all — a hand-built `wsig` isolates the read discipline. Not a spine candidate.
  Disambiguating note added (below).

**Interval examples** — interval is a full peer of Sign on the seeded-clean spine,
both in soundness and execution. The D/G/C *soundness* spine is domain-generic
(`Clean_RRead_Sound`, proved under `sound_transfer tf`) and instantiated for interval
in `Exec_Ivl_Cmp_Seed_Sound` (`ivl_clean_ctx_collect_rread`,
`ivl_clean_ctx_collect_rread_head`) with no interval-specific proof. The *executable*
interval seeded-clean run now also exists (`Exec_Ivl_Cmp_Seed_Clean_Run`): the
generic seed generator `side_cfg_T_eff_cmp_seed_st` and clean edge
`clean_edge_tree_st` (both lifted to the generic layer) with the interval
`ivl_etf_clean_st` / `ivl_combine_rread`, run through the vendored side solver on a
non-recursive two-call program, with stable `by eval` witnesses. The retain /
`side_env_cmp` (Obs) interval examples remain as the conservative baseline; their
loop / recursion imprecision is **widening/narrowing-related**, not D/G/C-related —
see "Interval D/G/C soundness vs widening precision" below.

**Flat-IP / intra examples** (`Example_Side_*`, `Example_Inc_Proc`,
`Example_Mixed_Flow_Sign`, `Example_Side_Execute`) — use `side_analyse_eff` /
`side_cfg_T_eff` / `sign_exec`, which are **monovariant** (no `(node, context)`
dimension). There is no context to key, so the seeded-clean context-keyed generator
does not apply.

**Trace / rendering examples** — operate at the collecting-semantics or GraphViz
level, below/beside any abstract routing choice.

## Proof / doc changes required

**`Example_Finite_Sign_Context_Analysis`** — one new import
(`Voblint_Analysis.Exec_Sign_Cmp_Seed_Sound`), a rewritten header note (the program
is now framed as a D/G/C scenario analysed three ways), and a new **Migration**
section with five `by eval` / `by simp` facts (above). No existing proof changed; all
prior lemmas (`fctx_*`, `fctxu_*`) are untouched.

Doc-only `text`-block additions elsewhere:

1. `Example_Sign_Mode_Digest` — architecture note: retained as the digest-writer
   study; seeded-clean is the sequential model.
2. `Example_Global_Ctx_Read_Precision` — **disambiguation** (the one potential
   confusion): the example's "the seeded caller-local split is unsound" claim refers
   to `Exec_Sign_Ctx_Seeded_Run`, which seeds from the caller **local**
   (`restrict_local_st`, erased by `enter_state`) → genuinely unsound. The certified
   *seeded-clean* spine seeds from the caller **global** (`restrict_global_st`,
   preserved by `enter_state`) → sound (`clean_ctx_collect_rread`). The note pins
   this distinction so the unsoundness claim is not over-read as applying to the
   seeded-clean spine.

## Examples whose behavior changed

**`Example_Finite_Sign_Context_Analysis`** — improved. It now additionally
demonstrates the certified seeded-clean spine resolving `fctx_prog` with a strict
precision gain: the caller read of `G` drops from `SNonNeg` (the `side_env_cmp`
observation) to the exact per-call-site points `SZero`/`SPos`. No prior result
regressed — the existing `side_env_cmp` and `fctxu` witnesses are unchanged. Every
other example's behavior is unchanged (remaining edits are documentation).

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

## Interval D/G/C soundness vs widening precision

The seeded-clean spine is domain-generic: `Clean_RRead_Sound` proves the clean
transfer, the five R_read obligations, the flat theorem `clean_cfg_collect_rread`,
the trace kernel `clean_ctx_trace_rread`, and the context-sliced
`clean_ctx_collect_rread` / `clean_ctx_collect_rread_head` under a single
`sound_transfer tf` assumption. Sign and interval are both thin instantiations —
`sign_etf_clean = clean_etf_of_transfer sign_tf`,
`ivl_etf_clean = clean_etf_of_transfer ivl_tf` — and the interval spine
(`Exec_Ivl_Cmp_Seed_Sound`) follows from `ivl_is_sound_transfer` with **no
interval-specific proof**.

The three obligations that carry domain/analysis content map to Goblint's
`Spec` interface:

| Obligation | Goblint |
| --- | --- |
| `ENTRY` / `PROC_ENTRY` (callee-entry local ⊒ context-specific caller stores) | `Spec.enter` |
| `ENTER_MONO` (routing context selected from the callee local `D`) | `Spec.context` |
| `COMB` (procedure-return reassembly) | `Spec.combine` |

**The boundary.** D/G/C soundness is orthogonal to interval precision. The
context-sliced theorem concludes the R_read local slot soundly over-approximates
`cfg_collect_ctx` for *any* post-solution meeting the enter / context / combine
obligations — at every program point, regardless of how coarse that solution is. On
programs with loops the coarseness is set by the widening / narrowing operators of
`abstract_domain` (`widen_state`, warrowing), not by the R_read split. Concretely:

* `Example_Interval_Loop_Coverage` proves the loop head `[0,20]` — the `[0,19]` body
  refinement plus the joined `20`. That the bound is `[0,20]` and not tighter is
  `assume_ivl` + join + the loop shape, i.e. a widening/guard matter.
* `Example_Interval_Recursion_Digest` / `Example_Interval_Recursion_Origin` widen `G`
  toward `[0, +inf]` / top under warrowing; recovering per-depth precision is a
  narrowing/origin question.

None of these imprecisions is a D/G/C artefact — confirmed executably.
`Exec_Ivl_Cmp_Seed_Clean_Run` runs the interval seeded-clean spine on a
non-recursive, loop-free two-call program and the D/G/C machinery is **exactly
precise**: the seed delivers each caller's `G` into the callee-entry local
(`[0,0]` / `[10,10]`, `iseed_callee_entry_seeded`), the clean transfer reads only
that local and computes the sound increment (`[1,1]` / `[11,11]`,
`iseed_callee_increment` + `iseed_increment_in_gamma`), and the two activations stay
at distinct points (`iseed_contexts_separate`). Where a loop or recursion *is*
present, the coarsening is the solver's widening/warrowing, orthogonal to this run:
`Example_Interval_Recursion_Digest` widens `G` to `[0, +inf]` under monovariant
Apinis warrowing (its own "genuine wall" — a warrowing matter, not a D/G/C one), and
`Example_Interval_Loop_Coverage` stabilises the loop head at `[0,20]` by guard
refinement and join. The retain / `side_env_cmp` interval examples remain the
conservative baseline. The interval seeded-clean spine — generic soundness
(`ivl_clean_ctx_collect_rread`), executable run, and precision witnesses — is
certified and `sorry`-free.
