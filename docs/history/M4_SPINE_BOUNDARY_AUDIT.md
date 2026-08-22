# Classic/generic D/G spine boundary audit

Read-only audit. No `.thy` file was edited, no batch build was run, no proof
was written. Every claim below cites the file and line actually read.

**Resolution.** Both of this audit's recommendations were subsequently
implemented and are done, not proposed. The sublocale unification (Section 4:
"the one adapter-shaped gap that is real and is worth scoping") landed in
commit `fa1dd790` — `sound_dg_spec <= hooks: sound_dg_hooks` and `<= hooks_ltr:
sound_dg_hooks_ltr`, plus a proof that `dg_gen = hook_gen` for the adapter
instance, closing the one genuine duplicate-proof-stack this audit found,
with zero example changes. The two unnecessary migrations this audit judged
"net-negative churn" (`Exec_Sign_DG_Run.thy`, `Example_Parity_DG_Flagship.thy`)
were reverted in commit `95ff7132`, back to their classic `sound_dg_spec`
form, with all reusable framework infrastructure the migration produced kept
intact. `docs/reviews/M4_MIGRATION_CHECKLIST.md` records the closure.

## 0. Question this audit answers

The migration checklist (`docs/reviews/M4_MIGRATION_CHECKLIST.md`) paused
after two example migrations produced large size growth (`Exec_Sign_DG_Run.thy`
158->997 lines, confirmed by `git show --stat 57d2b377` as 88 deletions/958
insertions against a 158-line original; `Example_Parity_DG_Flagship.thy`
269->1336 lines, confirmed by `git show --stat 31574413` as 128
deletions/1254 insertions net to a 269-line original) for a generic
abstraction (issue #81) that only bought back ~2-3% of that growth
(`Exec_Sign_DG_Run.thy` 1028->997, `Example_Parity_DG_Flagship.thy`
1370->1336, per the checklist's own "Validated deduplication" note).

The working hypothesis: the actual architectural risk the original PR review
flagged was duplicate proof stacks at the *definition* level, already fixed
in commit `865cbe10` (`unit_dg_spec` redefined as `unit_dg_spec_for
is_global`, `Split_State.thy`'s dead layer removed -- confirmed by `git show
--stat 865cbe10`: touches `DG_Framework.thy`, `Split_State.thy`,
`Exec_DG_Bridge.thy`, `DG_Soundness.thy`, `TD_Side_CFG.thy`). If true, forcing
every example onto `sound_dg_hooks`/`sound_dg_hooks_ltr` was never required to
close that risk, and `sound_dg_hooks` should be understood as a low-level
framework-construction API rather than the everyday user-facing one.

**Verdict: the hypothesis is true, with one qualification.** Every classic
constant task 1 was asked to classify is either architecture-neutral,
already reduced to the generic layer by an unconditional definitional
bridge, or a bare compatibility name. The one constant pair that is a
genuine, still-open independent implementation --
`restrict_local_resolved_q`/`restrict_global_resolved_q` -- is executable-layer
infrastructure, not something an example file calls directly for its own
soundness claim in a way that per-example migration would fix; the fix for
it is rerouting a small number of infrastructure call sites, not migrating
Sign/Interval/Parity/CallString examples to hooks. No example family audited
in task 3 relies on an independent-implementation duplicate in a way that
migration would resolve.

## 1. Constant classification

Legend: **independent implementation** (separately-proven, does not reduce to
the generic layer) / **thin specialization** (defined as, or bridged by a
one-line unconditional equation to, the generic `_for`/`_placed` layer at
`gs = is_global`) / **compatibility name** (bare alias, no independent
content) / **obsolete** (dead, safe to delete).

| Constant | File:line | Classification | Evidence |
| --- | --- | --- | --- |
| `dg_spec` | `DG_Framework.thy:414` | architecture-neutral (not classic-specific at all) | `record ('dl,'dg) dg_spec = dgs_nop :: ... dgs_combine_assign :: ...` -- a plain record of transfer functions, no classifier field, no key-type parameter. Used identically by the classic `unit_dg_spec`, by `dg_gen_of`, and by CallString's own hand-rolled `Spoly :: (sign exec_dg_st, sign exec_dg_st) dg_spec` (`Example_Sign_DG_CallString_K1.thy:69`). Keep permanently; nothing to migrate. |
| `sound_dg_spec` | `DG_Soundness.thy:135-156` | **not classic-fixed** -- `gs` is a locale parameter, same shape as `sound_dg_hooks` | `locale sound_dg_spec = fixes S ... and gammaDG ... and gs :: "vname => bool" assumes ... step_sound ... combine_sound ... enter_sound`. Every classic INFRA file interprets it generically: `Sign_DG.thy:47 sublocale sign_dg_api \<subseteq> sound_dg_spec_ltr "unit_dg_spec sign_tf" gamma_unit`, `Interval_DG.thy:43`, `Mixed_Sign_Interval.thy:118`, and `Rel_Order_Domain.thy:436 interpretation rel_order: sound_dg_spec rel_order_spec gammaDG_rel is_global` (own relational carrier, zero `abs_state`). Its own `dg_gen` abbreviation (`DG_Soundness.thy:208-215`) is fixed to `(pp \<times> unit, unit, ...) eqsT`, same restriction as `hook_gen` -- see boundary audit below. |
| `sound_dg_hooks` / `sound_dg_hooks_ltr` | `DG_Soundness.thy:799-808`, `DG_LTR_Sound.thy:134-144` | **independent implementation relative to `sound_dg_spec`/`sound_dg_spec_ltr_for`, structurally isomorphic but not derived** | Both prove the same shape of theorem (`ltr_collect gs g S0 v \<subseteq> ... gamma ... v`, four-case proof via `ltr_collect_semantic_postfix`) but as two textually separate locales over two separate tree representations (`dg_spec`-record trees built by `apply_dg_spec`/`dg_spec_combine_tree`/`dg_enter` vs. arbitrary hook trees). See Section 2 for whether this is closeable. |
| `unit_dg_spec` | `DG_Framework.thy:585-588` | **thin specialization** | `definition unit_dg_spec :: "'a domain_transfer => ('a abs_state,'a abs_state) dg_spec" where "unit_dg_spec tf = unit_dg_spec_for is_global tf"`, plus `lemma unit_dg_spec_for_is_global: "unit_dg_spec_for is_global tf = unit_dg_spec tf"` (`:590-592`, `by (rule refl)`). Literal definitional identity, not a derived equality -- the pre-`865cbe10` hand-duplication the original PR review flagged is gone. |
| `dg_gen_of` | `Exec_DG_Bridge.thy:2392-2398` | architecture-neutral (parametric in `S`, no classifier at all) | `dg_gen_of S g bot0 s0d s0g = side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. ()) (\<lambda>_ _ _ _. ()) (dg_cmb_of S) (dg_extra_of S g) g S bot0 s0d s0g`. Structurally identical to `sound_dg_spec`'s own locale-internal `dg_gen` (`DG_Soundness.thy:208-215`) but as a free top-level constant so callers can build the equation system before interpreting any soundness locale. Used by `Example_Interval_DG_IP_Flagship.thy` per the checklist ("own `dg_gen_of`; baseline the Ctx/CallString family builds on"). No `gs`/`is_global` dependency anywhere in its definition -- not a classic-route-specific constant, nothing to migrate. |
| `fun_of_dg_st` | `Exec_DG_Bridge.thy:51-54` | **thin specialization** | `definition fun_of_dg_st d = DG (fun_of_exec_dg_st (locals d)) (fun_of_exec_dg_st (globs d))`, where `fun_of_exec_dg_st` is itself an *abbreviation* `fun_of_exec_dg_st \<equiv> fun_of_resolved_st_q_for is_global` (`:22-24`). Bridge: `lemma fun_of_dg_st_for_is_global: "fun_of_dg_st_for is_global = fun_of_dg_st"` (`:427-429`, `by (rule refl)` after unfolding). |
| `fun_of_exec_dg_st` | `Exec_DG_Bridge.thy:22-24` | **compatibility name** | Pure `abbreviation`, not even a `definition` -- literally `fun_of_resolved_st_q_for is_global` with no independent body at all. |
| `fun_of_exec_dg_st_for` | `Exec_DG_Bridge.thy:403-405` | architecture-neutral rename | `definition fun_of_exec_dg_st_for gs = fun_of_resolved_st_q_for gs` -- a bare rename of the actually-generic `Exec_St.thy:1171` constant, kept so D/G-layer call sites use D/G-layer vocabulary. |
| `dg_tree_st_commute` | `Exec_DG_Bridge.thy:3570-3578` | **thin specialization** | Body uses `fun_of_dg_st` directly (`fun_of_dg_st (traverse_rhs t_st \<sigma>_st) = ...`). Bridge: `lemma dg_tree_st_commute_for_is_global: "dg_tree_st_commute_for is_global = dg_tree_st_commute"` (`:3606-3609`, `unfolding ... fun_of_dg_st_for_is_global by (rule refl)`). |
| `restrict_local_resolved_q` / `restrict_global_resolved_q` | `Exec_St.thy:1070-1078` | **independent implementation** (real, structural, not merely un-bridged) | `lift_definition restrict_local_resolved_q ... is restrict_local_resolved`, with `lookup_restrict_local_resolved_q: lookup_resolved_st_q (restrict_local_resolved_q s) loc = (case loc of Local_Location x => lookup_resolved_st_q s loc | Global_Location x => bot)`(`:1080-1084`). This is an **unconditional, unscoped** tag-based split with the classic *policy* baked in (every local kept, every global dropped) -- not classifier-parametric (it operates on already-resolved`location`tags, downstream of whatever classifier produced them) and not scope/`universe`-parametric the way`project_resolved_on`/`project_resolved_on_strict` are. The only connection to the new machinery is a **conditional** pointwise lemma, `lookup_project_resolved_on_classic_local`(`Exec_Placement.thy:1083-1103`), which requires`target \<in> set (universe @ effective_support (rep_resolved_st s))` as a hypothesis -- not an unconditional identity like the three rows above. This condition is not an artifact of an unfinished proof: outside a state's effective support, `lookup_resolved_st_outside_effective_support`(`Exec_Placement.thy:289-291`) returns`resolved_default s loc`, which is not always`bot` (it is `top` for a placement-completed state) -- so `restrict_local_resolved_q` and `project_resolved_on ... classic_keep_local` genuinely disagree outside the relevant scope in general, not just unverified. The comparison lemma's only consumers are `Exec_DG_Bridge.thy:1813,1841`(`lookup_placed_dg_edge_tree_classic_local/side`), which are a standalone reduction check ("new route collapses to old route's known output under the classic policy") -- not load-bearing for either route's own soundness theorem. Each route's actual soundness argument depends on its own separately-proven lemma family (`fun_of_resolved_st_for_restrict_local/global` for classic; `lookup_project_resolved_on_*` for placement); a bug in one would not silently propagate through the other. Still heavily used: `Exec_Bridge.thy`,`Call_String_Solver_Refinement.thy` (per the PR review's own count, "dozens of sites"). |

## 2. The four architectural boundaries

### Generator construction

`dg_gen_of`/`sound_dg_spec.dg_gen` (dg-spec-record route) and
`hook_gen` (`DG_Soundness.thy:856-865`, inside `sound_dg_hooks`) are both
thin instantiations of the same representation-neutral combinator,
`side_cfg_T_eff_keyed_seed_dg`/`side_cfg_T_eff_keyed_seed_trees`
respectively -- both ultimately reduce to `Finite_Set.fold`-based joins over
the CFG's own predecessor/call lists (the project's locked "Joins" decision).
Neither hardcodes `is_global`; both hardcode the *key type*
`(pp \<times> unit, unit, ...)`. This is architecture-neutral infrastructure at
this boundary -- no independent-implementation risk here.

### Hook (transfer/combine/enter) soundness

This is where the real duplication lives, and it is at the **locale** level,
not at any of the nine audited constants. `sound_dg_spec`'s three assumptions
(`step_sound`, `combine_sound`, `enter_sound`, `DG_Soundness.thy:143-156`) and
`sound_dg_hooks`'s three assumptions (`edge_hook_sound`, `enter_hook_sound`,
`combine_hook_sound`, `DG_Soundness.thy:812-842`) prove the same shape of
per-step obligation over two different tree representations
(`dg_spec_step`/`apply_dg_spec` vs. arbitrary `edge_tree`/`combine_tree`/
`enter_tree`). Checked directly whether the former reduces to an instance of
the latter: `apply_dg_spec S a u = dg_edge_tree (dg_spec_step S a) u`
(`DG_Framework.thy:442-446`), and `DG_Ctx_Activation.thy:76-110`
(`edge_tree_local_ctx`/`edge_tree_global_ctx`) already proves, for the
key-generalized case, that `locals (traverse_rhs (map_gtree ... (apply_dg_spec
S a u)) sigma) = snd (dg_spec_step S a ...)` -- exactly the reduction
`sound_dg_hooks`'s `edge_hook_sound` conclusion needs to specialize down to
`sound_dg_spec`'s `step_sound`. **`sound_dg_spec` is, in principle, an
instance of `sound_dg_hooks`** with `edge_tree u a v = map_gtree (\<lambda>_. ())
(map_ltree (\<lambda>w. (w,())) (apply_dg_spec S a u))` and the analogous
`combine_tree`/`enter_tree` -- the reduction lemmas needed already exist in
`DG_Ctx_Activation.thy` for the key-generalized version, just not wired as a
`sublocale sound_dg_spec \<subseteq> sound_dg_hooks ...`. This unification has **not
been done**; the two locales are proved independently today (confirmed:
`DG_LTR_Sound.thy:14-70` and `:134-...` share zero proof text, only the same
four-case skeleton). This is a genuine, still-open duplicate-proof-stack risk
-- but at the *framework* level, fixable in one `sublocale` interpretation
inside `DG_Soundness.thy`, not by touching any example.

### Executable/abstract transport

`dg_refines_on`/`complete_abs_on`/`le_lift_if_dg_refines_on_and_le`
(placement route) and `fun_of_dg_st`/`dg_tree_st_commute` (classic route,
Section 1 above) are not siblings solving the same problem: the classic route
never needed a finite/total bridge (its executable carrier read back through
one fixed classifier, unconditionally, no owner-scoped materialization), so
there is nothing here to reduce -- `fun_of_dg_st`/`dg_tree_st_commute` are
already the `is_global` instance of the exact same `_for`-parametric
readback the placement route also uses (`fun_of_resolved_st_q_for`, shared).
The one real independent-implementation pair at this boundary is
`restrict_local_resolved_q`/`restrict_global_resolved_q` vs.
`project_resolved_on`, per Section 1.

### Final collecting theorem

`dg_post_solution_collect_sound_ltr`/`dg_post_solution_collect_sound_ltr_for`
(`DG_LTR_Sound.thy:48-69`, `:107-128`) and
`hook_post_solution_collect_sound_ltr` (`DG_LTR_Sound.thy:192-...`) are the
end products of the two independently-proven locales above; they inherit
whatever duplication exists one layer down and add nothing of their own
beyond the `part_post_solution`/coverage bookkeeping, which is itself generic
(`part_post_solution_of_ball`, issue #81, `DG_Soundness.thy`, applies
identically regardless of which locale produced the `part_post_solution`
fact).

## 3. Per-family decision

For every classic-route example family, the test is: does the example's own
proof depend on `restrict_local_resolved_q`/`restrict_global_resolved_q`'s
independent-implementation status *as a soundness risk*, i.e. would a latent
bug in one silently corrupt the other's already-proved theorem? Per Section
1, the answer for every family is **no** -- each classic instance's own
theorem is discharged entirely through `sound_dg_spec`'s self-contained
`step_sound`/`combine_sound`/`enter_sound` chain (or, for CallString/Ctx,
through `dg_ctx_activation`/`routed_context`, which extend `sound_dg_spec`
via locale inheritance and reuse its facts directly -- see below), never
through a fact that also depends on `project_resolved_on`'s correctness.

- **Sign (flagship + CallString K1/K2).** Flagship: was migrated
  (`57d2b377`); it relied on nothing classified independent-implementation
  before migration (`unit_dg_spec`, `fun_of_dg_st`, `dg_tree_st_commute` were
  all already thin specializations at the time, since `865cbe10` landed
  first). CallString K1/K2: bypass `sound_dg_spec`'s `dg_gen` entirely and
  build their equation system with `side_cfg_T_eff_keyed_seed_dg` directly
  over `(pp \<times> cfg_node list, gk_1, ...)` keys (`Example_Sign_DG_CallString_K1.thy:90`),
  discharging soundness through `dg_ctx_activation`/`routed_context`
  (`:372,407`, interpretation), which are `sound_dg_spec S gamma_unit gs`
  extended with context/key polymorphism (`DG_Ctx_Activation.thy:18-20`,
  `locale dg_ctx_activation = sound_dg_spec S gamma_unit gs + ...`) --
  confirmed by direct inspection that `edge_tree_local_ctx`/
  `edge_tree_global_ctx` unfold `dg_spec_step`/`apply_dg_spec`, i.e. reuse
  `sound_dg_spec`'s own per-step facts, not re-derive transfer soundness.
  **No independent-implementation dependency; do not migrate.**
- **Parity.** Migrated flagship (`31574413`) relied on nothing
  independent-implementation for the same reason as Sign's flagship. **Would
  not have needed migration on soundness/drift grounds.**
- **Interval (flagship, IP flagship, CallString/Ctx variants).** All classic,
  all route through `sound_dg_spec_ltr "unit_dg_spec ivl_tf" gamma_unit`
  (`Interval_DG.thy:43`) or, for CallString/Ctx, through
  `dg_ctx_activation`/`routed_context` the same way Sign's CallString does
  (same `pp \<times> cfg_node list`/`gk_1` key shape, same locale-extension
  structure -- confirmed the pattern is identical across both domains'
  CallString files by direct `rg` inspection). **No independent-implementation
  dependency in any Interval variant; do not migrate any of them.**
- **Mixed.** `Mixed_Sign_Interval.thy` interprets `sound_dg_spec_ltr
  mixed_si_spec gamma_dg` (`:118`, own combined `dg_spec`).
  `Rel_Order_Domain.thy` interprets `sound_dg_spec rel_order_spec
  gammaDG_rel is_global` directly (`:436`, own relational carrier, not even
  `abs_state`-typed) -- itself a clean demonstration that `sound_dg_spec` was
  already built to be domain-representation-agnostic, "with zero
  [`abs_state`] dependency" (the file's own section header, `:5`).
  `Example_Relational_DG_Demo.thy` composes `Rel_Order_Domain` +
  `Interval_DG` under one more classic `dg_gen_of`. **No
  independent-implementation dependency; do not migrate.**

**Is `sound_dg_hooks`/`sound_dg_hooks_ltr` a low-level framework-construction
API rather than the everyday user-facing one?** Yes, and the evidence is
direct, not inferential: `sound_dg_spec` already exists as exactly the
"classic adapter" `unit_dg_spec` packages at the generator layer -- a locale
that is fully generic in the classifier (`gs` is a plain parameter, not
`is_global`-fixed) and that every ordinary analysis instance (Sign, Interval,
Parity's own `Interval_DG.thy`/`Sign_DG.thy` pattern once it gets one, Mixed,
the relational demo) interprets with one `sublocale`/`interpretation` line
plus its own `step_sound`/`combine_sound`/`enter_sound` proofs. The migrated
Sign and Parity flagships, by contrast, had to manually discharge, per CFG
node: a `raw`/transport-agreement hypothesis for every action kind
(`dgEx_se_edge`/`parity_se_edge`, wrapping `placed_hook_se_edge`), a
join-node counterpart that did not previously exist and had to be built as
part of this migration (`placed_hook_se_join_edge`, `Exec_DG_Bridge.thy`,
commit `121fd0e5`), and, even after issue #81, a per-node `dep\<^sub>L \<subseteq> vars`
`have` for every CFG node individually (the checklist's own words: "per-node
work is still domain-specific `have`s ... not part of this issue's scope").
None of that per-node manual work exists on the `sound_dg_spec` route: an
instance proves three locale obligations once, generically over every node
and edge action, and `dg_postfix`'s eight conjuncts
(`DG_Soundness.thy:292-318`) are then discharged automatically for the whole
CFG by `dg_postfix_edgeD`/`dg_postfix_enterD`/`dg_postfix_combineD`, not
node-by-node. This is the concrete shape of the size blowup the checklist
observed, and it is a direct consequence of `sound_dg_hooks` requiring a
per-node hook-tree instance and a per-node transport proof, where
`sound_dg_spec` requires neither.

## 4. Recommendation

**Delete or convert:** nothing in the nine audited constants needs deletion.
`unit_dg_spec`, `fun_of_dg_st`, `fun_of_exec_dg_st`, `dg_tree_st_commute` are
correctly-shaped thin specializations already; `dg_spec`/`dg_gen_of` are
correctly architecture-neutral; nothing here is a stale duplicate.
`restrict_local_resolved_q`/`restrict_global_resolved_q` should **not** be
deleted (dozens of live consumers, and each route's own soundness proof does
not depend on the other's), but the follow-up the original PR review already
named (Section 9: "route `Exec_Bridge.thy`'s and
`Call_String_Solver_Refinement.thy`'s direct uses ... through
`project_resolved_on`") remains the correct, bounded fix if this pairing is
ever to stop being an independent implementation -- it is infrastructure work
inside two files, not an example-by-example migration.

**Stay exactly as-is:** every constant in the "thin specialization" and
"architecture-neutral" rows of Section 1, and every classic example family
audited in Section 3. All of Sign (flagship + CallString), Interval
(flagship, IP flagship, CallString, Ctx), Parity's classic pattern, and Mixed
remain sound, non-duplicated, and correctly specialized on the classic route
today.

**Were the two completed migrations worth it, in retrospect?** No, on the
evidence gathered here. `Exec_Sign_DG_Run.thy` and
`Example_Parity_DG_Flagship.thy` were already fine on the classic route
before migration -- neither depended on anything this audit classifies as an
independent implementation. The 5-6x size growth bought a second data point
that the hook route works for a straight-line and a one-join-node program,
and produced one genuinely reusable library addition
(`placed_hook_se_join_edge`) plus the issue #81 assembly generalization,
which any *future, actually-necessary* hook-route example will benefit from.
But neither migration closed a soundness or drift risk that existed before
it ran; both examples' pre-migration classic-route theorems were already
proved through the same generic, classifier-parametric `sound_dg_spec`
machinery every other classic example uses. Given the size cost and the
absence of a closed risk, this was net-negative churn relative to the
project's own "generalize in place, do not duplicate" mandate -- it
generalized correctly (per issue #81) but generalized something that did not
need a second, parallel user-facing route in the first place.

**Is a "classic adapter" worth building?** Not in the sense the paused
migration was attempting (an adapter that lets classic examples call
`sound_dg_hooks` concisely) -- `sound_dg_spec` already *is* that adapter, and
has been since before this PR review cycle; nothing needs building for
Sign/Interval/Parity/Mixed to keep using it. The one adapter-shaped gap that
*is* real and *is* worth scoping as future work is the Section 2 finding:
`sound_dg_spec` (and, transitively, `sound_dg_spec_ltr`) is not yet expressed
as an interpretation of `sound_dg_hooks`, despite the reduction lemmas needed
for it already existing in `DG_Ctx_Activation.thy`
(`edge_tree_local_ctx`/`edge_tree_global_ctx`). Building that `sublocale`
would collapse the one genuine duplicate-proof-stack risk this audit found,
with zero changes to any example file (every consumer keeps interpreting
`sound_dg_spec`/`sound_dg_spec_ltr` exactly as today). A scoping note for
that future task: it would need (a) `edge_tree`/`combine_tree`/`enter_tree`
instantiated to the `dg_spec`-wrapped shape shown in Section 2, (b) the three
`sound_dg_hooks` assumptions discharged from `sound_dg_spec`'s
`step_sound`/`combine_sound`/`enter_sound` via the existing
`DG_Ctx_Activation.thy` reduction lemmas (generalized off their current
`ctx`-indexed form back to the plain `unit`-keyed case `sound_dg_spec` uses),
and (c) a check that `hook_gen`/`dg_gen`'s two independently-defined
`(pp \<times> unit, unit, ...)` equation systems can be shown equal (or that one is
simply dropped in favor of the other) once the locale relationship is live --
this last point is not yet verified either way and should be the first thing
that future task confirms, not assumed.

**Separately, on the CallString/Ctx blocker specifically:** the migration
checklist's framing ("no context-sensitive/call-string generalization of
this locale anywhere in the repo today") is not quite accurate --
`dg_ctx_activation`/`routed_context` (`DG_Ctx_Activation.thy`,
`Routed_Context.thy`) are exactly that generalization, already built,
already proven, and already used by every classic CallString/Ctx example in
the repository. They generalize `sound_dg_spec`, not `sound_dg_hooks`. If
`sound_dg_hooks` is ever unified with `sound_dg_spec` per the paragraph
above, `dg_ctx_activation`/`routed_context`'s existing key-polymorphic
machinery would very plausibly transfer to the hooks route with much less
new proof engineering than building an equivalent from scratch -- but that is
downstream of the unification, not a substitute for it, and remains
unattempted and unverified here.
