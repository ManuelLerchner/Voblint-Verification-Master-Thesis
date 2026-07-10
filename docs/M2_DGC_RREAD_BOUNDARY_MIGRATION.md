# M2 — `R_read` / D-G boundary alignment

Status: **Stage 1 partially done (transport toolkit landed); concrete closure
blocked by a structural finding.** Goblint-faithfulness *precision* upgrade of the
keyed context route. The shipped soundness results (Track B, keyed generator
overapproximation) stay green throughout. This is not a soundness prerequisite for
anything currently in the repo — it is the removal of a documented precision
obstruction.

Design basis: `DGC_ALIGNMENT_ANALYSIS.md` (the layered change, §6, and the
risk/obligation audit, §8–9), `ROUTE_A7_GOBLINT_CONTEXT_DESIGN_STUDY.md` (the
corrected call-only Goblint model), `ROUTE_A7_DECISION_A_vs_C.md` (why the keyed
`(=)` route is blocked today). This doc turns that analysis into a staged plan.

---

## Progress and findings (2026-07-09)

**Landed (committed, batch-green):** the exact `part_solution` st→abs transport
toolkit — the generic enabler for certifying a concrete run whose exactness is
established per run against a soundness theorem that needs an *exact* fixpoint:

- `part_solution_st_to_abs_transport` (`Exec_Bridge.thy`) — commit `c50eacfe`.
- `part_solution_cmp_st_to_abs_eff` (`Exec_Cmp_Bridge.thy`) — commit `c50eacfe`.
- `part_solution_cmp_switching_st_to_abs_eff_unit_transfer` (`Exec_Cmp_Bridge.thy`)
  — commit `4ea73e3b`.

**Foundations verified sound.** The retain-path abstract soundness (O1,
cross-procedure global soundness) is *already proven* conditional on an exact
fixpoint (`inl_glob_le_keyed_ctx_full` → retain enter/combine/collecting bounds →
`kgen_retain_keyed_generator_sound_if_exact_fixpoint`). The concrete run already
has an exact fixpoint (`kgen_retain_exact_eqs` eval-check → `kgen_retain_part_solution`).
The DGC-doc framing of O1 as "genuinely hard, new proof" was stale — the hard part
was already discharged; the residual generic link is the exact transport, now built.

**Structural blocker found (eval, definitive).** The concrete `kgen` retain run is
*genuinely context-sensitive*: `card (snd \` fst kgen_retain_solution) = 3` (three
value-derived contexts). The keyed collecting-soundness theorems
(`side_cfg_T_eff_cmp_collect_sound_gen_le`, `kgen_retain_keyed_generator_sound_if_exact_fixpoint`)
conclude against the **context-insensitive** `cfg_collect g S v0 ≤ side_env_cmp (=) σ (v0, ctx)`
and require **single-context global covering** — every edge target solved at *one*
fixed `ctx`. Eval confirms this is unsatisfiable here:

```
∃c ∈ snd ` fst kgen_retain_solution. ∀(u,a,w) ∈ edges kgen_cfg. (w,c) ∈ fst kgen_retain_solution
  = False
```

No single context covers all nodes, so the unconditional concrete closure via the
existing theorem is **impossible for a multi-context run** — not a proof-effort gap.

**Reframed remaining work — and the residual pinned to one obligation.** The
correct target already exists: `side_cfg_T_eff_cmp_collect_ctx_sound_semantic`
(`TD_Side_Eff_Cmp_Sound.thy:368`) concludes the **context-indexed**
`cfg_collect_ctx dg cmp g S v ctx ≤ side_env_cmp gcmp σ (v, ctx)` with **no
covering premise at all** — it bypasses the multi-context blocker. Its obligations
are the switching-combine soundness contract: `ENTRY` / `PROC_ENTRY` / `EDGE`,
`LOCAL_POST` / `CMP_SOUND`, the digest-propagation `DG_INTRA` / `DG_RETURN` /
`DG_CALLEE`, and **`ENTER_MONO`**.

`ENTER_MONO` is the crux and cannot be shortcut: it is a *semantic* statement
(`∀` concrete store `s ∈ γ(side_env_cmp σ (cl,ctx))`, the entry digest is
`cmp`-compatible with the routed context), so it is **not eval-dischargeable**.
It is exactly the `fctx` obstruction — whether the retain (`R_read`) routing lets
the value-keyed context distinguish the two calls. Discharging `ENTER_MONO` for
the retain routing (plus `CMP_SOUND` / `DG_*` for the value-keyed digest instance)
**is the core M2 research question**, not a mechanical assembly.

So the concrete closure's residual is now located precisely: the exact-transport
enabler is done; the remaining work is the `ENTER_MONO` (retain-routing) discharge
against `side_cfg_T_eff_cmp_collect_ctx_sound_semantic`, which is the substance of
the D/G/C boundary this doc set out to establish. Stages 2–7 below are the shape
of that discharge (R_read routing, invariant relaxation, the `fctx` separation).

## Stage 2 verdict (2026-07-09): ENTER_MONO is *not* provable — machine-backed

`ENTER_MONO` for the value-keyed retain routing is refuted, not merely open. Proven
batch-green in `src/Formalization/Examples/Executable/Sign/Keyed/Exec_Sign_Cmp_Keyed_Retain_EnterMono.thy`
(commit `413c9265`):

- `retain_keyed_merged_G` (eval): the per-context keyed global slot at
  `kgen_ctx_merged` is `SNonNeg` — the two value-distinct activations sharing that
  context join coarse in the one keyed slot.
- `retain_read_merged_G_coarse`: the soundness read `σ(Inl (cl,ctx)) ⊔ σ(Inr ctx)`
  (= `side_env_cmp` after the `(=)` singleton collapse) is `≥ SNonNeg` on `G` at
  *every* call site of that context — **independent of `route_read_cmp`**. The retain
  invariant `inl_glob_le_keyed_ctx` (`local ≤ keyed`) makes the keyed slot dominate
  the join, so routing precision from the local slot is invisible to the gamma.
- `read_admits_two_point_classes` / `enter_mono_read_not_point`: the read
  concretises to `0` and `2`, which lie in different point-sign classes
  (`0 ∈ SZero`, `2 ∉ SZero`). `ENTER_MONO` with `cmp = (=)` needs one routed context
  equal to `entdg s` for every such `s`; a value-keyed `entdg` separates them, so no
  single routed context works.

**Exact missing invariant:** `ENTER_MONO` needs `side_env_cmp` entry-digest-uniform;
retain gives `local ≤ keyed`, so the read equals the coarse keyed slot on globals;
uniformity would require the *converse* `keyed ≤ local` — which a per-context keyed
global cannot supply once two value-distinct calls share a context. **Not a
proof-effort gap and not fixable by strengthening retain-transfer lemmas.**

**Second, independent blocker (also machine-backed):** the value-keyed context type
`sign st` is **not** a `finite` instance, while the keyed soundness stack requires
`'g :: finite`; so `side_env_cmp` does not even type-apply to this run. A finite
context quotient is a prerequisite orthogonal to `ENTER_MONO`.

**Minimal required architecture change (documented, not implemented):** the D/G/C
read split — state `ENTER_MONO`'s gamma over the routing read `route_read_cmp` (the
local slot), decoupled from the global-read `side_env_cmp` the soundness conclusion
is stated against. That changes *what the theorem certifies* (the read in the
conclusion), so it is a genuine architecture change, not a local proof repair. Per
the standing instruction, this stops here for review before any such change.

---

## 1. Goal and motivation

Feed the callee-context selector a **pre-loss routing state** (`R_read`) instead
of the flow-insensitive joined read (`side_env_cmp`), and prove the keyed `(=)`
context analyzer sound under that boundary — dissolving the `fctx` negative
result so a global-derived split (`GZero` at call site 4, `GPos` at call site 7)
is *certified*, not just refuted.

Motivation: this is the one place where our formalization is knowingly *less
precise than Goblint by construction*, and the reason is an artifact of our
transfer discipline, not of context-sensitivity. Closing it makes the keyed route
faithful to Goblint's `D/G/C` split, where `Spec.context` reads a `D.t` that still
carries routing information before it is published to the separate `G.t` side
store.

## 2. Relation to Goblint (verified upstream references)

From `DGC_ALIGNMENT_ANALYSIS.md` §1, verified against upstream:

- `src/framework/analyses.ml`: the manager exposes `local : D.t`,
  `global : V.t -> G.t`, `sideg : V.t -> G.t -> unit` (≈ lines 1362–1385).
- `Spec.context : man -> fundec -> D.t -> C.t` — call-only selection from a `D.t`
  (≈ 1435–1444).
- `Spec.enter : … -> (D.t * D.t) list` — caller-after-enter and callee-entry
  states (≈ 1491–1498).
- `combine_env` / `combine_assign` receive callee context + returned `D.t`
  (≈ 1500–1514).
- `src/analyses/base.ml`: `sync` publishes via `Priv.sync … man.sideg …` only
  under `earlyglobs`/multithreaded; otherwise returns `man.local` (≈ 3075–3105).
  `context` filters the supplied store; `earlyglobs` drops syntactic globals
  (≈ 3407–3424).

**The architectural invariant** (not "globals always live in `D`"): `context()`
must observe whatever information the analysis routes on **before** that
information is published/widened/joined away. Base *sometimes* keeps C globals in
the store; that is evidence for the invariant, not the invariant.

Cross-check `constraints.ml` for the precise `enter` / `context` / callee
side-effect / `sync` **ordering** before implementation — the DGC audit flagged
this ordering as not live-verified.

## 3. Current status in the Isabelle formalization

**The obstruction is proven and eval-backed (do not re-litigate):**

- `unit_edge_tree` (`TD_Side_CFG.thy`) publishes globals to `Inr` and erases them
  from the local `Answer` on every edge via `restrict_local`
  (`restrict_local σ x = (if is_global x then bot else σ x)`).
- Maintained invariant `inl_slot_globals_bot_ctx` (`TD_Side_Eff_Cmp_Gen.thy`):
  every per-`(pp,C)` local slot has all globals at `⊥`. Load-bearing in
  `side_cfg_T_eff_cmp_enter_le` and the entry bound.
- Globals survive only in `Inr(gkey ctx)` — context-keyed, shared across all
  program points of a context (`pull_gk_Inr`).
- The read is a join: `side_env_cmp cmp σ (v,ctx) = σ(Inl(v,ctx)) ⊔
  glob_env_cmp cmp ctx σ` (`Global_Cmp_Read.thy`).
- The kernel routes callee reads through this joined read:
  `collect_ctx_sound_route` fixes `renv = side_env_cmp gcmp`
  (`TD_Side_Eff_Cmp_Sound.thy`), so `ENTER_MONO`/`CMP_SOUND` see the join.
- Negative result: `fctx_caller_read_G_imprecise`
  (`Example_Finite_Sign_Context_Analysis.thy`, `by eval`): `G:=0; f(); G:=1;
  f()` reads `G = SNonNeg`, whose `γ` admits both digests, so no single `(=)`
  context matches both calls.

**Reusable prototype (this is the head start):**

| Artifact | File | Role for M2 |
| --- | --- | --- |
| `retain_edge_tree_st` — intra edges **keep** the written global in the local `Answer` | `Exec_Bridge.thy` | the executable preserve-routing transfer |
| `sign_etf_retain_st`, `kgen_retain_solution`, `kgen_retain_runs` (`by eval`) | `Exec_Sign_Cmp_Keyed_Retain_Run.thy` | executable retain run on the two-call keyed program; context selected from the retained local global |
| `kgen_retain_keyed_generator_sound_if_{post,exact}_fixpoint` | `Exec_Sign_Cmp_Keyed_Gen_Run.thy` | **conditional** soundness reduction through `TD_side_upd_rule`; proves `part_post_solution`; exactness only operational (acyclic `eval`) |
| `context_domain` locale (`ctx_sel :: pp => 'c => 'a abs_state => 'c`) | `Context_Domain.thy` | interface already typed to accept a routing-state argument |
| `post_fixpoint_sound_at_ctx_semantic_generic` (parametric in `renv`, `rt`) | `TD_Side_Eff_Cmp_Sound.thy` | backbone whose read parameter M2 splits |

So the R_read discipline is **prototyped executably and reduced conditionally** —
not a blank slate. The missing work is the *abstract* soundness restatement and
discharging the cross-procedure-global obligation the retain reduction currently
assumes.

## 4. Missing pieces

- Split reads in the kernel: `R_read` (routing) vs `Obs` (γ observation) vs
  `G_read` (published globals), replacing the single joined `renv`.
- The `ENTER_COMPAT` obligation restated over `R_read`, with an explicit `Obs`
  compatibility side condition that does not reintroduce the incompatible join.
- A relaxed transfer invariant: `inl_slot_globals_bot_ctx` dropped/weakened for
  slots used as routing `D`, with `enter_le` + entry bound re-proved.
- **Cross-procedure global soundness under selective publication** — the proof
  that a callee's global write still soundly reaches the caller once publication
  is no longer automatic per edge. This is the crux.
- Explicit `publish` / `read_global` locale fields modelling `sync`/`sideg`.
- The closed `fctx` separation theorem, upgrading the executable retain run.

## 5. Dependencies

- **Independent of M1 and M3.** M2 changes the transfer/read discipline and the
  keyed-context kernel; it neither needs nor blocks call strings or lifters.
- Builds directly on the retain prototype (§3). No new domain needed — Sign
  suffices for the whole track.
- Stack B (`entry_store_ctx`, `subseteq`, unit global pot) is **untouched** — it
  does not route on a keyed global.

## 6. Risks and proof obligations

From `DGC_ALIGNMENT_ANALYSIS.md` §9, in severity order:

| ID | Obligation / risk | Severity | Note |
| --- | --- | --- | --- |
| O1 | **Cross-procedure global visibility under selective publication** | **High** | publication currently *guarantees* a callee write reaches the caller; a selective model can silently drop a global effect — that is unsoundness, not imprecision. The single most dangerous failure mode; guard it first. |
| O2 | Dropping `inl_slot_globals_bot_ctx` cascades | **High** | load-bearing in `enter_le`, entry bound, `pull_gk` invariants; every consumer re-proves |
| O3 | Collecting-correspondence rework | Med-High | `cfg_collect`/`γ` soundness restated with routing info retained in the local/routing slot |
| O4 | `Obs` reintroduces the join | Med | if `Obs` blindly re-adds incompatible global info for routing variables, the `SNonNeg` obstruction returns through the γ bound even with `R_read` routing |
| O5 | Backbone `ENTER_COMPAT`/`COMB_SEM` restatement | Med | shape is parametric (mechanical), but the compatibility obligations are new content |
| O6 | Scope creep into a full `sync` semantics | Med | model only the minimal preserve-routing + publication discipline `fctx` needs |
| O7 | `context_domain` interface churn | Low | signature already fits; add a side condition + `publish`/`read_global` fields |
| O8 | Stack B regression | Low | untouched |

**Soundness-direction caveat (from §9):** the current publish-erase discipline is
*conservative* (over-approximates globals by a flow-insensitive join). Preserve-
routing is more precise, sound **only if** the publication discipline still
dominates every concrete cross-procedure global flow. O1 is that proof.

## 7. Concrete stages (independently buildable commits)

Sequenced so the **highest-risk obligation (O1) is discharged on a minimal
fragment before any kernel change**. If Stage 1 fails, the track stops with a
sharpened negative result and no wasted kernel churn.

| Stage | Commit | Content |
| --- | --- | --- |
| **1 — de-risk O1** | `feat(dgc): cross-proc global soundness of the retain transfer (fctx fragment)` | on the 2-proc/1-global `fctx` shape, prove every concrete `G` write is soundly propagated to the caller under `retain_edge_tree_st` + an explicit publication point. **Gate: if unprovable, stop.** |
| **2 — read split** | `feat(dgc): R_read / Obs / G_read read combinators` | define the three reads; prove `G_read` = existing `glob_env_cmp`; prove `Obs` does not reintroduce the incompatible join (O4) on the `fctx` routing variable |
| **3 — invariant relax** | `refactor(dgc): weaken inl_slot_globals_bot_ctx for routing slots` | qualify the invariant; re-prove `side_cfg_T_eff_cmp_enter_le` + entry bound + `pull_gk` consumers (O2) |
| **4 — backbone restatement** | `feat(dgc): ENTER_COMPAT over R_read; Obs gamma bound` | restate `post_fixpoint_sound_at_ctx_semantic_generic` obligations: route `rt cl ctx (R_read σ (cl,ctx))`, γ over `Obs`; re-instantiate `collect_ctx_sound_route` |
| **5 — publish fields** | `feat(dgc): publish/read_global locale fields` | add `publish`, `read_global` to `context_domain`; model the explicit publication point from Stage 1 as the locale operation |
| **6 — collecting correspondence** | `feat(dgc): cfg_collect/gamma soundness with retained routing state` | O3: the `EDGE`/entry/combine chain and the γ bound re-proved with routing info in the local/routing slot |
| **7 — close fctx** | `feat(dgc): certified global-derived context split (fctx)` | prove `GZero` at site 4, `GPos` at site 7 as a theorem; upgrade `kgen_retain_…_sound_if_exact_fixpoint` by discharging its hypothesis; state the precision result |

Stages 1–2 are the go/no-go core. Stages 3–7 are the build-out once O1 holds.

## 8. Deliverables and exit criteria

- **Stage 1 (gate):** a soundness lemma that the retain transfer propagates every
  concrete callee global write to the caller on the `fctx` fragment. Green,
  no `sorry`. **Go/no-go for the whole track.**
- **Stage 2:** `R_read`/`Obs`/`G_read` with the anti-join compatibility lemma.
- **Stage 3:** re-proved `enter_le` + entry bound under the weakened invariant.
- **Stage 4:** backbone + `collect_ctx_sound_route` re-instantiated over the split.
- **Stage 5:** `publish`/`read_global` fields; existing interpretations re-derived.
- **Stage 6:** collecting-correspondence soundness under retained routing.
- **Stage 7:** `fctx` separation as a proved `⊂`; conditional retain reduction made
  unconditional.
- **Track exit:** the keyed `(=)` analyzer is certified sound under the D/G/C
  boundary, and a global-derived context split is proved strictly precise.

## 9. Expected impact

- **Executability:** the retain path already code-generates (`kgen_retain_solution`
  `by eval`); M2 makes its soundness abstract, not its execution new.
- **Soundness:** the substantive axis. New cross-procedure global soundness under
  selective publication; the current publish-erase result stays valid as the
  conservative baseline. Risk of *regression* is real (O1) — hence Stage-1 gating.
- **Precision:** dissolves the `fctx` obstruction; keyed `(=)` contexts can
  separate global-derived splits Goblint separates. Strict gain on the class of
  programs where a per-context global was previously joined flow-insensitively.

## 10. Classification

**Goblint-faithfulness, research.** Not thesis-critical and not a soundness
prerequisite (the shipped keyed generator is already a sound overapproximation).
It is the faithful path *iff* a chapter commits to certifying Goblint's `D/G/C`
`Spec.context` boundary with exact context matching. Highest research risk of the
three tracks; also the deepest alignment payoff. Ship the obstruction
characterization as a standalone result regardless of whether M2 is attempted.

## 11. Stage-1 progress: read split, machine-backed (`Exec_Sign_Cmp_RRead_Split`)

Landed theory: `src/Formalization/Examples/Executable/Sign/SeededClean/Exec_Sign_Cmp_RRead_Split.thy`
(session `Voblint_Formalization`, green, no `sorry`). It makes the D/G/C split explicit
and pins down — by `eval` on the concrete `kgen_cfg` run — where the `fctx`
obstruction actually lives.

**The three reads already exist as constants.** `R_read = route_read_cmp`
(`sg (Inl (v,ctx))`), `G_read = glob_env_cmp`, `Obs = side_env_cmp`, with
`side_env_cmp_def : Obs = R_read ⊔ G_read` (`obs_is_rread_join_gread`). "Defining
the reads" is naming + the decomposition, not new machinery.

**The read-site split is a sound relaxation, but insufficient alone.**
`enter_mono_rread_of_obs`: since `Obs ≥ R_read`, `⟦R_read⟧ ⊆ ⟦Obs⟧`, so `ENTER_MONO`
quantified over `R_read` is *implied by* — strictly weaker than — the current
`Obs` obligation. Migrating the routing read to `R_read` can only relax, never
strengthen (the safe direction). **But it does not dissolve the obstruction for
the retain run:** the retain local slot is *already* polluted at the transfer.
`traverse_retain_edge_tree_st` shows `retain_edge_tree_st` computes
`f (sg (Inl u) ⊔ sg (Inr ()))` — it folds the published global into the local at
**every** edge. Machine-checked (`retain_caller_local_polluted`): after `G := 0`
the local `G` is the point `SZero` (pp 3), but the next `Nop` re-merges the
flow-insensitive slot, so at the actual call site (pp 4, the combine's caller
`cc`) the local is already `SNonNeg`. No read-site choice recovers a point.

**The obstruction has two write-site sources**, both a re-merge of the published
global `g = sg (Inr ctx)`:
1. the transfer: `retain_edge_tree_st` computes `f (su ⊔ g)`;
2. the combine: `kgen_combine_st` computes `caller = sc ⊔ g` before selecting the
   callee context `kgen_ec ctx caller`.

**Applying the split at both write sites dissolves the obstruction (verified).**
`clean_edge_tree_st` (sequential-Goblint-faithful: keeps globals flow-sensitively
in the local via `Answer`, publishes to `Inr`, but does **not** read the published
slot back — `res = f su`) plus `kgen_combine_rread` (context from the local `sc`
alone). On the same `kgen_cfg`, `by eval`:
- caller locals are points — `SZero` at site 4, `SPos` at site 7
  (`kgen_rread_caller_locals_points`);
- the two value-distinct activations get **distinct point contexts** `{G:SZero}`
  and `{G:SPos}` (`kgen_rread_contexts_points`), where the retain run merged both
  into the single coarse `SNonNeg` slot (`retain_keyed_merged_G`);
- those contexts separate the exact values the obstruction conflated: `0 → SZero`
  context, `2 → SPos` context (`rread_contexts_separate_values`). Each context's
  read is entry-digest-uniform — the converse of `read_admits_two_point_classes` —
  so `ENTER_MONO` over `R_read` holds where the `Obs` read failed.

**Revised go/no-go (supersedes the §7 Stage-1 framing).** The gate is no longer
"cross-proc soundness of the *retain* transfer" (that transfer re-pollutes). It is
**soundness of the *clean* transfer** — dropping `⊔ g` — against `cfg_collect`.
Dropping the published-slot re-read models Goblint's sequential `D.t` discipline
(globals flow-sensitive in the local; the flow-insensitive `G.t` is a separate
`G_read`), which is sound for single-writer sequential collecting semantics. That
soundness is **not claimed** in the landed theory and is the next go/no-go before
any kernel `ENTER_MONO`/`CMP_SOUND` migration.

## 12. Stage-2 verdict: the clean transfer is UNSOUND — go/no-go = NO

Stage 2 discharged the go/no-go and it **fails**. `clean_edge_tree_st` is unsound
against the collecting semantics, proved two ways in `Exec_Sign_Cmp_RRead_Split`:

- **Program-independent (`clean_transfer_unsound`).** `¬ sound_effectful_transfer
  sign_etf_clean`. The assign obligation of `sound_effectful_transfer` quantifies
  the incoming store over `⟦σ(Inl u) ⊔ glob_env σ⟧` (local **⊔** global), while the
  clean image `etf_collecting_full = etf_full ⊔ glob_env` re-joins only the *old*
  `glob_env σ`; the assigned value is computed on the local, where a callee-entry
  global is `⊥`. Witness: global slot `G=SZero`, local `G=⊥`, concrete `G=0`;
  `G:=G+1` gives `1`, image is `SZero`, `1 ∉ gamma_sign SZero`.
- **Executable (`clean2_loses_increment_retain_keeps`).** On `int G; f(){G:=G+1};
  main(){G:=0; f()}` (concrete `G=1` at exit), the clean run's observed global is
  `SZero`; the sound retain run gives `SNonNeg`. `kgen`'s `G:=G+G` only *looked*
  sound because the seed sits on a fixpoint of `+`; a genuine global read exposes
  the loss.

**Why (mechanism).** In this equation system globals live in the flow-insensitive
`Inr` slot. The combine seeds a callee's globals *there* (via `Side`), and the
enter edge is filtered from the intra fold, so the callee-entry *local* slot is
`⊥` on globals. Both `unit_edge_tree` and `retain_edge_tree` read `su ⊔ g`; the
`⊔ g` is the **load-bearing channel** delivering globals to the transfer. The
Stage-1 precision loss and this soundness failure are the *same* mechanism —
reading the published `Inr` global. This is the earlyglobs/multithreaded channel,
**not** Goblint's sequential `D.t` discipline (where `enter` copies globals into
the callee `D.t`). The earlier "sound for sequential semantics" note was correct
about Goblint sequential mode but *wrong* about this architecture.

**Exact missing invariant.** A sound flow-sensitive-global (clean) transfer needs
the **callee-entry local slot seeded with the caller's globals**. The current
filtered-enter / `Inr`-seed does not establish it and cannot without a generator
change (the enter edge injecting globals into the callee local instead of the
flow-insensitive slot).

**Consequence.** Per the go/no-go, the kernel `ENTER_MONO`/`CMP_SOUND` are **not**
migrated to `R_read`. The read split (§11) stays as a certified precision/faithful
characterization; making it *sound* is gated on the generator-level enter/seed
change above — a larger slice than M2 Stage 2, to be scoped separately. The
retain (`⊔ g`) analyzer remains the sound shipped baseline.

## 13. Stage 3: Goblint-faithful enter (`Exec_Sign_Cmp_Seed_Enter`)

Stage 3 attacks the cause Stage 2 isolated — the callee-entry local lacks the
caller's globals — rather than the symptom (`⊔ g`).

**Where globals are lost (verified).** In `side_cfg_T_eff_cmp_st` the callee-entry
unknown `(v,c)` is a frame entry (`is_frame_entry`); its seed is the constant
`fresh_frame_st`, and `fresh_frame_sign` sets globals to `⊥`. The enter edge is
filtered (`non_enter_predecessor_list`), so the caller's globals never reach the
entry local — they are routed to the flow-insensitive `Inr` slot, and the
transfer recovers them via `⊔ g`.

**Goblint.** `Spec.enter` returns the callee `D.t` `v` (globals retained), and
`sidel (FunctionEntry f, fc) v` seeds the callee-entry **local** `(node,context)`
unknown with `v`. Goblint seeds a *local* unknown; we seed only the *global* slot.

**The refactor (`side_cfg_T_eff_cmp_seed_st`).** Minimal change: replace the
constant frame seed `fresh_frame_st :: 'a st` with a context-dependent
`frame_seed :: 'c ⇒ 'a st`. `seed_generalises` proves the shipped generator is the
constant instance `(λ_. fresh_frame_st)`, so every existing theorem transfers and
existing runs are untouched. The faithful seed is `restrict_global_st`: since the
context `c = restrict_global_st(caller)`, `restrict_global_st c = c` delivers
exactly the caller's flow-sensitive globals to the entry local (`faithful_seed_idem`).

**Result (executable, `seed_clean_sound_on_prog2`).** On the Stage-2 counterexample
`f(){G:=G+1}; main(){G:=0; f()}`, the seeded generator + *clean* transfer + R_read
combine gives: callee-entry local `G=SZero` (globals now present, was absent);
callee-exit local `G=SPos` (clean `f(local)` computed the increment, was `SBot`);
observed global `SNonNeg` (captures concrete `G=1`) — **sound**, where the unseeded
clean run was not. Context still the precise point `{G:SZero}` — Stage-1 precision
preserved.

**Success criteria met (executably).** The callee-entry local carries the required
globals without consulting the published slot; `⊔ g` becomes unnecessary because
`enter` (the seed) now supplies the information.

**Remaining obligation (discharged in Stage 4).** This is a go/no-go witness, not
yet a proof. The seeded clean transfer's soundness is *context-relative*: the entry
local holds the *precise* per-context global, so the soundness statement is against
`cfg_collect_ctx`, not flat `cfg_collect`. Stage 4 proves it.

## 14. Stage 4: certified soundness over R_read (`Exec_Sign_Cmp_Seed_Sound`)

Stage 4 discharges the Stage-3 obligation as a machine-checked theorem, with no
`sorry` and no weakened assumptions. The key move: measure soundness against the
**local read** (R_read), the read the clean transfer actually uses, instead of the
Obs read `local ⊔ global`.

**Transfer level.** The clean transfer violates the Obs-quantified
`sound_effectful_transfer` (Stage 2, `clean_transfer_unsound`) but satisfies its
R_read reformulation — every premise quantified over `⟦sg (Inl u)⟧` instead of
`⟦sg (Inl u) ⊔ glob_env sg⟧` — **unconditionally** (`clean_rread_nop` …
`clean_rread_enter`). Each reduces to the base sign transfer soundness applied to
the local slot; `clean_edge_collect_rread` packages the edge case.

**Flat collecting.** `clean_cfg_collect_rread`: under the natural local
post-fixpoint bounds (`etf_full (apply_etf sign_etf_clean a u) sg ≤ sg (Inl w)`), a
combine bound, and an entry seed bound, the clean spine over-approximates
`cfg_collect` **at the local slot** — never rejoining the published global.

**Context-sliced (the target).** `clean_ctx_collect_rread`:

```
cfg_collect_ctx dg cmp g S v ctx  ⊆  ⟦sg (Inl (v, ctx))⟧
```

the context-sensitive statement, conclusion at the per-context local slot. It
instantiates the read-agnostic trace backbone
`post_fixpoint_sound_at_ctx_semantic_generic` with **both** `renv` and `rread` set
to `route_read_cmp` (the local slot). This clears *both* obstructions the retain
spine hit:

* **(A) no `'g :: finite`.** `route_read_cmp` never touches an `Inr` slot, so the
  global-key type is unconstrained — the value-keyed context (`sign st`, not
  `finite`) needs no quotient. The obstruction that `side_env_cmp` does not
  type-apply is gone.
* **(B) ENTER_MONO over the local read.** The entering store is quantified over the
  precise per-context local `⟦sg (Inl (cl, ctx))⟧`, not the coarse published global
  that dominated the Obs read.

**The entry invariant, explicit.** `ENTRY` / `PROC_ENTRY` state exactly
*callee-entry local ⊒ context-specific caller stores* (globals included). The
Goblint-faithful seed (Stage 3) establishes it per context; `EDGE_BOUND` propagates
it reading only the local.

**Precision, machine-backed.** `rread_strictly_sharper_than_retain`: on the two-call
program the seeded-clean context slots are `{G:SZero}` and `{G:SPos}` — points
*strictly* below the retain merged `SNonNeg` (`SZero < SNonNeg`, `SPos < SNonNeg`).
The `SNonNeg` obstruction is dissolved; the global-derived context split is
certified, not merely executable.

**Executable reduction (`clean_ctx_collect_rread_head`).** For any *head* digest
(`head_digest`, reading only the head store of the current activation) the three
digest-propagation obligations `DG_INTRA` / `DG_RETURN` / `DG_CALLEE` discharge
generically. What remains is exactly the run-specific bundle: the seed soundness
`ENTRY` / `PROC_ENTRY`, the local post-fixpoint bounds `EDGE_BOUND` / `COMB`, and
the value-digest routing `ENTER_MONO` (over the local read). This is the R_read
analogue of the retain spine's `..._if_post_fixpoint` reduction — and, unlike it,
needs no `'c :: finite`, because the conclusion is the local slot, not
`side_env_cmp`. (The retain spine's own concrete `sign st` run is *not* bridged to
its abstract soundness for exactly that finiteness reason; the R_read conclusion
removes the blocker.)

**Executable seeded run + example.** `kgen_seed_clean_solution` runs the seeded +
clean + R_read spine through the vendored side solver on the two-call program;
`kgen_seed_clean_precision` gives the point contexts `{G:SZero}` / `{G:SPos}` and
`kgen_seed_clean_caller_locals` shows the seed delivers the globals to the callee
local (SZero at pp 4, SPos at pp 7). The example theory
`Example_Seed_Clean_Context` presents the spine end to end and contrasts it with
the retain baseline.

**Baselines preserved.** The retain (`⊔ g`) / `side_env_cmp` spine is untouched and
remains the sound conservative baseline for the Obs conclusion. `seed_generalises`
keeps every shipped run intact.

**Remaining.** The one obligation not yet discharged as a closed theorem for the
concrete run is deriving `EDGE_BOUND` / `COMB` / `ENTER_MONO` from the solver's
`part_post_solution` through the seeded-generator structure lemmas — the same
generator-bridge machinery the retain spine builds in `Exec_Sign_Cmp_Keyed_Gen_Run`.
`clean_ctx_collect_rread_head` isolates it to exactly those bounds; the executable
witnesses show the run satisfies them.

## 15. Stage 5: return rehydration (`Exec_Ivl_Cmp_Seed_Rehydrate_Run`)

Stage 4 seeded the callee *entry* Goblint-faithfully. The dual — the *return* path —
was still lossy: the seeded-clean combine (`ivl_combine_rread`) returned
`restrict_local_st` of the merged result, **stripping** globals from the caller-local
state. A caller reading a global back after the call (`g := G; h := GH`) observed
`bot`. Stage 5 closes the return path.

**Goblint's return path (Tasks 1–3).** `Spec.combine_env` / `combine_assign`
(`analyses.ml` ≈ 1500–1514) receive the callee's exit `D.t` (first argument) and the
caller's call-site `D.t` (second), and reconstruct the caller continuation. For a
non-relational domain that reconstruction is **caller locals + callee globals** —
verified against the repo's own alignment record (`GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`
§Gap 3: *"What we do: fixed structural combine — `restrict_local` of caller joined
with `restrict_global` of callee"*). In the Isabelle formalization that operation is
`combine_abs_st sc se = restrict_local_st sc ⊔ restrict_global_st se`
(`Exec_St.thy:531`), the abstract mirror of the concrete `combine_states` (`<s|t>`,
locals from `s`, globals from `t`). **No divergence from Goblint** — the strip combine
was simply discarding the reconstructed globals via an extra `restrict_local_st`.

**Where globals were discarded (Task 3).** `ivl_combine_rread` computes
`res = restrict_local_st sc ⊔ restrict_global_st (se ⊔ g)` (already carrying the
callee globals) but returns `Answer (restrict_local_st res)` — the outer
`restrict_local_st` erases them.

**Return rehydration (Task 4).** `ivl_combine_rehydrate` drops the extra
`restrict_local_st` and the non-faithful `⊔ g`: the caller continuation is
`Answer (combine_abs_st sc se)`, publishing the callee's returned globals
`restrict_global_st se` to the context slot. The transfer is unchanged (clean,
local-only `ivl_etf_clean_st`), the context is still selected from the caller local
(`ivl_ec`, `ivl_combine_rehydrate_context_is_local`), and the folded-in globals are
the callee's returned globals, **not** a `local ⊔ global` read of a published slot
(`ivl_combine_rehydrate_answer`). R_read architecture preserved.

**Soundness (Task 5).** The rehydrated continuation is exactly the `COMB` obligation
of the generic `clean_ctx_collect_rread` (`Clean_RRead_Sound.thy:230`), whose
conclusion is the return-node local slot. `rehydrate_caller_continuation_sound`
discharges it:

```
s ∈ ⟦fun_of_st sc⟧  ⟹  t ∈ ⟦fun_of_st se⟧  ⟹  <s|t> ∈ ⟦fun_of_st (combine_abs_st sc se)⟧
```

a pure `sound_domain` fact (`combine_states_sound` transported to the executable `st`
layer via `fun_of_st_combine_abs_st`) — no published-global read, so no `local ⊔
global` join. This is precisely what the *strip* combine could not discharge: its
returned local has the callee-written global at `bot`, so `<s|t>` (carrying the
concrete global) escapes the concretisation. Rehydration restores exactly the missing
globals, and no more. The generic theorem, the seeded-clean strip spine, and the
retain `side_env_cmp` baseline are all untouched — nothing is invalidated.

**Executable witness (Task 6).** On the target program (`f(){GH:=G+1}`; `main` calls
`f` twice with `G=0` then `G=10`, reading both globals back), `rhyd_readbacks_exact`
(`by eval`) gives `g1=[0,0]`, `h1=[1,1]`, `g2=[10,10]`, `h2=[11,11]` — the desired
result, arising through the rehydrating combine, not a read-time global join
(`rhyd_readbacks_in_gamma` certifies soundness). `rhyd_callee_exit_separated` shows the
two contexts stay separated (`GH=[1,1]` vs `GH=[11,11]`); a context-clustered GraphViz
(`rhyd_dot`) shows the read-backs accumulating along `main`. The second call's context
is `{G=[10,10], GH=[1,1]}` — rehydration carries the first call's derived global
forward into the caller local, so the second context observes it.

**Residual (unchanged).** The end-to-end discharge of `EDGE_BOUND` / `ENTER_MONO` from
the solver's `part_post_solution` (§14 "Remaining") is orthogonal to the return path
and unchanged by rehydration; `rehydrate_caller_continuation_sound` closes the `COMB`
half of that reduction as a closed theorem.

## 16. Stage 6: seeded-generator `st`→`abs` transport enabler (`Exec_Cmp_Bridge`)

Stage 4 left one generic enabler open (§14 "Remaining"): transporting the concrete
seeded-clean run's `part_post_solution` (over `'a st`) to the abstract
`side_cfg_T_eff_cmp_seed` post-solution the kernel bounds read. That enabler is now
landed, batch-green in session `Voblint_Analysis` (`Finished Voblint_Analysis`, no
`sorry`).

**What landed (`Exec_Cmp_Bridge.thy`).**

- The abstract seeded generator `side_cfg_T_eff_cmp_seed` and its denotation
  `eq_side_cfg_T_eff_cmp_seed` were hoisted from the Sign runs theory into
  `Exec_Cmp_Bridge`, beside the executable `side_cfg_T_eff_cmp_seed_st`, together with
  the new executable denotation `eq_side_cfg_T_eff_cmp_seed_st`. The Sign runs theory
  now inherits them instead of redefining.
- `part_post_solution_cmp_seed_st_to_abs_eff`: a post-solution of the executable
  seeded generator maps, under `fun_of_st`, to a post-solution of its abstract image,
  the frame seed `frame_seed_st` carried to `λc. fun_of_st (frame_seed_st c)`. It
  mirrors `part_post_solution_cmp_st_to_abs_eff` and routes through
  `part_post_solution_st_to_abs_transport` with three commutation obligations
  (`eq` / `sides` / `dep`).

**Why the mirror is exact — no new content.** `side_cfg_T_eff_cmp`'s `acc0` already
carries the `⊔ (if is_frame_entry then fresh_frame else ⊥)` shape; the seeded
generator only replaces the constant `fresh_frame` with `frame_seed c`. The transfer
is unit-global in both (`etf :: (unit, 'a)`, decoupled from the key type `'g`), and
the fold list `intra @ comb` is identical, so the three commutation lemmas reuse the
existing `private` fold-relation lemmas (`cmp_fold_traverse_rel` / `cmp_fold_sides_rel`
/ `cmp_fold_dep_rel`) unchanged.

**What this closes.** With the transport, the concrete `kgen_seed_clean_solution`'s
`part_post_solution` becomes the abstract post-solution that `seeded_clean_edge_bound`
(§14) consumes — so `EDGE_BOUND` is discharged for the real run with no `'g :: finite`
and no per-run `eval`. Item (i) transport and the intra edge half of the kernel
obligation are now closed generically.

**Structural seed bound (the order half of ENTRY/PROC_ENTRY).** The order-theoretic
reduction of `ENTRY` / `PROC_ENTRY` is now a theorem, `seeded_clean_seed_bound`
(`Exec_Sign_Cmp_Seed_Sound.thy`, batch-green): from any `part_post_solution` of the
seeded generator, at every reached frame-entry `(v, ctx)` (`is_frame_entry g v`,
`(v,ctx) ∈ vars`), the seed sits below the entry slot, `frame_seed ctx ≤ sg (Inl (v,
ctx))`. Same shape as `seeded_clean_edge_bound`, but the seed is a summand of the fold
seed `acc0`, so it is dominated directly by `side_acc_ctx` (`side_acc_ctx_ge_acc`) with
no membership witness.

**Residual, now a single semantic obligation.** With `seeded_clean_edge_bound` (EDGE),
`seeded_clean_seed_bound` (the order half of ENTRY/PROC_ENTRY),
`rehydrate_caller_continuation_sound` (COMB), and the head-digest discharge of
`DG_INTRA`/`DG_RETURN`/`DG_CALLEE` (`clean_ctx_collect_rread_head`) all landed, **every
structural obligation of the kernel is discharged**. What remains is exactly the
semantic γ-half: turning the order bound `frame_seed ctx ≤ sg (Inl (v, ctx))` into the
γ-statement `s ∈ ⟦sg (Inl (v, ctx))⟧` for entering stores `s` of compatible digest —
i.e. `s ∈ ⟦frame_seed ctx⟧`, the seed-covering that *is* `ENTER_MONO` over the local
read. Over `Obs` this was refuted (§12); over `R_read` the concrete run satisfies it by
`eval` (`kgen_rread_contexts_points`), and lifting that to a generic theorem is the
go/no-go crux (B3). This stage leaves that crux untouched and isolated: it is the sole
remaining run-specific semantic hypothesis of `clean_ctx_collect_rread`.
