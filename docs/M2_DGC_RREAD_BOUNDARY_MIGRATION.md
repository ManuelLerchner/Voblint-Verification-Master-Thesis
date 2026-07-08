# M2 — `R_read` / D-G boundary alignment

Status: **PLANNED, research. Not started.** Goblint-faithfulness *precision*
upgrade of the keyed context route. Lands on a worktree branch off `main`; the
shipped soundness results (Track B, keyed generator overapproximation) stay green
throughout. This is not a soundness prerequisite for anything currently in the
repo — it is the removal of a documented precision obstruction.

Design basis: `DGC_ALIGNMENT_ANALYSIS.md` (the layered change, §6, and the
risk/obligation audit, §8–9), `ROUTE_A7_GOBLINT_CONTEXT_DESIGN_STUDY.md` (the
corrected call-only Goblint model), `ROUTE_A7_DECISION_A_vs_C.md` (why the keyed
`(=)` route is blocked today). This doc turns that analysis into a staged plan.

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
