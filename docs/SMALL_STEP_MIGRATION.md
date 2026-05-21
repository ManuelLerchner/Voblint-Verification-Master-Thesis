# Small-Step Migration Plan

**Decision:** 2026-05-19 (meeting 3 §E + KB `wiki/concepts/semantics-style-tradeoffs.md`).
**Goal:** replace big-step IMP semantics with HOL-IMP-style small-step. Re-key collecting on `(pp, σ)` configurations. Make per-program-point soundness the **native** statement of the pipeline.
**Non-goal:** changing the solver interface, the abstract domains, or the CFG representation. Only the IMP-side concrete semantics and the IMP↔CFG bridge change.

See also:
- `~/goblint-formalization-kb/wiki/concepts/semantics-style-tradeoffs.md` — full rationale + worked div-by-zero example
- `~/goblint-formalization-kb/wiki/meetings/2026-05-18-meeting3.md` §E — decision record
- HOL-IMP `Small_Step.thy` — canonical template for the new semantics
- HOL-IMP `Collecting.thy` — Nipkow's `lfp step` collecting (matches our CFG side already)

---

## Migration scope (proof-repo audit, 2026-05-19)

39 `big_step` mentions across 9 `.thy` files. Two categories:

**Definition sites** (rewrite once):
- `src/IMP2/IMP2_Semantics.thy` (6) — relation definition + determinism theorem
- `src/Goblint_Formalization.thy` (7) — root imports / re-exports
- `src/IMP2/IMP2_Collecting.thy` (1) — `collect c S = { t. ∃s∈S. (c,s) ⇒ t }`

**Consumer sites** (rewrite or collapse):
- `src/CFG/CFG_Collecting.thy` (15) — bridge lemmas; most should **collapse** (see Phase 2), not get rewritten 1:1
- `src/Solver/TD_Soundness.thy` (3) — `terminates: big_step (c,s) t` assumption
- `src/Pipeline/Pipeline.thy` (3) — `pipeline_sound`, `sign_pipeline_sound_scaffold`, `ivl_pipeline_sound`
- `src/Examples/Example_CFG_Collecting_Equiv.thy` (2) — demo
- `src/Equations/Constraint_System_Sound.thy` (1), `src/CFG/IMP2_to_CFG.thy` (1) — leaf constructor mentions

Solver side (`Domains/`, TD locales, `make_rhs_tree`, `td_analyse`, `solve_dom`, `is_post_fixpoint`, `post_fixpoint_sound`) **untouched** — abstraction is semantics-agnostic.

---

## Strategy: keep both semantics permanently

`small_step` is added **alongside** `big_step`, not as a replacement. End state of the migration: both relations live in `IMP2_Semantics.thy`, with `small_step_big_step_eq` as the official bridge. Roles:

| Predicate | Role | Used by |
|---|---|---|
| `big_step :: com × store ⇒ store ⇒ bool` | **Specification side** — "program denotes this final state" | Hoare-logic compatibility, `code_pred` executable interpreter, exit-only corollaries of the pipeline theorem |
| `small_step :: com × store ⇒ com × store ⇒ bool` | **Operational basis** — "program reaches this configuration" | `pipeline_sound_small_step` (canonical top-level), per-pp soundness, intermediate-point safety properties, future trace-sensitive domains |
| `small_step_big_step_eq` | **Bridge** between the two | Any consumer that needs to switch perspectives |

Equivalence lemma to carry through Phase 1:
```isabelle
lemma small_step_big_step_eq:
  "(c, s) ⇒ t ⟷ (c, s) →* (SKIP, t)"
```
Proved once in `IMP2_Semantics.thy` (standard HOL-IMP result). Used as an `iff` rewrite at every site that needs to swap views.

**Why both, not one.** `big_step` keeps Hoare-logic comparability and clean executability open; `small_step` enables per-pp soundness as the native statement. The cost of keeping `big_step` is ~50 lines + the equivalence lemma + the existing `big_step_determ` theorem — all one-time, no ongoing maintenance. The benefit is that every exit-only corollary, every Hoare-style spec, every code-extraction demo stays a one-liner via the bridge. Full rationale: `~/goblint-formalization-kb/wiki/concepts/semantics-style-tradeoffs.md` §"Reasons to keep both".

**Migration invariant.** `main` builds green at every commit. `big_step` is never deleted at any phase. Phase 5 is **pruning dead lemmas**, not retiring the predicate.

---

## Phase 0 — preparation (½ day)

1. Create branch `small-step-migration` from `main`.
2. Open issue tracking each phase; link to this doc.
3. Tag current `main` as `pre-small-step` for easy rollback / before/after metrics.
4. Read HOL-IMP `Small_Step.thy` + `Collecting.thy` cover-to-cover; note any constructors/lemmas to crib.

**Exit criterion:** branch exists, tag pushed, `Small_Step.thy` understood.

---

## Phase 1 — add small-step alongside big-step (~2 days)

**Touches:** `src/IMP2/IMP2_Semantics.thy` only.

1. Append a new section "Small-Step Semantics" to `IMP2_Semantics.thy`. Mirror HOL-IMP `Small_Step.thy` for our extended IMP (`Minus`, `Times`, `Or`, `Eq` — no new structural rules, just reuse `aval`/`bval` we already have).
2. Define:
   ```isabelle
   inductive small_step :: "com × store ⇒ com × store ⇒ bool" (infix "→" 55)
   abbreviation small_steps (infix "→*" 55) where
     "cs →* cs' ≡ star small_step cs cs'"
   ```
   Rules: `Assign`, `Seq1`, `Seq2`, `IfTrue`, `IfFalse`, `WhileTrue`, `WhileFalse` (latter two via the standard while-unfolding pattern).
3. Prove standard meta-theorems:
   - `small_step_deterministic`
   - `small_step_big_step_eq` (terminating ⇔ `→* (SKIP, t)`)
   - `star_step1`, `star_trans`, etc. (likely already in `HOL-Library` via `Star.thy` — import, do not duplicate)
4. `code_pred small_step .` for executability parity.

**Exit criterion:** `IMP2_Semantics.thy` builds; `small_step_big_step_eq` proved; no other file touched.

---

## Phase 2 — re-derive `collect` and the IMP↔CFG bridge on small-step (~3-4 days, hardest phase)

**Touches:** `src/IMP2/IMP2_Collecting.thy`, `src/CFG/CFG_Collecting.thy`.

The structural payoff lives here. Today's `IMP2_Collecting.thy` defines:
```isabelle
definition collect :: "com ⇒ store set ⇒ store set" where
  "collect c S = { t. ∃ s ∈ S. (c, s) ⇒ t }"      -- exit only
```
Bridge lemma (`cfg_collect_exit_eq_collect`) translates this to per-pp on the CFG side via path induction. Painful precisely because of the style mismatch.

**Plan:**
1. Add a new definition next to `collect`, keyed on program points:
   ```isabelle
   definition collect_pp_src :: "com ⇒ store set ⇒ com × store set"
     -- reachable (residual command, store) configurations
   -- or equivalently, keyed by CFG pp via to_cfg embedding:
   definition collect_at :: "com ⇒ store set ⇒ pp ⇒ store set" where
     "collect_at c S p =
        { σ. ∃ s ∈ S. ∃ c'. (c, s) →* (c', σ) ∧ resid_pp c c' = p }"
   ```
   Need an auxiliary `resid_pp :: com ⇒ com ⇒ pp` mapping residual commands to program points in `to_cfg c`. HOL-IMP has analogous machinery in `Small_Step.thy` (`small_step_cs_acom` etc.); adapt.
2. Prove the new per-pp ↔ CFG bridge:
   ```isabelle
   lemma cfg_collect_eq_collect_at:
     "cfg_collect (to_cfg c) S p = collect_at c S p"
   ```
   This is the structural payoff: both sides are `lfp` of a per-pp step function. Expect this proof to be **shorter** than the current `cfg_collect_exit_eq_collect` chain — see notes in `~/goblint-formalization-kb/wiki/concepts/semantics-style-tradeoffs.md` §"Nipkow's lfp step parallel".
3. Derive the old exit-equivalence as a **corollary** (keep it; consumers in `Pipeline.thy` still use it during migration):
   ```isabelle
   corollary cfg_collect_exit_eq_collect_via_small:
     "cfg_collect (to_cfg c) S (cfg_exit (to_cfg c)) = collect c S"
     -- uses cfg_collect_eq_collect_at + small_step_big_step_eq
   ```
4. Audit `CFG_Collecting.thy:867+` (the `WHILE compound paths` block from the path-induction era). Many lemmas there are scaffolding for the big-step bridge and become dead once the new lemma lands. **Do not delete yet** — mark with a `(* SS-MIGRATION: candidate for removal *)` comment, prune in Phase 5.

**Exit criterion:** `cfg_collect_eq_collect_at` proved sorry-free; old `cfg_collect_exit_eq_collect` still builds (as corollary or original); `IMP2_Collecting.thy` + `CFG_Collecting.thy` build green; no consumer yet changed.

---

## Phase 3 — switch `Pipeline.thy` to small-step framing (~2 days)

**Touches:** `src/Pipeline/Pipeline.thy`, `src/Solver/TD_Soundness.thy`.

Today's top-level theorem `pipeline_sound` carries `assumes terminates: big_step (c, s) t`. The companion `pipeline_invariant_sound` does **not** depend on big-step at all — it already proves the per-pp invariant
```isabelle
∀v. cfg_collect (to_cfg c) {s} v ≤ γ_state (run_analysis cfg c v)
```
which is the small-step soundness statement modulo the `cfg_collect` ↔ `collect_at` identity proved in Phase 2.

**Plan:**
1. Add a new top-level theorem next to `pipeline_invariant_sound`:
   ```isabelle
   theorem pipeline_sound_small_step:
     assumes …same TF/init/cfi/solver assumptions as pipeline_invariant_sound…
       and reaches: "(c, s) →* (c', σ)"
     shows "σ ∈ γ_state (run_analysis cfg c (resid_pp c c'))"
   ```
   Proof: discharge by `pipeline_invariant_sound` + `cfg_collect_eq_collect_at`.
2. Rephrase `pipeline_sound` (exit-only) as a **corollary** of `pipeline_sound_small_step` via `small_step_big_step_eq`. Keeps the existing `sign_pipeline_sound_scaffold` / `ivl_pipeline_sound` corollaries working unchanged.
3. In `TD_Soundness.thy`, the three `big_step` mentions are all `terminates:` assumptions on existing theorems. Add small-step-shaped variants next to them (do **not** delete the originals yet — sign chain still uses them).

**Exit criterion:** `pipeline_sound_small_step` proved; `pipeline_sound` re-derived as corollary; sign + interval scaffolds still build; full repo green; `solve_dom` and TD locales untouched.

---

## Phase 4 — re-derive sign chain on small-step (~1-2 days)

**Touches:** `src/Pipeline/Pipeline.thy` (sign + ivl scaffolds), `src/Equations/Constraint_System_Sound.thy`, `src/Examples/Example_CFG_Collecting_Equiv.thy`.

1. Restate `sign_pipeline_sound_scaffold` and `ivl_pipeline_sound` using `(c, s) →* (c', σ)` premise (or directly the per-pp invariant — preferred). Old exit-shape statements remain as corollaries.
2. Update example file to demonstrate the new framing. Add the **div-by-zero loop example** from the KB tradeoff page as `Example_NonTerminating_Safe.thy` — concrete payoff showcase. Suggested skeleton:
   ```isabelle
   theory Example_NonTerminating_Safe
     imports Pipeline
   begin
     definition prog where
       "prog ≡ ''x'' ::= N 10 ;;
                WHILE (Less (N 0) (N 1)) DO
                  (''y'' ::= Div (N 100) (V ''x'') ;;
                   ''x'' ::= Plus (V ''x'') (N 1))"
     -- requires Div in aexp; if out of scope for current IMP2 syntax,
     -- replace with a different intermediate-point safety property
     -- (e.g. "x > 0" at the body entry of any non-terminating loop).
     lemma "∀ (c', σ). (prog, s₀) →* (c', σ) ⟶ σ ''x'' > 0" by …
   end
   ```
   **Note:** our current `aexp` does not include `Div`. If we keep it out of scope (status quo), pick a different intermediate-point safety property — e.g. *"`x ≥ 10` at every iteration of the loop body"*, which interval analysis still proves and which is still impossible to state under big-step.
3. `Constraint_System_Sound.thy` leaf usage — one constructor mention. Trivial swap.

**Exit criterion:** sign pipeline soundness sorry-count unchanged or lower (regression check: `make` + `PROOF_PHASES.md` §Sorry inventory); new `Example_NonTerminating_Safe.thy` builds.

---

## Phase 5 — prune dead lemmas, finalise roles (~½ day)

**Touches:** all files touched above. `big_step` itself is **not** removed.

1. Inventory `big_step` usage after Phase 4 (`/opt/homebrew/bin/rg -n "big_step" src/`). Classify each hit:
   - **Keep as-is**: definition + `big_step_determ` + `code_pred big_step` in `IMP2_Semantics.thy`; `small_step_big_step_eq` bridge.
   - **Keep as corollary**: the old `pipeline_sound` (exit-only, big-step shape), sign/ivl exit-only scaffolds — these stay alive as one-line corollaries of `pipeline_sound_small_step` via the bridge.
   - **Prune**: lemmas that only existed to support the old IMP↔CFG bridge (the `WHILE compound paths` scaffolding in `CFG_Collecting.thy:867+`, plus any per-construct big-step↔walk lemmas tagged `(* SS-MIGRATION: candidate for removal *)` in Phase 2). Removing them must not break any Phase 4 theorem.
2. Confirm role split is clean: `big_step` appears only in (a) its definition + meta-theorems, (b) the bridge lemma, (c) exit-only corollaries, (d) `code_pred` demos. It must **not** appear in any new theorem statement introduced by this migration.
3. Add a short header comment block to `IMP2_Semantics.thy` documenting the two-predicate convention (spec vs operational) so future readers don't try to delete `big_step` thinking it's vestigial.
4. Update `docs/ROADMAP.md`, `docs/PROOF_PHASES.md`, `docs/PROOF_OVERVIEW.md`, `docs/HOL_IMP_COMPARISON.md` to reflect: (i) the new top-level theorem is `pipeline_sound_small_step`, (ii) big-step is retained as the specification-side predicate, (iii) the bridge lemma is `small_step_big_step_eq`.

**Exit criterion:** dead bridge scaffolding pruned; both predicates documented with their respective roles; corollaries cover the old big-step exit-only shape; no `sorry` regressions; `make` green; docs updated.

---

## Phase 6 — KB sync (~½ day, KB repo)

Done from `~/goblint-formalization-kb/`:
1. Update `wiki/concepts/collecting-semantics.md`: add the small-step / per-pp definition (`Collect_at(pp) = { σ | (c, s₀) →* (c', σ) ∧ resid_pp c c' = pp }`) **alongside** the existing big-step exit-only one. Both formulations are live; mark them as "specification side" vs "operational side" and reference the bridge lemma.
2. Update `wiki/research/decisions.md` § Language & semantics: mark the small-step decision as **landed**. Wording: *"Pipeline soundness is stated against small-step; big-step retained as the specification-side predicate via `small_step_big_step_eq`."*
3. Update `wiki/concepts/soundness.md`: the canonical statement is now per-pp small-step; the exit-only big-step form is documented as a derived corollary.
4. Update `wiki/concepts/semantics-style-tradeoffs.md` §"Verdict": replace the "switch to small-step" verdict with a "both, with roles" verdict that mirrors the **Strategy** table at the top of this document.
5. `python3 tools/cross_link.py --apply` + `python3 tools/check_links.py`.
6. Append to `wiki/log.md`: `## [YYYY-MM-DD] migration | small-step landed end-to-end; big-step retained as spec-side predicate`.

---

## Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| Phase 2 `collect_at` definition needs auxiliary structure (`resid_pp`) not yet in repo | Medium | Crib `Small_Step.thy` from HOL-IMP; if `resid_pp` proves brittle, fall back to indexing collecting directly by `→*`-prefix length |
| `cfg_collect_eq_collect_at` proof is harder than expected (path-induction by another name) | Medium | Keep `cfg_collect_exit_eq_collect` as a fallback corollary derived via `small_step_big_step_eq`; pipeline still closes even if the cleaner per-pp lemma is sorried |
| `WHILE compound paths` block in `CFG_Collecting.thy` turns out to be load-bearing | Low | Phase 5 prunes only after Phase 4 builds green — if removal breaks something, restore and leave a `(* kept: still used by X *)` comment |
| Sign/ivl scaffolds need a fresh tf-soundness flavour for per-pp framing | Low | `pipeline_invariant_sound` already takes per-pp shape — TF lemmas in `Domains/` are already pp-agnostic |
| Code extraction (`code_pred`) breaks | Low | Keep `big_step` per Phase 5 option (a); extraction unaffected |

---

## Estimated effort

| Phase | Estimate | Risk |
|---|---|---|
| 0 — prep | ½ day | none |
| 1 — small-step alongside | 2 days | low (template exists in HOL-IMP) |
| 2 — collect + bridge | 3-4 days | medium (the new structural payoff) |
| 3 — Pipeline.thy switch | 2 days | low (pipeline_invariant_sound already pp-shaped) |
| 4 — sign chain re-derivation + div-by-zero example | 1-2 days | low |
| 5 — retire big-step + prune | ½ day | low |
| 6 — KB sync | ½ day | none |
| **Total** | **~10 working days** | dominated by Phase 2 |

Matches the §E meeting estimate (1 week migration + 1-2 days re-derive). Solver side untouched throughout.

---

## Definition of done

1. **Both predicates live.** `big_step` and `small_step` both defined in `IMP2_Semantics.thy`; `small_step_big_step_eq` proved as the bridge; `big_step_determ` and `code_pred big_step` retained unchanged.
2. **Roles documented.** Header comment in `IMP2_Semantics.thy` (and a row in `docs/ROADMAP.md`) explicitly states: `big_step` = specification side / Hoare-friendly / executable demos; `small_step` = operational basis for the pipeline theorem.
3. `pipeline_sound_small_step` is the canonical top-level soundness theorem of the thesis (per-pp, small-step shape).
4. Old big-step `pipeline_sound` survives as a one-line corollary via `small_step_big_step_eq` — exit-only consumers (Hoare specs, code-extraction demos) continue to work unchanged.
5. Sign pipeline soundness chain has **no sorry regressions** vs `pre-small-step` tag.
6. Interval pipeline scaffold compiles in the new shape (sorry count documented in `PROOF_PHASES.md`).
7. `Example_NonTerminating_Safe.thy` demonstrates a safety property at an intermediate program point of a non-terminating program — the property that is **inexpressible** under big-step alone.
8. Dead bridge scaffolding (`WHILE compound paths` block in `CFG_Collecting.thy` and any per-construct big-step↔walk lemmas) pruned; `big_step` appears only in its definition, meta-theorems, the bridge, exit-only corollaries, and `code_pred` demos.
9. KB pages `semantics-style-tradeoffs`, `collecting-semantics`, `soundness`, `decisions` all reflect the "both, with roles" landed state.
10. `make` green; `docs/ROADMAP.md` and `docs/PROOF_PHASES.md` updated.
