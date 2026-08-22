# Generic non-relational pipeline: handoff

Status: **IN PROGRESS.** Investigation complete (three simulation agents, read-only,
findings below). Implementation not started. This handoff is for whoever picks up
next — a fresh agent or a continuation of this session.

Read this document together with:

- docs/RELATIONAL_DOMAIN_ARCHITECTURE_DECISION.md — the sibling decision this
  investigation builds directly on; do not re-derive its conclusions.
- docs/PROOF_HYGIENE_MIGRATION.md — Stage 0-7 definition-unfolding cleanup
  (commit `bd4629e0`), already committed. Unrelated to this task except as
  precedent for the working style (I/Q inner loop, batch outer gate).

## Where this came from

Three passes already landed in this repo this session, each a distinct kind of
work:

1. **Proof-hygiene migration** (commit `bd4629e0`) — replaced repeated
   `unfolding X_def` re-derivation with named characterization lemmas.
   Committed.
2. **Proof-API consolidation** (commit `def1f4a`) — deduplicated a lemma,
   added `apply_tf_wrap_eqI`, `ivl_exhaustE`, `compile_proc_calls_source_stmtE`,
   `dg_postfix_edgeD/edgeG/enterD/enterG`, extracted a shared `Exec_Backward`
   locale for Sign/Interval's executable backward-filter mirrors. Committed.
3. **Second proof-architecture pass** (8 items: completed the `dg_postfix`
   8-conjunct projection family with `entryD/G`/`combineD/G`; added
   `side_env_apply` — **left untagged, not `[simp]`**, see below;
   `callee_entry_invariant_keyD`/`_call_enterD`; `activation_collect_I`/`_E`
   (`ltr_collect_I`/`_E` already existed, only `activation_collect` needed new
   lemmas); `sound_transfer` destructors `tf_sound_*D`; `sound_dg_spec`
   fst/snd wrappers `step_sound_fs`/`enter_sound_fs`/`combine_sound_fs`).
   **Batch-green (full rebuild, exit 0), NOT YET COMMITTED.** This required 3
   rounds to reach green:
   - Round 1: an `obtains`/`blast` method mismatch in `Activation_Backbone.thy`
     (`using activation_collect_E by blast` instead of
     `by (rule activation_collect_E)`) caused a real proof-search blowup
     (30+ seconds and climbing) — killed the build, fixed the method.
   - Round 2: two more real bugs surfaced — an equality-direction mismatch in
     the same file's `obtain` clause (`st = sink_store t` vs.
     `activation_collect_E`'s `sink_store t = s`), and `side_env_apply`'s
     `[simp]` tag broke `LTR_TD_Side_Eff_Sound.thy` (untouched directly) via
     a locale abbreviation `ltr_gamma.gamma_ltr` that is itself stated in
     terms of `side_env` — eagerly expanding `side_env` elsewhere broke that
     abbreviation's term-shape matching. Fixed by flipping the equality
     direction and **untagging `side_env_apply`** (kept as a bare lemma, cited
     explicitly where used, matching the `restrict_local_sup` regression
     precedent from pass 1).
   - Round 3: full rebuild green, 0 failures, exit 0.
   **Open decision: whether/how to commit this.** User has not yet answered.
   Files touched: `Constraint_System.thy`, `Constraint_System_Sound.thy`,
   `Activation_Backbone.thy`, `DG_Ctx_Activation.thy`, `DG_Soundness.thy`,
   `TD_Side_CFG.thy`, `CFG_Local_Trace.thy`, `LTR_Abstract.thy`,
   `Located_LTR.thy`.

## This task: framework design, not cleanup

User's explicit framing: stop optimizing for more helper lemmas; investigate
whether Transfer/Exec/Exec_Sound/DG-integration duplication between Sign and
Interval can collapse into one generic locale, so a future domain supplies
only a lattice + transfer function + soundness proofs. **Think before
changing code.** Three parallel read-only simulation agents were launched
(Constant Propagation, Octagon, Polyhedra) to stress-test the framework from
three different complexity angles. All three completed; findings below.

## Settled decision: two architectural paths, not one

**Relational domains (Octagon, Polyhedra) need no new framework work.**
`gamma_state`'s pointwise `∀x` quantification (`Abstract_Domain.thy:58-59`,
`gamma_state σ = {s. ∀x. s x ∈ gamma (σ x)}`) makes cross-variable facts
provably inexpressible in the `abs_state`/`domain_transfer`/`sound_domain`
spine — a type-signature fact, confirmed independently by both the Octagon
and Polyhedra simulation agents, not a judgment call. The only viable path
for a relational domain is interpreting `sound_dg_spec` directly
(`DG_Soundness.thy:135-156`), bypassing Transfer/Exec/Exec_Sound entirely —
exactly what the existing `src/Analysis/Instances/Mixed/Rel_Order_Domain.thy`
already does, validated batch-green with a one-line diff outside the new
file, and already documented in
`docs/RELATIONAL_DOMAIN_ARCHITECTURE_DECISION.md`. **Do not build anything
for the relational side in this task** — it is already built. One real but
speculative opportunity surfaced independently by both the Octagon and
Polyhedra agents: a `havoc_conservative_dg_spec` locale to stop the
"havoc/forget is trivially sound" pattern being hand-derived fresh per
relational domain. **Not implementing this now** — there is currently only
one relational domain instance (`Rel_Order_Domain.thy`) in the repo, so this
would be abstracting from a sample size of one. Revisit once a second
relational domain actually exists.

**Non-relational domains (Sign, Interval, and any future Constant-Propagation-
shaped domain) have four concrete, high-confidence generalization
opportunities**, each validated against the **two already-existing**
instantiations (Sign and Interval), not a hypothetical future one. This is
the actual scope of this task.

## The four opportunities (treat as ONE coherent refactor, not four)

Organizing goal (user's framing): after this refactor, adding a new
non-relational domain should require only: lattice, concretization (`gamma`),
transfer function, top/reset policy, one soundness proof set — everything
else comes from interpretations and generic infrastructure. That is the
architectural invariant to hold the four sketches to.

### (A) Generic top-reset enter-frame

Home: `src/Analysis/Generic/Equations/Constraint_System.thy`, alongside
`bind_formals_abs`.

Both `Sign_Transfer.thy`'s `enter_frame_sign`/`enter_sign` (+ soundness/mono
proofs, ~65 lines) and `Interval_Transfer.thy`'s `enter_frame_ivl`/`enter_ivl`
(same shape) are the *same* "reset locals to a fixed top-like value, keep
globals, bind formals" pattern, parameterized only by which top-like value.
Sketch (from the Constant-Propagation simulation agent's report — verify
signatures against the live `Constraint_System.thy` before use, do not
copy-paste blindly):

```isabelle
definition enter_frame_D :: "'a => 'a abs_state => 'a abs_state" where
  "enter_frame_D top_val sigma = (%x. if is_global x then sigma x else top_val)"

lemma enter_frame_D_sound:
  fixes top_val :: "'a::sound_domain"
  assumes gs: "s : [[sigma]]" and top_full: "gamma top_val = UNIV"
  shows "enter_state s : [[enter_frame_D top_val sigma]]"
  unfolding gamma_state_def enter_frame_D_def enter_state_def
  using gamma_stateD[OF gs] top_full by auto

lemma enter_frame_D_mono:
  "s1 <= s2 ==>
     enter_frame_D top_val s1 <= (enter_frame_D top_val s2 :: 'a::order abs_state)"
  by (rule le_funI) (auto simp: enter_frame_D_def le_funD)

definition enter_D ::
  "'a => (aexp => 'a abs_state => 'a) => vname list => aexp list
   => 'a abs_state => 'a abs_state" where
  "enter_D top_val aval_abs xs es sigma =
     bind_formals_abs xs (map (%e. aval_abs e sigma) es)
       (enter_frame_D top_val sigma)"
```

Sign would instantiate `enter_frame_sign = enter_frame_D STop`, discharging
soundness/mono by citing `enter_frame_D_sound`/`_mono` plus the one-line fact
`gamma_sign STop = UNIV` (already an equation of `gamma_sign` — check this is
still true against the live file before relying on it). Same for Interval
with `ivl_top`. Expected: ~65 lines -> ~15-20 lines per domain.

**Risk flagged by the simulation agent**: this assumes every domain resets
locals to a single fixed value that is provably `gamma`-total (`= UNIV`).
Holds for Sign and Interval today. Would NOT hold for a domain whose "enter"
isn't a simple top-reset — out of scope here (that's the relational-domain
side, already excluded above), but worth a comment in the generic
definition's docstring so a future domain author knows the assumption
exists.

### (B) Same idea at the executable `st` layer

Home: `src/Analysis/Generic/Domain/Exec_St.thy`, mirroring how
`Exec_Backward.thy` (a prior pass's successful generalization) already
handles backward filters generically.

`Sign_Exec.thy`'s `fun_rep_enter_sign_rep`/`enter_sign_st`/
`enter_frame_sign_st_commute` (~18 lines) and `Ivl_Exec.thy`'s equivalent are
the executable-state twin of (A). Sketch (same caveat: verify against live
`Exec_St.thy` before using):

```isabelle
lift_definition enter_frame_st_D :: "'a => 'a st => 'a st"
  is "%top_val (dl, dg, ps). (top_val, dg, filter (%(x,_). is_global x) ps)"
  by (auto simp: eq_st_def fun_eq_iff split: option.split)

lemma enter_frame_st_D_commute:
  "fun_of_st (enter_frame_st_D top_val s) = enter_frame_D top_val (fun_of_st s)"
  unfolding enter_frame_D_def by transfer (auto simp: map_of_filter_key split: option.split)
```

Expected: ~18 lines -> ~1-2 lines per domain (one instantiation citation).

### (C) `sound_transfer` discharge combinator — the strongest of the four

Home: `src/Analysis/Generic/Equations/Constraint_System.thy`, next to the
`sound_transfer` locale (already has the `tf_sound_*D` destructors from pass
3 — build on those, don't duplicate them).

**Why this is the highest-value item**: `Sign_Transfer.thy` currently
contains `combine_sign`/`combine_sign_sound` (~16 lines) that are **already
dead weight today** — `tf_combine tf = combine_abs` and the generic
`combine_states_sound` (`Constraint_System.thy:325` roughly, verify current
line) already prove exactly this fact. This isn't just duplication, it's a
symptom that the framework wasn't exposing the right introduction rule for
"my domain uses the standard combine." Sketch:

```isabelle
lemma sound_transferI:
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes "!!x a sigma s. s : [[sigma]] ==>
             s(x := aval a s) : [[tf_assign tf x a sigma]]"
      and "!!b sigma s. s : [[sigma]] ==> bval b s ==>
             s : [[tf_assume tf b sigma]]"
      and "!!b sigma s. s : [[sigma]] ==> ~ bval b s ==>
             s : [[tf_assume_not tf b sigma]]"
      and "!!xs es sigma s. s : [[sigma]] ==>
             bind_formals xs (map (%e. aval e s) es) (enter_state s)
               : [[tf_enter tf xs es sigma]]"
      and "tf_combine tf = combine_abs"
  shows "sound_transfer tf"
  by unfold_locales (auto simp: assms combine_states_sound)
```

This makes "is `tf_combine` really always `combine_abs`" a **required,
checked premise** instead of a silently-repeated proof that never uses
anything domain-specific. Expected: ~20 lines -> ~5 lines (one citation),
plus **deletes** `Sign_Transfer.thy`'s 16 dead-weight lines outright.

**Risk flagged by the simulation agent**: a domain whose `combine` genuinely
isn't `combine_abs` would need this to become an OR-branch. The framework
already anticipated this — `Constraint_System.thy` has
`sound_effectful_transfer_framed`/`_framed_le` locales that generalize the
enter-bound to an arbitrary `fresh_frame` rather than assuming reset-to-top;
worth reading these before finalizing sketch (A)/(C)'s exact shape, since
they may already be the "right" generalization point rather than a new one.
**Verify this file section still exists and re-read it before implementing**
— it was cited by the simulation agent from a full read, not independently
re-confirmed in this handoff.

### (D) `interpretation ... defines ...` for the DG wrapper files

Home: `Sign_DG.thy`, `Interval_DG.thy`, `Mixed_Sign_Interval.thy` — no new
generic code needed, this is purely exploiting an existing Isabelle
mechanism the wrapper files aren't using yet.

All three files follow the same shape: `interpretation ... sound_dg_spec ...`
then manually restate the interpretation's own facts under plain names via
separate `definition`/`theorem` blocks (~50-55 lines each). Isabelle's
`interpretation ... defines X = Y.foo and Z = Y.bar ...` clause introduces
the plain-named definitions AND rewrites the locale's theorems to use them,
in the interpretation line itself — eliminating the manual wrapper
entirely. Already flagged in a prior audit (this session, second pass) as a
"low risk, low blast radius" item; confirmed again independently by the
Constant-Propagation simulation. Expected: ~50-55 lines -> ~10-15 lines per
file, 3 files.

## Explicitly NOT in scope for this pass

- **`Sign_Local_Effects.thy`'s 504-line `local_edge_invariant` proofs.** The
  simulation agent's own report flags this as "unverified" — the hypothesis
  is that a generic `backward_domain`-level `local_edge_invariant` theorem,
  parameterized only by two `aval_abs` restriction facts, could collapse
  this to ~50-100 lines per domain (biggest potential win of anything found
  this session), but the agent explicitly did not attempt to write and
  discharge that theorem, and flagged a specific risk: the `Eq`/`Less` cases
  may secretly require `meet`/`inv_less` to commute with `restrict_local` in
  a way not already given by `backward_domain`'s existing assumptions. If
  that holds, the realistic collapse is smaller (~150-200 lines/domain, still
  a win, just not the headline one). **This needs its own dedicated prototype
  attempt in isolation** — do not bundle into the (A)-(D) refactor. If it's
  picked up later, treat it as its own investigation with room to fail and
  fall back, not a "safe extension" of this pass.
- **The relational `havoc_conservative_dg_spec` locale.** Speculative,
  sample-size-of-one, deferred per the "settled decision" section above.
- **Any `[simp]` tag additions.** User's explicit instruction: keep
  automation conservative, do not expand the global simp set without strong
  justification. None of (A)-(D) require one — they are structural/
  definitional generalizations, not new rewrite rules. If implementation
  reveals a genuine need for one, apply the full LHS-overlap-with-existing-
  lemmas-AND-local-derived-facts check documented in this repo's `AGENTS.md`
  "Automation that batch tolerates" section before tagging — this session
  already hit two real regressions from skipping that check (the original
  `restrict_local_sup` incident, and `side_env_apply` in pass 3 above).

## Deliverables still owed (per user's latest message)

1. **This handoff document** — done, this file.
2. **Architecture decision record**, matching
   `docs/RELATIONAL_DOMAIN_ARCHITECTURE_DECISION.md`'s structure. User's
   requested outline, verbatim:
   1. Problem
   2. Existing duplication
   3. Why the abstraction is sound
   4. Alternatives considered
   5. Chosen design
   6. Migration strategy
   7. Expected LOC reduction
   8. Why this doesn't help relational domains (this is the section tying
      the two architectural paths together — write it carefully, it's the
      part that explains the whole two-path split to a future reader who
      hasn't seen this session's simulation agents' work)
   Proposed filename: `docs/GENERIC_NONRELATIONAL_PIPELINE_ARCHITECTURE_DECISION.md`
   (user suggested this name or similar — confirm before finalizing if
   picking this up fresh).
3. **Measurement table**, per domain (Sign, Interval), before and after
   implementing (A)-(D):

   | Metric | Before | After |
   | --- | --- | --- |
   | Lines in Sign (Transfer + Exec + DG files touched) | | |
   | Lines in Interval (same) | | |
   | Number of duplicated lemmas (same shape/proof across both domains) | | |
   | Number of manual interpretations | | |
   | Number of wrapper theorems | | |
   | Proof obligations per new domain (count, not lines) | | |

   The last row is the one the user flagged as most important — it's the
   direct measure of "how much does a 4th domain have to prove," which is
   the actual goal of this whole task.
4. **"Checklist for Adding a New Non-Relational Domain"** — the stable
   extension-point document, written LAST, after (A)-(D) land and are
   batch-verified. Should read as a short, concrete numbered list (user's
   sketch: define lattice / instantiate transfer / prove transfer soundness
   / interpret generic pipeline / done). If the checklist is still long or
   contains duplicated proof steps once (A)-(D) are in, that's a signal the
   architecture isn't actually finished — say so honestly rather than
   declaring victory.
5. **Risk analysis** — fold into the architecture decision doc's own
   structure (per the 8-section outline above) rather than a separate
   document.

## Implementation order (once resumed)

1. Re-read the live `Constraint_System.thy`, `Exec_St.thy`,
   `Sign_Transfer.thy`, `Interval_Transfer.thy`, `Sign_Exec.thy`,
   `Ivl_Exec.thy`, `Sign_DG.thy`, `Interval_DG.thy`, `Mixed_Sign_Interval.thy`
   via `mcp__isabelle-pide-mcp__read` (NOT host Read — these are tracked
   `.thy` files, see this repo's own `CLAUDE.md`/`AGENTS.md` theory-file
   boundary rule) to confirm every line/name cited above still matches
   current state before writing a single edit. Sketches above are drafted
   from simulation-agent reports, not independently re-verified against the
   live files in this handoff.
2. Implement (A), verify against Sign AND Interval both (both must batch-
   build green before moving on — do not implement against one domain and
   assume the other follows).
3. Implement (B), same dual-verification.
4. Implement (C), same dual-verification, and confirm the dead-weight
   `combine_sign`/`combine_sign_sound` deletion is safe (grep for any other
   citation of these two lemma names across the repo before deleting).
5. Implement (D) across all three DG wrapper files.
6. One full clean batch build (`Voblint_CFG` -> `Voblint_Analysis` ->
   `Voblint_Formalization` -> `Voblint_Examples`), not a cached one — this
   session has repeatedly found real regressions that a cached/partial build
   missed. Expect at least one round of real fixes; do not declare done on
   the first attempt without genuine full-rebuild confirmation.
7. Fill in the measurement table with real before/after line counts (use
   `wc -l` / `git diff --stat` on the actual touched files, not estimates).
8. Write the architecture decision doc.
9. Write the "Checklist for Adding a New Non-Relational Domain" doc.
10. Report back: what changed, the filled-in measurement table, and ask
    about committing — separately from the still-open pass-3 commit
    decision noted above. Do not conflate the two commits.

## Known session hazards to keep in mind

- I/Q (`mcp__isabelle-pide-mcp__*`) has repeatedly shown either genuinely
  clean states or stale/vacuous ones this session (`commands_finished: 0`
  while reporting `errors: 0`, or a `get_state` command-detail dump that
  doesn't match the actual current file content per a fresh `read`). Treat
  `read` as ground truth for content; treat a full batch build as ground
  truth for correctness. Do not declare a fix confirmed on I/Q alone.
- A concurrent human/agent may be editing files in this repo — check
  `git status`/`git diff` for unexpected changes before assuming you're the
  only editor, and do not commit or force-overwrite anything you didn't
  author without checking provenance first.
- Watch batch build logs for `command ... running for Ns` lines past
  ~30-40s — per this project's own guidance (`docs/ISABELLE_AGENT_NOTES.md`),
  that's a real proof-search blowup signal, not just a slow but fine
  computation. Distinguish this from legitimately slow-but-successful
  Example theories (`Example_Interval_DG_Ctx_Flagship.thy` genuinely takes
  ~200s+ some runs) by checking whether the theory eventually reports
  `100%` — if it does, it was slow, not stuck.
