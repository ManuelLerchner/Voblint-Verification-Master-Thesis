# Thesis scope — decision memo

One page for the supervisor sign-off that gates the next phase. Status as of the
M4-precision landing (branch `feat/m4-digest-precision`).

---

## Refresh (2026-08-04) — read this section first

The section below this line is the **original memo, dated 2026-06-10**. Its
recommendation was "Scope A, write now." That recommendation was never acted
on, and the repository kept moving for two more months. This refresh
deliberately separates three things that should not blur together: **facts**
(verified against the repository), **interpretation** (one reading of what
the facts might mean — a judgment call, not a finding), and
**recommendation**.

### Facts (verified against the repository)

Since the original memo, the repository underwent several architectural
changes. Some of the artifacts cited as evidence in June were removed during
later simplifications; several new framework results were added.

**Removed:**

1. `digest_beats_flat`, `flat_env_is_digest_sound`, `reaching_global_read_sound`,
   and the entire trace/digest read spine (16 theories) were removed
   2026-07-18 after an audit found the retained soundness path never actually
   used them (full record: `docs/history/DIGEST_SPINE_REMOVAL_PLAN.md`). The original
   memo cites this precision result in the "History-sensitive globals (M4)"
   bullet and the "Recommendation" section below.
2. `src/VIMP/IMP2_Bridge.thy` (456 lines) and `IMP2_VCG_Example.thy` — the
   backward-simulation bridge to AFP IMP2's big-step semantics and the
   VCG-interop demo the original memo cites as delivered evidence — were
   removed in commit `42b750d8` ("cleanups", 2026-07-20) with no explanatory
   message and no decision doc. At least four other docs
   (`docs/history/ARRAY_SYNTAX_EXTENSION.md`, `docs/history/SESSION_DAG_MIGRATION.md`,
   `docs/history/GHOST_INSTRUMENTATION_MIGRATION.md`,
   `docs/history/VIMP_PRETTY_NOTATION_MIGRATION.md`) still cite these files as if they
   exist — worth a deliberate decision (restore, or correct the citing docs)
   rather than leaving as silent drift.
3. Likely a third, **unconfirmed**: `Retain_Analysis.thy` (`retain_dg_spec`,
   `gamma_retain`, `sound_dg_spec_retain` — cited in AD-41 as evidence for the
   opaque-carrier generalization) has zero hits anywhere in `src/` today. Not
   traced to a specific commit in this pass — verify before citing either way.

**Added** (per the KB ledger, `research/architecture-decisions.md` AD-41
through AD-48 — summarized here, not independently re-derived from the
theories in this pass, so treat as a pointer to verify, not a citable claim
on its own):

- **AD-43/45 (2026-07-13…19).** Activation-local trace semantics `valid_ltr`
  (proved `= lfp(ltr_F)`, `LTR_Def.thy`); `ltr_collect`/
  `ltr_collect_keyed` are now the canonical compiled-program soundness
  target, not `cfg_collect` directly. Reflected in the current
  `docs/PROOF_OVERVIEW.md`/`docs/PROOF_PHASES.md` — those two read as
  up to date with this axis.
- **AD-41/42 (2026-07-13/14).** Native D/G spec over opaque `D`/`G` carriers
  as the context-sensitive spine; `Exec_DG_Bridge.thy`/`Exec_Sign_DG_Run.thy`
  run the verified solver directly on a D/G carrier and certify the result
  `by eval`.
- **AD-46/47 (2026-07-21, 2026-08-01).** `routed_context`/`dg_ctx_activation`
  give call-string context sensitivity generically;
  `Example_Sign_DG_CallString_K1/K2.thy` prove a strict-order precision
  result (`sign_k2_strictly_more_precise_than_k1_at_g`) through the real,
  executable plain-join solver.
- **AD-48 (2026-08-04, today).** `sound_dg_spec` proved a sublocale of a more
  general `sound_dg_hooks`; a migration that would have moved every example
  onto the general layer was investigated and cancelled; owner-sensitive
  **placement** analyses (`Example_Sign_Placement.thy`,
  `Example_Interval_Placement.thy`) are a new capability class the original
  `dg_spec` record could not express. Full record:
  `docs/reviews/M4_SPINE_BOUNDARY_AUDIT.md`,
  `docs/reviews/M4_MIGRATION_CHECKLIST.md`.
- **P1 renamed, not resolved.** The original memo's ask #3 names `solve_dom`;
  the current IP/side-effecting spine's analogous hypothesis is
  `side_cfg_solve_dom_eff` totality. Same open question, different name.

### Interpretation (a reading, not a decision)

Whether the added results **replace** the earlier contribution — in the
sense of becoming the thesis's central claim — is a judgment call for the
supervisors and the author, not something this document settles. One
possible framing, offered as a starting point for that conversation, not a
conclusion:

> *A formally verified, extensible interprocedural abstract interpretation
> framework with activation-local traces, context-sensitive routing, and a
> unified D/G semantics supporting customizable storage placement.*

The pipeline the current repository demonstrates, stated as architecture
rather than as a claim about "the contribution":

```text
VIMP source -> CFG -> activation-local trace semantics (valid_ltr = lfp)
  -> ltr_collect / ltr_collect_keyed canonical soundness target
  -> native D/G spec (opaque carriers, sound_dg_hooks framework layer beneath it)
  -> context-sensitivity (routed_context) + owner-sensitive placement
  -> solver-certified executable runs (Exec_DG_Bridge, by eval)
  -> precision witness: Sign CallString k=1 vs k=2 strict order
```

This is a different narrative than the one the original memo's Scope A table
describes. Whether it is a stronger, weaker, or merely different thesis than
the June framing is exactly the open question — not pre-judged here.

### Recommendation (refresh)

**"Scope A, write now" may still be the right call — it cannot be
re-affirmed on the original evidence**, since two of the three items the
original memo cites as delivered no longer exist as stated. Concrete next
step, not yet done: verify the "Added" list above claim-by-claim against the
theories (not the KB summary), then take a refreshed decision — facts, one
or more candidate interpretations, and the original three asks plus a
fourth (does AD-41–48 belong in the thesis's central contribution, or is it
supporting infrastructure) — back to the supervisor.

---

## Original memo (2026-06-10) — historical, superseded evidence flagged above

### Where the machine-checked work stands

The soundness chain is closed end-to-end, `0 sorries`, full `isabelle build` green:

- **Pipeline soundness** at every program point (`pipeline_invariant_sound`,
  `pipeline_sound_path`) and at exit (`goblint_sign_sound`, `goblint_interval_sound`),
  modulo one explicit TD hypothesis (P1 `solve_dom`).
- **Trace foundation** (Seidl pivot): `cfg_collect = α_last(cfg_collect_trace)`
  lifts every numeric-domain proof through the projection unchanged.
- **History-sensitive globals (M4):**
  - *Soundness core* — any variable's value over any reaching interprocedural
    trace lies in `γ(env v x)` (`reaching_global_read_sound`).
  - *Precision* — the digest layer: refining the trace set by a digest only
    shrinks it (`cfg_collect_trace_ip_d_subset`), the existing analyzer is a
    sound digest-indexed env (`flat_env_is_digest_sound`), and a digest-indexed
    env can be **strictly tighter** than any sound flat env on a concrete program
    (`digest_beats_flat`, sign domain).
    **[Refresh 2026-08-04: this entire digest layer was deleted 2026-07-18. See
    "Refresh" section above.]**
- **AFP IMP2 semantic anchor**
  **[Refresh 2026-08-24: not in the tree. `src/VIMP/IMP2_Bridge.thy`, `to_imp2`
  and `backward_sim` do not exist, and the migration plan this entry cited is
  gone; `docs/history/AFP_IMP2_REUSE_DECISION.md` records the decision.
  Soundness is stated against VIMP's own semantics only.]**
  The intent was: soundness expressible against AFP IMP2's standard big-step
  semantics, not only our bespoke small-step, via a one-way bridge and a
  backward simulation transferring soundness to the recognised reference
  semantics. A worked example
  (`src/VIMP/IMP2_VCG_Example.thy`) verifies a scalar loop's translation with
  IMP2's own VCG (`vcg_cs`) and pulls the result back via `backward_sim`,
  demonstrating that the verified abstract interpreter and a deductive verifier
  interoperate on one semantics. Significance and the trace-vs-big-step
  comparison: KB thesis outline `research/thesis-structure` §5.4–5.6.
  **[Refresh 2026-08-04: `IMP2_Bridge.thy`/`IMP2_VCG_Example.thy` were deleted
  2026-07-20, commit `42b750d8`. See "Refresh" section above.]**

The research question — *can a verified pipeline soundly and precisely analyze
history-sensitive globals?* — is answered in the machine-checked artifact.

### The decision

The thesis is defensible at two scope levels. Pick one before the octagon
two-layer refactor lands, because that refactor is only worth its cost if a
relational domain actually follows it.

| | **Scope A — finished pipeline + history-sensitive globals** | **Scope B — Scope A + octagon** |
| --- | --- | --- |
| Content | Verified IMP→CFG→eqsys→TD pipeline; sign + interval; trace pivot; M4 soundness **and** precision | Scope A **plus** a relational octagon domain with reduced product |
| Status | **Essentially done** — proof side is polish + writing | ~4–6 weeks of new work, ~2 of it plumbing before any octagon theory |
| Risk | Low; calendar-bound by writing | High; no Isabelle octagon prior art, DBM closure proofs from scratch |
| Payoff | Clean, complete, defensible | First AFP octagon entry; relational precision story |

### One open question that affects what "done" means

**Must the Galois `α` be formalized, or does `γ`-only suffice?** The domains use
semantic `γ`-axioms (`sound_domain`); no best-abstraction `α` is mechanized.
Soundness needs only `γ`. The M4 precision witness sidesteps `α` entirely — its
strictness is *forced by soundness alone* (in the sign domain only `STop`
concretizes both a positive and a negative). If the thesis claims *optimality*
(not just "strictly tighter"), `α` and a best-abstraction argument become
load-bearing. Recommend: stay `γ`-only, claim *strict improvement*, not
optimality. Cheaper and still a real precision result.

### Recommendation

**Scope A, write now.** The proof core is complete; M4 precision is the
centerpiece result and it is landed. Treat octagon as acknowledged future work
with the difficulty notes in `docs/ROADMAP.md`. Reopen Scope B only if the
supervisors want the relational-domain contribution and accept the calendar risk.
**[Refresh 2026-08-04: this recommendation was never revisited after the
digest/IMP2-bridge deletions above. Do not act on it as-is — see "Refresh"
section for the concrete next step.]**

Concrete asks for sign-off:

1. Scope A or B?
2. `γ`-only soundness + strict-precision (recommended), or formalize `α` for an
   optimality claim?
3. Keep P1 `solve_dom` as an explicit, documented TD hypothesis (recommended —
   see `docs/P1_TOTAL_CORRECTNESS_ROUTE.md`), or invest in total correctness?
