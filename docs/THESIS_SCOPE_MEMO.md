# Thesis scope — decision memo

One page for the supervisor sign-off that gates the next phase. Status as of the
M4-precision landing (branch `feat/m4-digest-precision`).

## Where the machine-checked work stands

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

The research question — *can a verified pipeline soundly and precisely analyze
history-sensitive globals?* — is answered in the machine-checked artifact.

## The decision

The thesis is defensible at two scope levels. Pick one before the octagon
two-layer refactor lands, because that refactor is only worth its cost if a
relational domain actually follows it.

| | **Scope A — finished pipeline + history-sensitive globals** | **Scope B — Scope A + octagon** |
| --- | --- | --- |
| Content | Verified IMP→CFG→eqsys→TD pipeline; sign + interval; trace pivot; M4 soundness **and** precision | Scope A **plus** a relational octagon domain with reduced product |
| Status | **Essentially done** — proof side is polish + writing | ~4–6 weeks of new work, ~2 of it plumbing before any octagon theory |
| Risk | Low; calendar-bound by writing | High; no Isabelle octagon prior art, DBM closure proofs from scratch |
| Payoff | Clean, complete, defensible | First AFP octagon entry; relational precision story |

## One open question that affects what "done" means

**Must the Galois `α` be formalized, or does `γ`-only suffice?** The domains use
semantic `γ`-axioms (`sound_domain`); no best-abstraction `α` is mechanized.
Soundness needs only `γ`. The M4 precision witness sidesteps `α` entirely — its
strictness is *forced by soundness alone* (in the sign domain only `STop`
concretizes both a positive and a negative). If the thesis claims *optimality*
(not just "strictly tighter"), `α` and a best-abstraction argument become
load-bearing. Recommend: stay `γ`-only, claim *strict improvement*, not
optimality. Cheaper and still a real precision result.

## Recommendation

**Scope A, write now.** The proof core is complete; M4 precision is the
centerpiece result and it is landed. Treat octagon as acknowledged future work
with the difficulty notes in `docs/ROADMAP.md`. Reopen Scope B only if the
supervisors want the relational-domain contribution and accept the calendar risk.

Concrete asks for sign-off:
1. Scope A or B?
2. `γ`-only soundness + strict-precision (recommended), or formalize `α` for an
   optimality claim?
3. Keep P1 `solve_dom` as an explicit, documented TD hypothesis (recommended —
   see `docs/P1_TOTAL_CORRECTNESS_ROUTE.md`), or invest in total correctness?
