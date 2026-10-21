# Round 3: returning reviewers (summaries)

A second session wrote its own blind round 3 into this directory. Its editor
replaced the returning reviewers' full reports for A, B, C and E, which had
not been committed. Only their summaries survive, recorded here. `reviewer-D.md`
and `reviewer-G.md` in this directory are the returning reviewer D and the new
reviewer G of that run. `meta-review.md` and `revision-plan.md` belong to the
blind run.

## A (Isabelle), minor revision, confidence 4

- Resolved: the Return obligation (now matches `Activation_Trace_Abstract.thy:58–63`) and the trace hook.
- Partly resolved: availability.
- Every new formal statement is faithful: Return, the carries rules, `routed_entry_context_rel`, Theorem 2 against `activation_collect_dg_sound` (`Routed_Context.thy:585`), `live_unknowns`, and the Theorem 1 proof idea.
- New issues:
  - Table 1 omits `cmb_wf`, `extra_wf`, `sg_cov`, `sg_uncov` and `is_bot_bot`, and its caption omits `init_env_le`.
  - `congruence_mod_sound` is a lemma, not the locale assumption (`mod_sound`, `Abstract_Arithmetic.thy:120`).
  - The proof idea cites `caller_chain_closure` where the instance `caller_chain_covered` is meant, and omits `activation_context_rel_caller_entryI`.
  - *e* means both a call edge and an entry state.
  - "Two combine operations" is followed by one.
  - The removed vendored assumption is not named.
  - The trace hook also fires in routing and report construction.
  - The shipped entry-state policy admits at most one context per call.

## B (static analysis), minor revision (close to major), confidence 4

- Literature correct: Knoop–Steffen, Reps et al., Jeannet–Serwe and Van Horn–Might.
- Literature wrong: Might–Manolios is mischaracterized. Their state abstraction is fixed in advance too. The difference is a per-run choice function against a relation read off the solution; their non-empty candidate sets correspond to Total.
- Under-credited: Knoop–Steffen's stacks for recursive locals. §3 contradicts §8 on Sharir–Pnueli's functional approach. Seidl–Fecht is still uncited.
- Table 3 reproduces. Callee contexts per policy: 1 per procedure, 4 (k=1), 6 (k=2), 6 (entry).
- All 21 timeouts are entry-state runs (7 fixtures × Interval, Int, Congruence). The timing study never runs k=2.
- Cutting the Goblint table removed the external baseline. "Five of eight" is handwritten and picks the best setting after seeing the results.
- §3 (a frame stack cannot provide per-context stores) contradicts §6 (a frame stack with ghost contexts is the obvious alternative).
- `context_sound` is a definition; the theorem is `run_voblint_contexts`.
- "369 fixtures that set no timeout" is wrong: 380 were selected and 11 are ill-formed.

## C (semantics), minor revision, confidence 4

- Return obligation resolved: the round-2 counterexample is now rejected by the displayed contract.
- "Arbitrary CFG" is justified for the contract. The abstract's "every post-solution" overstates Theorem 2.
- Table 1 is incomplete (`cmb_wf`, `extra_wf`, `is_bot_bot`). The `pp` row omits the side-effect bound and the query membership.
- The entry-state formula drops the call description.
- *V* names two sets.
- `c₀`, `path_of`, `extend` and `entry_g` are undefined.
- The VIMP list omits that `main` has no explicit `return`, and stuck calls.
- The shipped enter returns a single alternative (`DG_Analysis.thy:601`).

## E (artifact), badges: Available no, Functional CLI only, Reusable no

- All 148 claims, Figure 1, Table 3 and every number reproduce. `paper-generated` leaves an empty diff.
- All three rebuttals in `response.md` hold.
- The data statement is inaccurate: the branch is not pushed, and the archive also lacks the flavors data, the profiling script and the paper tooling.
- `paper/tools/scale.py` bypasses the guard in `pages_stats.py`, and `pixi run paper` does not run it.
- `response.md` swaps the numbers of Table 2 and Table 3. The congruence attribution is wrong.
