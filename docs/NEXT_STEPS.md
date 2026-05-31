# Next steps

Short-term work plan (updated 2026-05). Issues: `gh issue list --state open`.
Catalogue: `docs/OPEN_PROBLEMS.md`. Architecture: `docs/ROADMAP.md`.

---

## Where we are

**Done**

- Full soundness chain: collecting semantics → post-fixpoint → TD → pipeline.
- Sign + interval end-to-end: `goblint_sign_sound`, `goblint_interval_sound`.
- **0 sorries** in `src/`; batch build without `quick_and_dirty` in `ROOT`.

**Still on main theorems**

Two TD side conditions (P1–P2), documented in `docs/OPEN_PROBLEMS.md`:

| ID | Assumption | Issue |
| --- | --- | --- |
| P2 | `td_cfg_in_reach` | [#8](https://github.com/ManuelLerchner/goblint-formalization/issues/8) |
| P1 | `TD_plain.solve_dom` | [#14](https://github.com/ManuelLerchner/goblint-formalization/issues/14) (total correctness / finite `pp`) |

---

## Tomorrow — start here

**Primary: [#8 — Discharge P2 (`td_cfg_in_reach`)](https://github.com/ManuelLerchner/goblint-formalization/issues/8)**  
Fix the structural inconsistency in the TD reach hypothesis (see P2 finding in `docs/OPEN_PROBLEMS.md`).
Recommended approach: Fix B (per-pp solve), making `reach.base` trivially discharge the hypothesis.

Why first:

- P3 (`comp_fun_idem`) is closed via `join_state_comp_fun_idem` ([#7](https://github.com/ManuelLerchner/goblint-formalization/issues/7) done).
- P2 is the next open hypothesis; fixing it removes the vacuous soundness issue.
- Fix B is a focused refactor of `td_analyse` and the pipeline statement shape.

**First hour**

1. I/Q: `open_file` `src/Solver/TD_Interface.thy` — `td_analyse`, `td_analyse_post_fixpoint`.
2. Review P2 finding in `docs/OPEN_PROBLEMS.md` — Fix B recommendation.
3. Redefine `td_analyse` as per-pp solve; update pipeline theorems to per-pp `solve_dom`.
4. Verify `reach.base` discharges `td_cfg_in_reach` trivially.

**Fallback (no proof progress)**

- Thesis prose from `docs/walkthrough/` (interval instance mirrors sign).
- Or executability polish ([#16](https://github.com/ManuelLerchner/goblint-formalization/issues/16)).

---

## Next goals (short horizon)

| Priority | Goal | Issue | Payoff |
| --- | --- | --- | --- |
| 1 | Drop **P2** | **#8** | Second assumption gone; CFG reachability + TD `reach` |
| 2 | **Thesis writing** | **#17** | Bridges documented in walkthrough; PDF still open |
| 3 | Executability | **#16** | Per-pp `value` works; full `run_analysis` map still open |
| 4 | Session split | **#13** | Core vs Stretch — needs `TD_Soundness` / `Pipeline` import refactor |

**Defer unless scope expands**

- **#14** (total correctness, P5 finite `pp`) — large; partial correctness + explicit P1 is a defensible thesis stance (`docs/ROADMAP.md`).
- Octagon track (**#25**, **#15**, **#19**) — only if supervisors choose Scope B.

---

## Suggested week

```text
Day 1–2:  #7 (P3), then #8 (P2) if P3 closes cleanly
Parallel:  thesis prose (sign + interval) from docs/walkthrough
Later:     #16 (demos) OR #13 (session split) — one of, not both
Stretch:   #11 (backward transformers) only if interval precision is thesis-critical
```

---

## Thesis milestone (next “done” slice)

> Sign + interval soundness with **at most one** explicit TD hypothesis (ideally only `solve_dom`), plus one thesis chapter per domain.

Sequence: **#7 → #8 → write-up**. Treat **#14** as optional stretch.

---

## References

- `docs/OPEN_PROBLEMS.md` — P1–P10, bridge diagram
- `docs/PROOF_PHASES.md` — sorry inventory, completed milestones
- [GitHub Project 8](https://github.com/users/ManuelLerchner/projects/8) — board view
