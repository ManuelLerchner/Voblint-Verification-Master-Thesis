# Next steps

Short-term work plan (updated 2026-06). Issues: `gh issue list --state open`.
Catalogue: `docs/OPEN_PROBLEMS.md`. Architecture: `docs/ROADMAP.md`.

---

## Where we are

**Done**

- Full soundness chain: collecting semantics → post-fixpoint → TD → pipeline.
- Sign + interval end-to-end: `goblint_sign_sound`, `goblint_interval_sound`.
- **0 sorries** in `src/`; batch build without `quick_and_dirty` in `ROOT`.
- **P2 closed** (Fix B, 2026-06-01): `td_cfg_in_reach` removed; per-pp `td_analyse`; `td_analyse_collect_sound_at` proved via path induction.

**Still on main theorems**

One TD side condition remains (P1), documented in `docs/OPEN_PROBLEMS.md`:

| ID | Assumption | Issue | Status |
| --- | --- | --- | --- |
| P2 | `td_cfg_in_reach` | [#8](https://github.com/ManuelLerchner/goblint-formalization/issues/8) | ✅ closed |
| P1 | `TD_plain.solve_dom` | [#14](https://github.com/ManuelLerchner/goblint-formalization/issues/14) | open |

---

## Now — start here

**Primary: [#17 — Thesis writing](https://github.com/ManuelLerchner/goblint-formalization/issues/17)**

The soundness chain is complete. Only `solve_dom` (P1) remains as an explicit hypothesis — a defensible thesis stance. Write up.

**Alternative: [#14 — P1 `solve_dom` total correctness](https://github.com/ManuelLerchner/goblint-formalization/issues/14)**

Prove termination of the per-pp TD solver (finite `pp`, well-founded recursion). Closes the last TD hypothesis.

**Fallback**

- Executability polish ([#16](https://github.com/ManuelLerchner/goblint-formalization/issues/16)).
- Session split ([#13](https://github.com/ManuelLerchner/goblint-formalization/issues/13)).

---

## Next goals (short horizon)

| Priority | Goal | Issue | Payoff |
| --- | --- | --- | --- |
| 1 | **Thesis writing** | **#17** | All core lemmas proved; write-up is the blocker |
| 2 | P1 `solve_dom` | **#14** | Last TD hypothesis; closes the chain fully |
| 3 | Executability | **#16** | Per-pp `value` works; full `run_analysis` map still open |
| 4 | Session split | **#13** | Core vs Stretch — needs `TD_Soundness` / `Pipeline` import refactor |

**Defer unless scope expands**

- **#14** (total correctness, P5 finite `pp`) — large; partial correctness + explicit P1 is a defensible thesis stance (`docs/ROADMAP.md`).
- Octagon track (**#25**, **#15**, **#19**) — only if supervisors choose Scope B.

---

## Suggested week

```text
Day 1–2:  Thesis prose (sign + interval soundness chapters) from docs/walkthrough
Parallel:  #14 (solve_dom total correctness) — closes last TD hypothesis
Later:     #16 (demos) OR #13 (session split) — one of, not both
Stretch:   #11 (backward transformers) only if interval precision is thesis-critical
```

---

## Thesis milestone (next “done” slice)

> Sign + interval soundness with **only `solve_dom`** as explicit TD hypothesis, plus one thesis chapter per domain.

#7, #8 done. Remaining: **#14 → write-up**. Treat **#14** as optional stretch if `solve_dom` is explicitly stated in the thesis.

---

## References

- `docs/OPEN_PROBLEMS.md` — P1–P10, bridge diagram
- `docs/PROOF_PHASES.md` — sorry inventory, completed milestones
- [GitHub Project 8](https://github.com/users/ManuelLerchner/projects/8) — board view
