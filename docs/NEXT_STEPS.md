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

Three TD side conditions (P1–P3), documented in `docs/OPEN_PROBLEMS.md`:

| ID | Assumption | Issue |
| --- | --- | --- |
| P3 | `comp_fun_idem (ac_join cfg)` | [#7](https://github.com/ManuelLerchner/goblint-formalization/issues/7) |
| P2 | `td_cfg_in_reach` | [#8](https://github.com/ManuelLerchner/goblint-formalization/issues/8) |
| P1 | `TD_plain.solve_dom` | [#14](https://github.com/ManuelLerchner/goblint-formalization/issues/14) (total correctness / finite `pp`) |

---

## Tomorrow — start here

**Primary: [#7 — Discharge P3](https://github.com/ManuelLerchner/goblint-formalization/issues/7)**  
Derive `comp_fun_idem` from `sound_domain` join laws instead of assuming it on
`pipeline_invariant_sound` / `goblint_*_sound`.

Why first:

- Listed in `OPEN_PROBLEMS.md` as the **cheap win** (packaging, not new mathematics).
- Removes one explicit assumption from the headline theorems.
- Typically 1–2 focused sessions; good momentum before reachability (P2).

**First hour**

1. I/Q: `open_file` `src/Domains/Abstract_Domain.thy` — join laws, `comp_fun_idem_sup`.
2. `explore` goal: pointwise `comp_fun_idem` on `'a abs_state` from `sound_domain`.
3. New lemma (e.g. `join_state_comp_fun_idem`); use in `Pipeline.thy` / `Goblint_Formalization.thy`.
4. Drop `cfi` / `join_cfi` assumptions where the lemma applies.

**Fallback (no proof progress)**

- Thesis prose from `docs/walkthrough/` (interval instance mirrors sign).
- Or executability polish ([#16](https://github.com/ManuelLerchner/goblint-formalization/issues/16)).

---

## Next goals (short horizon)

| Priority | Goal | Issue | Payoff |
| --- | --- | --- | --- |
| 1 | Drop **P3** | **#7** | Cleaner main theorems |
| 2 | Drop **P2** | **#8** | Second assumption gone; CFG reachability + TD `reach` |
| 3 | **Thesis writing** | **#17** | Bridges documented in walkthrough; PDF still open |
| 4 | Executability | **#16** | Per-pp `value` works; full `run_analysis` map still open |
| 5 | Session split | **#13** | Core vs Stretch — needs `TD_Soundness` / `Pipeline` import refactor |

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
