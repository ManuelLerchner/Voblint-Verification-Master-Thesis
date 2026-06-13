# Next steps

Short-term work plan (updated 2026-06). Issues: `gh issue list --state open`.
Catalogue: `docs/OPEN_PROBLEMS.md`. Architecture: `docs/ROADMAP.md`.

---

## Where we are

**Done**

- Full IP soundness chain: IMP2 with procedures → interprocedural CFG → `cfg_collect_ip` → side-effecting TD solver → `trace_ip_analysis_sound` / `reaching_global_read_sound`.
- Sign domain end-to-end: `side_ip_sign_analysis_sound`, `proc_global_side_sign_analysis`.
- **0 sorries** in `src/`.
- Trace semantics (`cfg_collect_trace_ip`) + projection (`alpha_last`) + soundness morphism.
- AFP IMP2 bridge + VCG co-existence example.
- Classical (intra) spine extracted to sibling repo `voblint-formalization-classical`.

**Still open on main theorems**

| ID | Assumption | Status |
| --- | --- | --- |
| P1 | `side_cfg_ip_solve_dom g sign_tf bot s0 v` (per-pp solve termination) | open |

---

## Now — start here

**Primary: [#17 — Thesis writing](https://github.com/ManuelLerchner/voblint-formalization/issues/17)**

The IP soundness chain is complete. Only `side_cfg_ip_solve_dom` (P1) remains as an
explicit hypothesis — a defensible thesis stance. Write up.

**Alternative: P1 solve_dom total correctness**

Prove termination of the per-pp TD side solver (finite `pp`, well-founded recursion
in `TD_side`). Closes the last solver hypothesis.

**Fallback**

- Add Interval domain — fits the `sound_transfer` locale; no architectural changes needed.
- Examples / executability.

---

## Next goals (short horizon)

| Priority | Goal | Payoff |
| --- | --- | --- |
| 1 | **Thesis writing** | Core chain proved; write-up is the blocker |
| 2 | P1 `side_cfg_ip_solve_dom` | Closes the last solver hypothesis |
| 3 | Interval domain | Second numeric domain; same scaffold |
| 4 | Digest-indexed combine (M4 precision) | Context-sensitivity via `reaching_global_read_sound_d` |

**Defer unless scope expands**

- Octagon domain — 4–6 weeks min; see `docs/ROADMAP.md` for difficulty notes.
- Session split (Core / Stretch) — needs import refactor.

---

## Suggested week

```text
Day 1–2:  Thesis prose (IP soundness + trace semantics chapter) from docs/walkthrough
Parallel:  P1 (solve_dom total correctness) — closes last TD hypothesis
Later:     Interval domain OR digest precision — one of, not both
```

---

## Thesis milestone (next "done" slice)

> IP trace soundness with **only `side_cfg_ip_solve_dom`** as explicit hypothesis,
> plus thesis chapter covering `trace_ip_analysis_sound` / `reaching_global_read_sound`.

---

## References

- `docs/OPEN_PROBLEMS.md` — P1, bridge diagram
- `docs/PROOF_PHASES.md` — sorry inventory, completed milestones
- [GitHub Project 8](https://github.com/users/ManuelLerchner/projects/8) — board view
