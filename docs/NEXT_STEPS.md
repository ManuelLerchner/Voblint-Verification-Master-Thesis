# Next steps

Short-term work plan (updated 2026-06). Issues: `gh issue list --state open`.
Catalogue: `docs/OPEN_PROBLEMS.md`. Architecture: `docs/ROADMAP.md`.

---

## Where we are

**Done**

- Full IP soundness chain: IMP2 with procedures → interprocedural CFG → `cfg_collect` → side-effecting TD solver → `trace_ip_analysis_sound` / `reaching_global_read_sound`.
- Sign and Interval domain end-to-end on the standalone effectful path: `side_sign_analysis_sound`, `side_ivl_analysis_sound`, executable `sign_exec_sound_collecting` via `Exec_Bridge`.
- **Effectful spine is the sole spine** (2026-06-18): all pure-only solver files (`TD_Side_IP_Soundness`, `TD_Side_IP_Interface`, `TD_Side_IP_Bounds`, `TD_Side_IP_Mono`) deleted; `side_cfg_T_ip_eff` is the only equation system; shim mono in `TD_Side_Eff_Soundness`, transport in `Exec_Bridge` via direct fold simulation.
- **0 sorries** in `src/`.
- **`sound_domain`/`abstract_domain` → type classes** (2026-06-23): `locale sound_domain` and `locale abstract_domain` replaced by `class sound_domain` and `class abstract_domain`; `gamma` is now a single class operation; `gamma_state`/`widen_state` are global definitions with `⟦_⟧` notation; Sign and Interval instantiated via `instantiation` blocks; `backward_domain` drops the `γ` parameter; solver theorems require only `'a::sound_domain` constraints. `Update_rules.N` shadow clash fixed via `hide_const (open)` in `Abstract_Domain`, `Sign_Domain`, `Interval_Domain`.
- Trace semantics (`cfg_collect_trace`) + projection (`alpha_last`) + soundness morphism.
- AFP IMP2 bridge + VCG co-existence example.
- Classical (intra) spine extracted to sibling repo `voblint-formalization-classical`.

**Explicit hypotheses (out of scope by design)**

| ID | Assumption | Stance |
| --- | --- | --- |
| P1 | `side_cfg_solve_dom_eff … (cfg_exit …)` | Vendor's obligation. `TD_side` is vendored from `td-verification`; its termination is not our proof obligation. Our result is conditional soundness: *if* the solver terminates, the abstract result is sound. See `docs/NON_GOALS.md`. |

---

## Now — start here

**Primary: [#17 — Thesis writing](https://github.com/ManuelLerchner/voblint-formalization/issues/17)**

The IP soundness chain is complete. `side_cfg_solve_dom` (P1) is explicitly
out of scope — a vendor hypothesis, not ours. Write up.

**Alternatives**

- **NONDET_HAVOC** — add `x := random()` to the language; first nondeterministic construct, demonstrates pipeline extensibility. See `docs/NONDET_HAVOC_MIGRATION.md`.
- **Digest fork S1** — `Digest` locale + `CallString` interpretation, no sorry. See `docs/TRACE_BASED_FORK_MIGRATION.md`.

---

## Next goals (short horizon)

| Priority | Goal | Payoff |
| --- | --- | --- |
| 1 | **Thesis writing** | Core chain proved; write-up is the blocker |
| 2 | NONDET_HAVOC | Language extension; demonstrates pipeline extensibility |
| 3 | Digest fork S1 | First step toward context-sensitivity |
| 4 | Interval domain | Second numeric domain; same scaffold |

**Defer unless scope expands**

- Octagon domain — 4–6 weeks min; see `docs/ROADMAP.md` for difficulty notes.
- Session split (Core / Stretch) — needs import refactor.

---

## Suggested week

```text
Day 1–2:  Thesis prose (IP soundness + trace semantics chapter) from docs/PROOF_OVERVIEW.md
Parallel:  P1 (solve_dom total correctness) — closes last TD hypothesis
Later:     Interval domain OR digest precision — one of, not both
```

---

## Thesis milestone (next "done" slice)

> IP trace soundness with **only `side_cfg_solve_dom`** as explicit hypothesis,
> plus thesis chapter covering `trace_ip_analysis_sound` / `reaching_global_read_sound`.

---

## References

- `docs/OPEN_PROBLEMS.md` — P1, bridge diagram
- `docs/PROOF_PHASES.md` — sorry inventory, completed milestones
- [GitHub Project 8](https://github.com/users/ManuelLerchner/projects/8) — board view
