# Proof status

Execution status and sorry inventory. Overview: `docs/PROOF_OVERVIEW.md`.
Roadmap: `docs/ROADMAP.md`.

---

## Target theorems

**Trace soundness (per-pp):** `alpha_last (cfg_collect_trace g S v) ⊆ γ(env v)`.
`Trace_Analysis_Sound.trace_analysis_sound`.

**Global read soundness:** For every reaching trace `tr` at `v`, `(last tr) x ∈ γ(env v x)`.
`Trace_Analysis_Sound.reaching_global_read_sound`.

**Sign domain exit:** `cfg_runs_to pi ps c s t` → `t ∈ γ(side_analyse_eff … exit)`.
`Sign_Side_Soundness.side_sign_analysis_sound`.

**Concrete witness:** `proc_global_side_sign_analysis` in `Example_Side_Proc_Global.thy`.

---

## Sorry inventory

Source of truth:

```bash
rg -n '^\s*sorry' src/ | rg -v '\.thy~'
```

As of last full-session build: **0 sorries** in `src/`.

---

## Completed milestones

### IMP2 language + procedures

- `com` extended with Scope / Call / Restore; frame-stack `pstep` semantics.
- `combine_states`, `enter_state`, `is_global` (`IMP2_Globals.thy`).
- `compile_prog pi ps c` → interprocedural CFG with enter edges + combine triples.
- Bridge to AFP IMP2 (`IMP2_Bridge.thy`); VCG example (`IMP2_VCG_Example.thy`).

### CFG collecting files (`src/CFG/Collecting/`)

| File | Role |
| --- | --- |
| `CFG_Collect.thy` | edge/path transfer, `cfg_collect` — IP collecting with combine triples, and the path-to-lfp bridge |
| `CFG_Collect_Runs.thy` | `cfg_runs_to`, run-to-exit collecting witness |
| `CFG_Collect_Trace.thy` | `cfg_collect_trace`, `alpha_last`, projection lemma; shared trace machinery |

### Equations + unified soundness

- `Constraint_System.thy` — `rhs`, `is_post_fixpoint`, `combine_abs`, `etf_full`, `glob_env`.
- `Constraint_System_Sound.thy` — `post_fixpoint_sound_at` + IP bounds (merged from former `Constraint_System_IP_Sound`).
- `Analysis_Sound.thy` — `unified_post_fixpoint_sound` (single engine).

### Side-effecting TD solver bridge

- `TD_Side_CFG.thy` — `restrict_local`, `restrict_global`, `side_env`, `side_cfg_T` base.
- `TD_Side_Tree.thy` — `side_cfg_T_eff` construction and denotation; pure fold retained as simulation stepping stone in `Exec_Bridge`.
- `TD_Side_Eff_Bounds.thy` — generic `_gen` mono and static-deps preconditions; `TD_Side_Eff_Sound.thy` — shim mono for `etf_from_tf`.
- `TD_Side_Eff_Interface.thy` — `side_cfg_solve_dom_eff`, `side_analyse_eff`; imports `TD.TD_side`.
- `TD_Side_Eff_Soundness.thy` — `side_analyse_eff_collect_sound_exit_pruned_gen` via reach cone + pruning.

### Pipeline + domain

- `trace_analysis_sound`, `reaching_global_read_sound`, `reaching_global_read_sound_d`, `flat_env_is_digest_sound` (`Trace_Analysis_Sound.thy`).
- `side_sign_analysis_sound`, `side_ivl_analysis_sound` (`Sign_Side_Soundness.thy`).
- `named_analysis_sound` (`Sign_Named_Global_Eff.thy`) — non-unit `'g` witness closing the Gap-1 instantiation gap.
- `proc_global_side_sign_analysis` (`Example_Side_Proc_Global.thy`) — concrete procedural witness.

### Classical spine retirement

The intra-procedural (classical) spine — plain `TD_Soundness`, intra `Sign`/`Interval`
analysis, `Pipeline.thy`, `voblint_sign_sound` — was extracted to
`voblint-formalization-classical` and removed. See `docs/CLASSICAL_SPINE_RETIREMENT.md`.

---

## Open / stretch

- **`side_cfg_solve_dom`** — deliberately kept as an explicit hypothesis (P1).
  Termination of the vendored `TD_side` solver is the vendor's obligation, not
  ours. Our result is conditional soundness: *if* the solver terminates, the
  abstract result over-approximates `cfg_collect`. See `docs/NON_GOALS.md` and
  `docs/P1_TOTAL_CORRECTNESS_ROUTE.md`.
- **Interval / octagon** domains — `Interval_Domain.thy` exists; `side_ivl_analysis_sound` carries P1.
- **Digest-indexed combine** (M4 precision) — `reaching_global_read_sound_d` is the hook.

```bash
gh issue list --state open
```

---

## Maintenance

1. After lemma changes: `rg -n '^\s*sorry' src/` and check the table above.
2. Batch verify: `isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization`
3. Refresh matching `src/<layer>/README.md` when a layer changes materially.
