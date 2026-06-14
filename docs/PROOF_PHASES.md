# Proof status

Execution status and sorry inventory. Overview: `docs/PROOF_OVERVIEW.md`.
Roadmap: `docs/ROADMAP.md`.

---

## Target theorems

**Trace soundness (per-pp):** `alpha_last (cfg_collect_trace_ip g S v) ⊆ γ(env v)`.
`Trace_IP_Analysis_Sound.trace_ip_analysis_sound`.

**Global read soundness:** For every reaching trace `tr` at `v`, `(last tr) x ∈ γ(env v x)`.
`Trace_IP_Analysis_Sound.reaching_global_read_sound`.

**Sign domain exit:** `pruns_to_ip pi ps c s t` → `t ∈ γ(side_analyse_ip … exit)`.
`Sign_Side_IP_Soundness.side_ip_sign_analysis_sound`.

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
| `CFG_Collect_Edges.thy` | `edge_collect`, `collect_pp`, `cfg_collect` (intra lfp) |
| `CFG_Collect_Core.thy` | `cfg_collect_F`, intra collecting engine |
| `CFG_Collect_IP.thy` | `cfg_collect_ip` — IP collecting with combine triples |
| `CFG_Collect_IP_Adeq.thy` | `pruns_to_ip`, operational adequacy witness |
| `CFG_Collect_Unified.thy` | `collecting` locale; `intra.collect = cfg_collect`, `ip.collect = cfg_collect_ip` |
| `CFG_Collect_Trace.thy` | Intra trace collecting |
| `CFG_Collect_Trace_IP.thy` | `cfg_collect_trace_ip`, `alpha_last`, projection lemma |

### Equations + unified soundness

- `Constraint_System.thy` — `rhs`, `rhs_ip`, `is_post_fixpoint`, `is_post_fixpoint_ip`.
- `Constraint_System_Sound.thy` — `post_fixpoint_sound_at` (intra).
- `Constraint_System_IP_Sound.thy` — `post_fixpoint_sound_at_ip` (interprocedural).
- `Analysis_Sound.thy` — `unified_post_fixpoint_sound_ip` (single engine; U2 migration).

### Side-effecting TD solver bridge

- `TD_Side_CFG.thy` — `restrict_local`, `restrict_global`, `side_env`, `side_cfg_T` base.
- `TD_Side_IP_CFG.thy` — `side_cfg_T_ip`, `side_rhs_ip`, `ip_reaches`, `ip_succ`; monotonicity.
- `TD_Side_IP_Interface.thy` — `side_cfg_ip_solve_dom`, `side_analyse_ip`; imports `TD.TD_side`.
- `TD_Side_IP_Soundness.thy` — `side_analyse_ip_collect_sound_exit_pruned` via reach cone + pruning.

### Pipeline + domain

- `trace_ip_analysis_sound`, `reaching_global_read_sound`, `reaching_global_read_sound_d`, `flat_env_is_digest_sound` (`Trace_IP_Analysis_Sound.thy`).
- `side_ip_sign_analysis_sound` (`Sign_Side_IP_Soundness.thy`).
- `proc_global_side_sign_analysis` (`Example_Side_Proc_Global.thy`) — concrete procedural witness.

### Classical spine retirement

The intra-procedural (classical) spine — plain `TD_Soundness`, intra `Sign`/`Interval`
analysis, `Pipeline.thy`, `voblint_sign_sound` — was extracted to
`voblint-formalization-classical` and removed. See `docs/CLASSICAL_SPINE_RETIREMENT.md`.

---

## Open / stretch

- Discharge **`side_cfg_ip_solve_dom`** — last solver termination hypothesis (cf. P1 in `docs/OPEN_PROBLEMS.md`).
- **Interval / octagon** domains — fit the `sound_transfer` locale; no `Interval_Domain.thy` in current tree.
- **Digest-indexed combine** (M4 precision) — `reaching_global_read_sound_d` is the hook.

```bash
gh issue list --state open
```

---

## Maintenance

1. After lemma changes: `rg -n '^\s*sorry' src/` and check the table above.
2. Batch verify: `isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization`
3. Refresh matching `src/<layer>/README.md` when a layer changes materially.
