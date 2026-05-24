# Proof status

Execution status and sorry inventory. Overview: `docs/PROOF_OVERVIEW.md`.
Walkthrough: `docs/PIPELINE_WALKTHROUGH.md` (HTML copies under `docs/html/` may lag).
Roadmap: `docs/ROADMAP.md`.

---

## Target theorems

**Canonical (path-based, per-pp):** `cfg_path (to_cfg c) (cfg_entry …) es v` and
`t ∈ edges_collect es {s}` imply `t ∈ γ_state (σ v)` — no termination premise.
`Pipeline.pipeline_sound_path`.

**Point-map (lfp):** `∀ v. cfg_collect (to_cfg c) {s} v ⊆ γ_state (σ v)`.
`Pipeline.pipeline_invariant_sound` / `sign_pipeline_invariant_sound`.

**Exit corollary:** `runs_to c s t` (equivalently `t ∈ cfg_collect … exit`) implies
`t ∈ γ_state (σ (cfg_exit (to_cfg c)))`. `Pipeline.pipeline_sound_runs_to`.

**Small-step link:** `runs_to_iff_small_step` in `CFG_Runs_To_Bridge.thy` (via `CFG_Collecting` umbrella).

**Sign end-to-end:** `goblint_sign_sound` in `Goblint_Formalization.thy`.

**Non-terminating showcase:** `Example_NonTerminating_Safe.thy` — intermediate-pp
safety via `pipeline_sound_path` without any terminating run.

---

## Sorry inventory

Source of truth:

```bash
rg -n '^\s*sorry' src/ | rg -v '\.thy~'
```

As of last full-session build: **0 sorries** on the main chain under
`options [quick_and_dirty]` in `ROOT` (stretch theories may still use `oops` in
examples only — re-run the command after changes).

| Area | Notes |
| --- | --- |
| `IMP2/`, `CFG/`, `Equations/Constraint_System_Sound.thy` | Collecting ↔ post-fixpoint bridges closed |
| `Goblint_Formalization.thy`, sign pipeline | `goblint_sign_sound` closed |
| `Solver/TD_Soundness.thy`, `Pipeline.thy`, `Interval_Domain.thy` | Interval packaging — verify with `rg` |
| `Scratch_Explore.thy` | MCP scratch only; not in session build |

---

## Completed milestones

### Collecting and equations

- `cfg_collect` / `cfg_edges_collect` / path–lfp alignment (CFG collecting layer).

**CFG collecting files** (import chain; umbrella `CFG_Collecting.thy`):

| File | Role |
| --- | --- |
| `CFG_Edges_Collect.thy` | `edge_collect`, `edges_collect`, `cfg_collect` lfp |
| `CFG_Collecting_Core.thy` | `cfg_edges_collect`, path↔lfp bridge |
| `CFG_Compound_Paths.thy` | Seq/If/While path structure |
| `CFG_Path_Bridge.thy` | `compile_path_small_step`, path soundness |
| `CFG_Runs_To_Bridge.thy` | `runs_to_def`, small-step ↔ `cfg_collect` |
- `post_fixpoint_sound`, `exit_sound` (`Constraint_System_Sound.thy`).
- `td_analyse_post_fixpoint`, `sign_analysis_sound` (`TD_Interface`, `TD_Soundness`).

### Pipeline (sign)

- `pipeline_invariant_sound`, `pipeline_sound_path`, `pipeline_sound_runs_to`.
- `sign_pipeline_sound`, `sign_pipeline_invariant_sound`, `goblint_sign_sound`.

### Semantics cleanup (landed)

- No `big_step`, no AST `collect`, no `Direct_Equations`, no `TD_Total` on the path.
- `runs_to` = exit projection of `cfg_collect`; small-step bridge retained.

---

## Open / stretch (see roadmap)

Tracked on **[GitHub Project 8](https://github.com/users/ManuelLerchner/projects/8)** and
`docs/OPEN_PROBLEMS.md` (P1–P10 catalogue):

- Discharge or document **TD hypotheses** (`solve_dom`, `td_cfg_in_reach`, `comp_fun_idem`).
- **Interval / octagon** domains and executability.
- Remaining **Phase 4** automation (`IMP2_to_CFG` apply scripts, path-lifting combinators).
- Remove **`quick_and_dirty`** from `ROOT` when the session is sorry-free by policy.

```bash
gh issue list --state open --label phase:stretch
```

---

## Maintenance

1. After lemma changes: `rg -n '^\s*sorry' src/` and update the table above.
2. Batch verify: `isabelle build -v -d ~/afp/thys -d vendor/td-verification -D . Goblint_Formalization`
3. Refresh `docs/html/` if `PIPELINE_WALKTHROUGH.md` changes materially.

---

## Risks

| Risk | Mitigation |
| --- | --- |
| `make_rhs_tree` / `predecessor_list` order | Join must be commutative + idempotent; see `Constraint_System.thy` |
| Doc drift vs `.thy` names | Prefer `rg '^(lemma\|theorem)' src/` over hand-maintained lists |
| Session / AFP drift | Fixed build command in `AGENTS.md` / `CLAUDE.md` |
