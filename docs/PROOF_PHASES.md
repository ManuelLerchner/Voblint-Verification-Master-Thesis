# Proof phases

Execution status and sorry inventory. Overview: `docs/PROOF_OVERVIEW.md`.
Walkthrough: `docs/PIPELINE_WALKTHROUGH.md` (HTML copies under `docs/html/` may lag).
Roadmap and live backlog: `docs/ROADMAP.md`.

---

## Target theorems

**Canonical (path-based, per-pp):** `cfg_path (to_cfg c) (cfg_entry ...) es v` and
`t ∈ edges_collect es {s}` imply `t ∈ γ_state (σ v)` — at every CFG-reachable pp,
no big-step premise. Proved as `Pipeline.pipeline_sound_path` (`f86603d`).

**Big-step exit corollary:** `(c, s) ⇒ t` implies `t ∈ γ_state (σ (cfg_exit (to_cfg c)))`.
Proved as `Pipeline.pipeline_sound`, now derived from `pipeline_sound_path` via `big_step_cfg_path`.

**Small-step exit corollary:** `(c, s) →* (SKIP, t)` implies `t ∈ γ_state (σ (cfg_exit (to_cfg c)))`.
Proved as `Pipeline.pipeline_sound_small_step`, derived from `pipeline_sound` via `small_step_big_step_eq`.

**Point-map invariant (lfp form):** `∀ v. cfg_collect (to_cfg c) {s} v ⊆ γ_state (σ v)` —
proved unconditionally for sign via `sign_pipeline_invariant_sound`.

**Non-terminating safety showcase:** `Example_NonTerminating_Safe.thy` — instantiates
`pipeline_sound_path` on `x := 10; while True do skip` to show intermediate-pp safety
is expressible (and provable) despite the program never reaching a big-step result.

---

## Sorry inventory

Source of truth: `rg -n '^\s*sorry' src/`

| File                                                     |    n | Notes                        |
| -------------------------------------------------------- | ---: | ---------------------------- |
| `IMP2/`, `CFG/`, `Equations/Constraint_System_Sound.thy` |    0 | Bridges #1 and #2 closed     |
| `Goblint_Formalization.thy`, sign pipeline               |    0 | `goblint_sign_sound` closed  |
| `Solver/TD_Soundness.thy`                                |    1 | `interval_analysis_sound`    |
| `Pipeline/Pipeline.thy`                                  |    1 | `ivl_pipeline_sound`         |
| `Domains/Interval_Domain.thy`                            |    5 | Interval stretch             |
| `Solver/TD_Total.thy`                                    |    8 | Optional totality / widening |
| `Equations/Direct_Equations.thy`                         |    7 | Alternate AST path (skip)    |
| `Scratch_Explore.thy`                                    |    1 | MCP scratch only             |

Sign pipeline builds with `quick_and_dirty`; remaining sorries are outside the sign chain.

---

## Phase 1 Collecting bridges **DONE**

### 1.1 IMP ↔ CFG at exit (`CFG_Collecting.thy`)

- `cfg_collect_exit_eq_collect` and supporting path/compile lemmas.

### 1.2 Post-fixpoint soundness (`Constraint_System_Sound.thy`)

- `collect_pp_abstract_sound`, `post_fixpoint_sound`, `exit_sound`.

---

## Phase 2 Pipeline (sign) **DONE**

- `pipeline_invariant_sound`, `pipeline_sound`
- `sign_pipeline_sound_scaffold`, `sign_pipeline_invariant_sound`
- `goblint_sign_sound` (top-level)

**TD hypotheses (explicit on `goblint_sign_sound`):** `comp_fun_idem` on
`sign_domain.join_state`, `TD_plain.solve_dom` at `cfg_entry`, and `cfg_in_reach` for the
solved tree. Soundness of γ-overapproximation does not depend on these; they say the
verified solver actually returns a post-fixpoint on this CFG. See `PROOF_OVERVIEW.md`
§ TD hypotheses.

---

## Phase 3+ Beyond sign — see roadmap

Active work (interval pipeline, backward transformers, reduced product, total
correctness, octagon, executable demos, thesis writeup) is tracked on
**[GitHub Project 8](https://github.com/users/ManuelLerchner/projects/8)** with
explicit dependency arrows via `blockedBy`. Filter by label:

```bash
gh issue list --state open --label phase:stretch
gh issue list --state open --label source:blazy-2013
```

Architectural directions (no issue numbers — they drift): `docs/ROADMAP.md`.
The historical "Phase 3 / Phase 4" linear sequencing is superseded by the issue
DAG.

---

## Phase 4 Polish

- Examples: `Example_Sign_Analysis.thy` (verify on change).
- Remove `quick_and_dirty` from `ROOT` once stretch goals are resolved or explicitly deferred.
- Refresh `docs/html/` walkthroughs if the markdown sources change.
- Optional: `docs/PROOF_SIMPLIFICATION.md` if shrinking `CFG_Collecting.thy`.

---

## Working order

1. ~~CFG collecting bridge~~ **done**
2. ~~Post-fixpoint soundness~~ **done**
3. ~~Sign pipeline~~ **done**
4. Interval domain (optional)
5. Examples + batch build without `quick_and_dirty`

---

## Risks (stretch / maintenance)

| Risk                                                | Mitigation                                                                          |
| --------------------------------------------------- | ----------------------------------------------------------------------------------- |
| `make_rhs_tree_correspondence` / predecessor `SOME` | List-based preds must be join-order independent; redesign `make_rhs_tree` if stuck  |
| Interval proof creep                                | Finish lattice + TF lemmas before pipeline packaging                                |
| `Direct_Equations` scope                            | Alternate AST path skip unless thesis needs `direct_eq_cfg_analyse`                 |
| Session / AFP drift                                 | `isabelle build -d ~/afp/thys -d vendor/td-verification -D . Goblint_Formalization` |
| Doc drift                                           | Sorry counts: `rg -n '^\s*sorry' src/`; update this file when inventory shifts      |
