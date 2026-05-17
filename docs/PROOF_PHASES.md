# Proof phases

Execution status and sorry inventory. Overview: `docs/PROOF_OVERVIEW.md`.
Walkthrough: `docs/PIPELINE_WALKTHROUGH.md` (HTML copies under `docs/html/` may lag).

---

## Target theorems

**Exit (main):** `big_step (c, s) t` implies `t ∈ γ_state (σ (cfg_exit (to_cfg c)))`.

**Point-map (strong):** `∀ v. cfg_reach (to_cfg c) {s} v ⊆ γ_state (σ v)` proved for
sign via `sign_pipeline_invariant_sound`.

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

## Phase 3 Interval stretch (optional)

Follow the domain recipe in `PROOF_OVERVIEW.md` § Adding a domain:

1. Close `Interval_Domain.thy` sorries (join laws, `gamma_ivl_*`, transfer soundness).
2. Discharge interval stubs in `Pipeline.thy` / `TD_Soundness.thy` (`ivl_pipeline_sound`,
   `interval_analysis_sound`).
3. Reuse Phase 2 templates no new bridge lemmas if the generic pipeline stays unchanged.

`Interval_Domain.thy`: lattice laws, transfer soundness, then instantiate Phase 2
template for `ivl_pipeline_sound` / `interval_analysis_sound`.

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
