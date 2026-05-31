# Open problems and handoffs

Catalogue of repo-level problems with stable file:line refs (P1–P10). For *new
work and extensions*, see `docs/ROADMAP.md` + [GitHub Project 8](https://github.com/users/ManuelLerchner/projects/8).

Source of truth for live sorries:

```bash
rg -n '^\s*sorry' src/ | rg -v '\.thy~'
```

Related: `docs/HOL_IMP_COMPARISON.md`, `docs/PROOF_PHASES.md`, `docs/PROOF_OVERVIEW.md`.

---

## Bridges in the soundness chain

```
cfg_collect (spec at each pp)
       |
       |  post_fixpoint_sound (B3)
       v
gamma_state (env v)  <-----  td_analyse output (B4)
       ^
       |  [P1 solve_dom] [P2 td_cfg_in_reach] [P3 comp_fun_idem]
       |
   TD_plain solver
```

| Bridge | Statement | Where | Status |
| --- | --- | --- | --- |
| B3 | `is_post_fixpoint env ==> ∀v. cfg_collect g S v ⊆ gamma_state (env v)` | `Constraint_System_Sound.thy` | done |
| B4 | `td_analyse` output is a post-fixpoint | `TD_Interface.thy` | done (modulo P1–P3 as hyps) |
| B5 | `td_cfg_in_reach` — solver covers reachable tree nodes | `Pipeline.thy` assumptions | open (P2) |
| B6 | `comp_fun_idem (ac_join cfg)` | `Pipeline.thy` assumptions | **done** (P3 — `join_state_comp_fun_idem`) |
| B7 | `TD_plain.solve_dom … (cfg_entry …)` | `Pipeline.thy` assumptions | open (P1) |
| B8 | Interval widening + termination | `Interval_Domain.thy` | stretch (P6/P7) |

**Exit link:** `runs_to c s t` is definitional exit `cfg_collect` (`runs_to_def`).
`exit_sound` uses `exit_in_collect` / `cfg_collect` at exit, not big-step.

**Operational link:** `runs_to_iff_small_step` connects small-step termination to `runs_to`.

Optional / removed from main path:

| Item | Status |
| --- | --- |
| `Direct_Equations.thy` | **deleted** — was alternate AST path (P10 abandoned) |
| `TD_Total.thy` | **deleted** — was orphan totality track (P6) |
| HOL-IMP `Abs_Int2_ivl` reuse | not started; see `HOL_IMP_COMPARISON.md` |

`pipeline_invariant_sound` / `pipeline_sound_path` carry P1–P3 as named assumptions.

---

## Problem catalogue

| ID | Problem | Files | Why it blocks | Needed for |
| --- | --- | --- | --- | --- |
| P1 | `TD_plain.solve_dom` assumed | `Pipeline.thy`, `TD_Interface.thy` | "If TD terminates, result is sound" | Cleaner main theorem; total correctness (gated on P5) |
| P2 | `td_cfg_in_reach` assumed (**structural, false in current shape**) | `Pipeline.thy` | Solver reach from entry = `{entry}` only; assumption false. See P2 finding below | Real (non-vacuous) soundness |
| P3 | `comp_fun_idem (ac_join cfg)` assumed | `Pipeline.thy` | Finite fold needs commutative idempotent join | **done** 2026-05-27; lemma `join_state_comp_fun_idem` |
| P4 | Interval domain stretch | `Interval_Domain.thy` | ~~Second domain~~ | **done** — `ivl_pipeline_sound`, `goblint_interval_sound`; still carries P1–P3 |
| P5 | `pp = nat` vs TD `finite UNIV` | `CFG_Def.thy`, vendored TD | Termination locale type finiteness | Generic termination claim |
| P6 | TD total correctness | was `TD_Total.thy` | **file removed**; reopen if totality returns | Total correctness |
| P7 | Widening soundness | `Interval_Domain.thy` | Feeds termination track | Interval + widening |
| P8 | `quick_and_dirty` in `ROOT` | `ROOT` | ~~Batch ignores sorries~~ | **done** — removed; optional Core/Stretch session split remains |
| P9 | Executable end-to-end limited | `Example_Sign_Analysis.thy` | `value` on full maps only for finite domains | In-Isabelle execution |
| P10 | `Direct_Equations` | was `Equations/Direct_Equations.thy` | **deleted** — CFG path is the only route | — |

---

## Per-problem notes

### P1 / P2 / P3 — assumptions on pipeline theorems

`pipeline_invariant_sound`, `pipeline_sound_path`, and `pipeline_sound_runs_to`
carry these TD-side assumptions:

```isabelle
assumes td_solve_dom:    "TD_plain.solve_dom ..."        -- P1
assumes td_cfg_in_reach: "\<And>v. v \<in> reach ..."    -- P2
```

P3 discharged 2026-05-27 via `join_state_comp_fun_idem`
(`Abstract_Domain.thy`); see commit `1c119d3`. Top-level theorems
now carry only P1, P2.

P1 is gated on P5 for generic termination.

P2: see finding below — **not** a simple lemma bridge.

### P2 finding (2026-05-27) — structural inconsistency

`td_cfg_in_reach` is the hypothesis

```isabelle
\<And>v::pp. v \<in> reach T sigma (cfg_entry g)
```

where `T = make_rhs_tree (to_cfg c) tf join bot s0` and
`sigma = TD_plain_Interp_solve T (cfg_entry g)`.

#### Why it is false

- `reach T sigma x` (`vendor/td-verification/Basics.thy:278`) is the set
  of unknowns transitively queried while computing `eq T x sigma`.
  Inductively: `x \<in> reach T sigma x`; if `y \<in> reach T sigma x` and
  `z \<in> dep T sigma y` then `z \<in> reach T sigma x`.
- `dep T sigma y = dep_aux sigma (T y)` (`Basics.thy:212`) is the set of
  `Query` targets in the strategy tree at `y`.
- `make_rhs_tree g tf join bot s0 v` (`src/Solver/TD_CFG_Core.thy:62`)
  builds the forward dataflow equation: `Query` nodes target
  `predecessor_list g v`.
- Therefore `dep T sigma v` = CFG predecessors of `v`, and
  `reach T sigma entry` = `{entry}` ∪ predecessors-of-entry ∪ ... .
- `to_cfg` constructions give entry no predecessors, so

  ```
  reach T sigma (cfg_entry g) = {cfg_entry g}
  ```

The assumption then claims `\<forall>v. v = cfg_entry g`. False for any
program with more than one program point.

#### Concrete example

Take `c = ''x'' ::= N 5`. The compiled CFG `to_cfg c` has two pp's:
`cfg_entry g = 0`, `cfg_exit g = 1`, with a single Assign edge
`(0, x:=5, 1)`. Then:

- `predecessor_list g 0 = []` (entry has no predecessors).
- `dep T sigma 0 = {}`, so `reach T sigma 0 = {0}`.
- `td_cfg_in_reach` at `v = 1` requires `1 \<in> {0}`. False.

Instantiating `goblint_sign_sound` on this `c` is impossible: discharging
`td_cfg_in_reach` would require proving false.

The proofs go through only because the hypothesis is left abstract — no
example actually discharges it. The soundness chain holds *vacuously* on
a false premise.

#### Where it bites in the proof

`td_env_post_fixpoint` (`src/Solver/TD_Interface.thy:38-58`) closes the
post-fixpoint goal at arbitrary `v` via

```
part_solutionD[OF psol v_reach]
```

`psol : part_solution cfg_T entry sigma (reach cfg_T sigma entry)`
gives the equation only on `reach`. `v_reach : v \<in> reach ...` is the
P2 assumption that bridges to "for all `v`". Without P2 actually true,
this step is unjustified at non-entry `v`.

#### Possible fixes

**A. Solve at exit, prove backwards-reachability as CFG side condition.**

- Change `td_solve_dom T (cfg_exit g)` and `... \<in> reach T sigma (cfg_exit g)`.
- New lemma: every pp on an entry→exit path is in
  `reach T sigma exit` (equivalent to "backwards-reachable from exit").
- Provable from `to_cfg` structure by induction on the program.
- **Breaks for non-terminating programs.** `nonterm_prog`,
  `incr_loop_prog` have no entry→exit path; exit is reachable in
  neither the CFG nor `reach`. Loop-body pp's would need a separate
  solve point.

**B. Per-pp solve (cleanest).**

- Redefine

  ```isabelle
  td_analyse c tf join bot s0 v
    \<equiv> lookup_bot (Interp_solve (make_rhs_tree ...) v) v
  ```

  One solve per query. Each solve fills the queried node's transitive
  predecessors.
- The reach hypothesis becomes `v \<in> reach T sigma_v v`, which is
  `reach.base` — **trivially true**.
- The solve-termination hypothesis becomes per-pp: `\<forall>v. solve_dom T v`.
  Slightly stronger than the single `solve_dom T entry` we have now,
  but in line with how TD is actually used.
- Pipeline theorems quantify per-pp termination, no architectural
  inversion.
- Cost: more solver invocations at run time. Acceptable for a
  formalization — Goblint's real worklist solver covers everything in
  one pass; this is a proof artifact.

**C. Invert the equation system (rejected).**

- Make `make_rhs_tree` query *successors* (`successor_list g v`) instead
  of predecessors. Then `reach T sigma entry` covers everything
  forward-reachable from entry.
- But the resulting equation is a backwards predicate transformer, not
  the forward dataflow equation. Sign/interval analyses are forward;
  this changes their meaning.
- Off-table for the existing domain track.

**D. Macro-solve over a covering root set.**

- Compute a set `R \<subseteq> pp` whose backward-reach covers every pp,
  call TD once per root, merge.
- Effectively Fix B with the solve set chosen up front. More machinery,
  same trade-off.

**Recommendation.** Fix B. Cleanest mathematically (`reach.base`
discharges the hypothesis, no CFG-side connectivity proof needed),
covers terminating and non-terminating examples uniformly, no
architectural inversion. Cost is a minor refactor of `td_analyse` and
the pipeline statement shape (per-pp solve termination instead of
single-point), not weeks of work.

**Track B overlap.** B3 (side-effecting TD) already reshapes the
`strategy_tree` signature (`Side`/`QueryL`/`QueryG`). If B3 proceeds,
fold P2 into the B3 refactor rather than fix it standalone first.

#### Status

Surfaced for meeting 4 (2026-06-01). See
`wiki/meetings/2026-06-01-meeting4-prep.md`. No code change pending —
existing pipeline theorems left as-is until the supervisor verdict on
A2 strategy and Track B scope.

### P5 — type-level finiteness

See previous table (routes a/b/c). Partial-correctness thesis may keep P1 explicit.

### P4 / P7 — interval domain

Sign chain proved (`goblint_sign_sound`; carries P1–P3). Interval uses the same pipeline theorems with `ivl_pipeline_sound`.

### P6 — TD total correctness

`TD_Total.thy` removed from the tree. Reintroduce only if P5 is resolved and totality is in scope.

### P8 — session hygiene

Split core vs stretch sessions when sorry-free core is policy.

### P10 — Direct_Equations

**Abandoned.** File deleted; `Goblint_Formalization` imports CFG route only.

---

## Where to start

**Session plan:** `docs/NEXT_STEPS.md` (tomorrow: issue #8 / P2 — `td_cfg_in_reach`).

1. `rg -n '^\s*sorry' src/ | rg -v '\.thy~'`
2. `docs/PROOF_OVERVIEW.md` — current theorem names
3. `src/Pipeline/Pipeline.thy` — `pipeline_invariant_sound`, `pipeline_sound_path`
4. P3 is closed ([#7](https://github.com/ManuelLerchner/goblint-formalization/issues/7) done); current priority is P2 `td_cfg_in_reach` ([#8](https://github.com/ManuelLerchner/goblint-formalization/issues/8)); P8 session split is cosmetic ([#13](https://github.com/ManuelLerchner/goblint-formalization/issues/13))
5. MCP-first workflow: `AGENTS.md`
