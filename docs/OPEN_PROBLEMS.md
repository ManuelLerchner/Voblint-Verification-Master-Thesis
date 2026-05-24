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
| B6 | `comp_fun_idem (ac_join cfg)` | `Pipeline.thy` assumptions | open (P3) |
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
| P2 | `td_cfg_in_reach` assumed | `Pipeline.thy` | Solver tree reach vs CFG pp reach | Drop one assumption |
| P3 | `comp_fun_idem (ac_join cfg)` assumed | `Pipeline.thy` | Finite fold needs commutative idempotent join | Drop user obligation |
| P4 | Interval domain stretch | `Interval_Domain.thy` | Second domain end-to-end packaging | Interval thesis example |
| P5 | `pp = nat` vs TD `finite UNIV` | `CFG_Def.thy`, vendored TD | Termination locale type finiteness | Generic termination claim |
| P6 | TD total correctness | was `TD_Total.thy` | **file removed**; reopen if totality returns | Total correctness |
| P7 | Widening soundness | `Interval_Domain.thy` | Feeds termination track | Interval + widening |
| P8 | `quick_and_dirty` in `ROOT` | `ROOT` | Batch ignores sorries in stretch | Sorry-free core session |
| P9 | Executable end-to-end limited | `Example_Sign_Analysis.thy` | `value` on full maps only for finite domains | In-Isabelle execution |
| P10 | `Direct_Equations` | was `Equations/Direct_Equations.thy` | **deleted** — CFG path is the only route | — |

---

## Per-problem notes

### P1 / P2 / P3 — assumptions on pipeline theorems

`pipeline_invariant_sound`, `pipeline_sound_path`, and `pipeline_sound_runs_to`
carry three TD-side assumptions:

```isabelle
assumes cfi:             "comp_fun_idem (ac_join cfg)"   -- P3
assumes td_solve_dom:    "TD_plain.solve_dom ..."        -- P1
assumes td_cfg_in_reach: "\<And>v. v \<in> reach ..."    -- P2
```

P2: CFG-shape + solver reach — check `TD_plain` for prior art.
P3: should follow from `sound_domain` join laws once packaged as a lemma.
P1: gated on P5 for generic termination.

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

1. `rg -n '^\s*sorry' src/ | rg -v '\.thy~'`
2. `docs/PROOF_OVERVIEW.md` — current theorem names
3. `src/Pipeline/Pipeline.thy` — `pipeline_invariant_sound`, `pipeline_sound_path`
4. P3 lemma packaging is a cheap win; P8 is cosmetic
5. MCP-first workflow: `AGENTS.md`
