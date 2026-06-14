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
cfg_collect_trace_ip (trace spec at each pp)
       |
       |  alpha_last projection (CFG_Collect_Trace_IP)
       v
cfg_collect_ip (state spec at each pp)
       |
       |  unified_post_fixpoint_sound_ip (Analysis_Sound / B3)
       v
gamma_state (env v)  <-----  side_analyse_ip output (B4)
       ^
       |  [P1 side_cfg_ip_solve_dom per pp]
       |
   TD_side solver (per-pp root at v, interprocedural)
```

| Bridge | Statement | Where | Status |
| --- | --- | --- | --- |
| B3 | `is_post_fixpoint_ip env ==> ∀v. cfg_collect_ip g S v ⊆ gamma_state (env v)` | `Analysis_Sound.thy` (`unified_post_fixpoint_sound_ip`) | done |
| B4 | per-pp `side_analyse_ip` sound w.r.t. `cfg_collect_ip` at queried `v` | `TD_Side_IP_Soundness.thy` (`side_analyse_ip_collect_sound_exit_pruned`) | done (modulo P1 as hyp) |
| B5 | ~~`td_cfg_in_reach`~~ — removed (Fix B, 2026-06-01) | was `Pipeline.thy` (classical spine) | **done** (historical; classical spine retired) |
| B6 | `comp_fun_idem (ac_join cfg)` | classical spine | **done** (historical; classical spine retired) |
| B7 | `side_cfg_ip_solve_dom g tf bot s0 v` for each queried `v` | `Sign_Side_IP_Soundness.thy` assumptions | open (P1) |

**Operational link:** `pruns_to_ip pi ps c s t` is definitional exit `cfg_collect_ip`
at `cfg_exit (compile_prog …)` (`CFG_Collect_IP_Adeq.thy`).

Optional / removed from main path:

| Item | Status |
| --- | --- |
| `Direct_Equations.thy` | **deleted** — was alternate AST path (P10 abandoned) |
| `TD_Total.thy` | **deleted** — was orphan totality track (P6) |
| Classical intra spine (`Pipeline.thy`, `TD_Soundness.thy`, etc.) | **extracted** to `voblint-formalization-classical` |

`trace_ip_analysis_sound` / `reaching_global_read_sound` carry **P1** (`side_cfg_ip_solve_dom`) as the only solver hypothesis.

---

## Problem catalogue

| ID | Problem | Files | Why it blocks | Needed for |
| --- | --- | --- | --- | --- |
| P1 | `side_cfg_ip_solve_dom` assumed | `Sign_Side_IP_Soundness.thy` | "If TD side terminates, result is sound" | Cleaner main theorem; total correctness |
| P2 | ~~`td_cfg_in_reach`~~ | was classical `Pipeline.thy` | **done** 2026-06-01 — Fix B; classical spine retired | (historical) |
| P3 | `comp_fun_idem (ac_join cfg)` | classical `Pipeline.thy` | **done** 2026-05-27 (`join_state_comp_fun_idem`); classical spine retired | (historical) |
| P4 | Interval domain | not in current tree | Second numeric domain | Wider thesis scope |
| P5 | `pp = nat` vs TD `finite UNIV` | `CFG_Def.thy`, vendored TD | Termination locale type finiteness | Generic termination claim |
| P6 | TD total correctness | was `TD_Total.thy` | **file removed**; reopen if totality returns | Total correctness |
| P7 | Widening soundness | not in current tree | Feeds termination track | Interval + widening |
| P8 | `quick_and_dirty` in `ROOT` | `ROOT` | **done** — removed | — |
| P9 | Executable end-to-end limited | `Example_Side_Proc_Global.thy` | Concrete solve_dom witness needed | In-Isabelle execution |
| P10 | `Direct_Equations` | was `Equations/Direct_Equations.thy` | **deleted** — CFG path is the only route | — |

---

## Per-problem notes

### P1 — solver termination assumption

`trace_ip_analysis_sound`, `reaching_global_read_sound`, and `side_ip_sign_analysis_sound`
ultimately require:

```isabelle
assumes side_solve_dom:
  "side_cfg_ip_solve_dom (compile_prog pi ps main) sign_tf bot s0
     (cfg_exit (compile_prog pi ps main))"
```

This is `TD_side.solve_dom destab_opt True (side_cfg_T_ip …) v`, i.e. termination
of the side-effecting per-pp solve. Monotonicity of `side_cfg_T_ip` is proved
(in `TD_Side_IP_Mono.thy`), so P1 is gated on well-foundedness of the TD side
worklist over a finite pp set.

P1 is gated on P5 for a generic termination proof.

**P2 (closed 2026-06-01):** Fix B — per-pp `td_analyse`, `td_analyse_collect_sound_at`
via `td_env_at_path_step_le`; `td_cfg_in_reach` removed from all theorems. See finding below (historical).

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

Instantiating `voblint_sign_sound` on this `c` is impossible: discharging
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
  formalization — Voblint's real worklist solver covers everything in
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

**Closed 2026-06-01** — Fix B implemented ([#8](https://github.com/ManuelLerchner/voblint-formalization/issues/8)):
`TD_Interface.thy`, `TD_Soundness.thy`, `Pipeline.thy`, `Constraint_System_Sound.thy`
(`post_fixpoint_sound_at`). Historical analysis above kept for thesis / meeting notes.

### P5 — type-level finiteness

See previous table (routes a/b/c). Partial-correctness thesis may keep P1 explicit.

### P4 / P7 — interval domain

Sign end-to-end proved (`side_ip_sign_analysis_sound`; carries P1 only). Interval
domain not in current tree — was in classical spine (sibling repo). Adding it
requires only a `sound_transfer` interpretation for interval transfer functions;
no architectural changes needed.

### P6 — TD total correctness

`TD_Total.thy` removed from the tree. Reintroduce only if P5 is resolved and totality is in scope.

### P8 — session hygiene

Split core vs stretch sessions when sorry-free core is policy.

### P10 — Direct_Equations

**Abandoned.** File deleted; `Voblint_Formalization` imports CFG route only.

---

## Where to start

**Session plan:** `docs/NEXT_STEPS.md`.

1. `rg -n '^\s*sorry' src/ | rg -v '\.thy~'`
2. `docs/PROOF_OVERVIEW.md` — current theorem names
3. `src/Formalization/Pipeline/Trace_IP_Analysis_Sound.thy` — `trace_ip_analysis_sound`, `reaching_global_read_sound`
4. `src/Analysis/Domains/Sign_Side_IP_Soundness.thy` — `side_ip_sign_analysis_sound`
5. Open TD hyp: P1 (`side_cfg_ip_solve_dom`) only
6. MCP-first workflow: `AGENTS.md`
