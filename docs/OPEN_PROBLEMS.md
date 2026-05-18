# Open problems and handoffs

Unfinished pieces in the formalization. Source of truth for live sorries:

```bash
rg -n '^\s*sorry' src/ | rg -v '\.thy~'
```

Related: `docs/HOL_IMP_COMPARISON.md`, `docs/PROOF_PHASES.md`.

---

## Bridges in the soundness chain

```
big_step --B1--> collect --B2--> cfg_collect --B3--> gamma . env <--B4-- TD output
                                       .                                    ^
                                       .                 [B5 cfg_in_reach]--+
                                       .                 [B6 comp_fun_idem]-+
                                       .                 [B7 TD terminates]-+
                                       interval ----------[B8 widening] ----+
```

| Bridge | Statement                                                                       | Where                                                | Status                           | Drops    |
| ------ | ------------------------------------------------------------------------------- | ---------------------------------------------------- | -------------------------------- | -------- |
| B1     | `big_step (c,s) t ==> t \<in> collect c {s}`                                    | `IMP2/IMP2_Collecting.thy` (definitional)            | done                             | -        |
| B2     | `t \<in> collect c {s} <-> t \<in> cfg_collect (to_cfg c) {s} (cfg_exit ...)`   | `CFG/CFG_Collecting.thy` (`cfg_collect_exit_eq_collect`) | done                         | -        |
| B3     | `is_post_fixpoint env ==> \<forall>v. cfg_collect g {s} v \<subseteq> gamma_state (env v)` | `Equations/Constraint_System_Sound.thy:226` | done                             | -        |
| B4     | TD solver output satisfies `is_post_fixpoint`                                   | `Solver/TD_Interface.thy:425`                        | done (modulo B5/B6/B7 as hyps)   | -        |
| B5     | `cfg_in_reach (to_cfg c)` for every CFG pp                                      | not yet stated                                       | missing                          | P2       |
| B6     | `sound_domain ==> comp_fun_idem join_state`                                     | not yet stated                                       | missing                          | P3       |
| B7     | `TD_plain.solve_dom T (cfg_entry (to_cfg c))` for compiled CFG                  | requires P5 first                                    | missing                          | P1       |
| B8     | `widen_ivl` UB + wf widening chains + narrowing                                 | `Domains/Interval_Domain.thy`, `Solver/TD_Total.thy` | missing                          | P6 / P7  |

Optional, off the critical path:

| Bridge | Statement                                                          | Status                                                |
| ------ | ------------------------------------------------------------------ | ----------------------------------------------------- |
| B-alt  | AST-direct eqsys = CFG-via eqsys (`direct_rhs_eq_cfg_rhs`)         | partial (`Direct_Equations.thy`); see P10             |
| B-hol  | HOL-IMP `Abs_Int2_ivl` mapped onto our interval domain             | not started; see `docs/HOL_IMP_COMPARISON.md`         |

B1-B4 are the soundness chain and are proved. B5-B8 are what remains.
`pipeline_sound` as it stands today carries B5/B6/B7 as named assumptions.

---

## Problem catalogue

| ID  | Problem                                                                | Files                                                                  | Why it blocks                                                                                                                              | Needed for                                                                |
| --- | ---------------------------------------------------------------------- | ---------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------- |
| P1  | `TD_plain.solve_dom` is an assumption on `pipeline_sound`              | `src/Pipeline/Pipeline.thy:201`, `src/Solver/TD_Interface.thy:430`     | Theorem reads "if TD terminates on this program then the result is sound". User has to discharge solver termination per program.           | Cleaner main theorem; total correctness. Gated on P5.                     |
| P2  | `cfg_in_reach` is an assumption on `pipeline_sound`                    | `src/Pipeline/Pipeline.thy:205`                                        | Every CFG pp lies in the solver's reach-set from entry. True by construction of `to_cfg`, not proved.                                      | Drops one assumption from the main theorem.                               |
| P3  | `comp_fun_idem (ac_join cfg)` is an assumption on `pipeline_sound`     | `src/Pipeline/Pipeline.thy:200`                                        | TD interface needs join to be commutative + idempotent in the fold sense. Currently a user obligation.                                     | Drops another assumption; user only supplies `sound_domain` axioms.       |
| P4  | Interval-domain soundness sorries (5)                                  | `src/Domains/Interval_Domain.thy:119,133,139,165,182`                  | No `sound_domain` interpretation for interval -> no `pipeline_sound[OF ...]` corollary for interval. Sign is the only worked example.      | Second domain end-to-end (partial correctness).                           |
| P5  | `pp = nat` vs `TD_warrow_mono_term`'s `finite (UNIV :: 'x set)`        | `src/CFG/CFG_Def.thy:19`, `vendor/td-verification/TD_warrow.thy:3251`  | Termination locale demands type-level finiteness. `nat` is infinite even when `to_cfg c` uses finitely many of its values.                 | Generic termination claim.                                                |
| P6  | TD termination obligations sorry                                       | `src/Solver/TD_Total.thy:61,68,76,94,107,121,130,138`                  | `widening_precise` / `wf widening_chains` / `is_mono_eq` / `mono_deps` / `narrowing_le` open. No `TD_warrow_mono_term` interpretation.     | Total correctness. Gated on P5.                                           |
| P7  | Widening soundness sorries                                             | `src/Domains/Interval_Domain.thy:126,127,130`                          | `widen_ivl_ub1/ub2` and `widen_ivl_terminates` open. Blocks `abstract_domain` interpretation for interval (used only by termination).      | Interval termination track. Feeds P6.                                     |
| P8  | `ROOT` runs with `options [quick_and_dirty]`                           | `ROOT`                                                                 | Batch build "passes" while ignoring sorries in imported stretch theories. Build cannot claim sorry-free.                                   | Sorry-free build of the thesis core.                                      |
| P9  | Executable end-to-end is limited                                       | `src/Examples/Example_Sign_Analysis.thy:159`                           | `value` on the full output map only works for tiny finite domains; no code generation for interval.                                        | Running the verified analyser on a real program inside Isabelle.          |
| P10 | `Direct_Equations.thy` partially sorry                                 | `src/Equations/Direct_Equations.thy:58,62,142,186,199,239,278`         | Alternate AST->eqsys path. Not on the thesis pipeline.                                                                                     | Only if the thesis claims AST-direct = CFG-via equivalence.               |

---

## Per-problem notes

### P1 / P2 / P3 — assumptions on `pipeline_sound`

`pipeline_sound` (`Pipeline.thy:248-269`) currently carries three TD-side
assumptions:

```isabelle
assumes cfi:             "comp_fun_idem (ac_join cfg)"   -- P3
assumes td_solve_dom:    "TD_plain.solve_dom ..."        -- P1
assumes td_cfg_in_reach: "\<And>v. v \<in> reach ..."    -- P2
```

P2 is a CFG-shape lemma (every emitted pp is path-reachable from `cfg_entry`,
plus the corresponding TD reach lemma — check `vendor/td-verification/TD_plain.thy`
for prior art before re-proving).

P3 should be derivable from the `sound_domain` axioms (`join_comm`,
`join_assoc`, and idempotence). State once as
`sound_domain.join_state_comp_fun_idem` and use it inside the pipeline.

P1 is gated on P5 (the termination locale requires a finite pp type).

### P5 — type-level finiteness

Vendored locale `TD_warrow_mono_term` requires `finite (UNIV :: 'x set)`.
`pp = nat` makes that false regardless of how many nodes `to_cfg c` actually
uses, because the locale axiom is about the type's universe, not the used set.

| Route                                            | Effect on stack                                                                                                              |
| ------------------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------- |
| (a) Stack parameterised on `'pp::finite`         | Every theorem from `CFG_Def` upward gets a type parameter. `to_cfg` becomes `'pp::finite cfg`. User picks the concrete type. |
| (b) Per-program datatype generator               | Tactic that takes a `com`, emits `datatype pp_c = ...`, produces `to_cfg_fin c :: pp_c cfg`.                                 |
| (c) Rewrite vendored TD termination on set-level | Modify `vendor/td-verification/TD_warrow.thy` to take a `finite_dom :: 'x set` instead of `finite UNIV`.                     |

(c) voids the "vendored, untouched" property of the TD solver. (a) and (b) are
large refactors. For a thesis defending partial correctness, leaving P1 as an
explicit assumption is a defensible position.

### P4 / P7 — interval domain

Two halves of the same gap. P4 alone is enough for "interval as second worked
example, partial correctness". P7 is only needed if also tackling P6.

### P6 — TD total correctness

Cannot be attempted before P5: `TD_warrow_mono_term` does not type-check over
`pp = nat`.

### P8 — session hygiene

Split into two sessions: `Goblint_Formalization_Core` (no stretch, no
`quick_and_dirty`) imports IMP2/CFG/Equations/Sign/Pipeline only;
`Goblint_Formalization_Stretch` keeps the current behaviour for interval /
direct / total.

### P10 — `Direct_Equations`

Quarantine candidate: alternate AST -> eqsys design from before the CFG path
was settled. Either finish the equivalence theorems or drop from `ROOT`
imports.

---

## Where to start

1. Re-run `rg -n '^\s*sorry' src/ | rg -v '\.thy~'`; counts above may have drifted.
2. Read `docs/HOL_IMP_COMPARISON.md` for how this differs from textbook AI.
3. Open `src/Pipeline/Pipeline.thy:193` (`pipeline_invariant_sound`) and
   `Pipeline.thy:248` (`pipeline_sound`) — these are the main theorems; the
   listed assumptions are P1/P2/P3.
4. P3 is the cheapest concrete win. P8 is the cheapest cosmetic win.
5. Follow `CLAUDE.md` workflow: MCP-first (I/Q `write_file` + `explore`),
   `isabelle build` only to confirm. ASCII-only in `.thy`.
