# Migration — context-sensitive (history-indexed) globals

Status: **IN PROGRESS.** High-level project plan, not a step list. Makes the trace
foundation *load-bearing* by adding a context dimension to globals — the thesis's
innovative core. Discussed and judged feasible (2026-06-23). Phase 1 landed
(`mixed_flow_analysis_sound`, OQ-32, 2026-06-24).

KB: `wiki/research/trace-precision-direction.md`, `wiki/concepts/reduced-cardinal-power.md`,
`wiki/research/toxic-trash-preliminaries-vs-repo.md`, `wiki/concepts/update-rules.md`,
open questions OQ-30/OQ-32/OQ-33 (GitHub #44/#46/#47).

## Grounding: this is the PLDI 2025 §2 context axis

Stemmler et al. (PLDI 2025, *Taking Out the Toxic Trash*) §2 is the same
side-effecting constraint system this repo already mechanizes: unknowns `pp + 'g`
(= their `G ⊎ L`), `strategy_tree` RHS producing a local `Answer` + global `Side`
contributions (= their `[e,c]^♯ : (L→D)×(G→D) → D × (G→D)`), solved by the vendored
`TD_side` (= their solver). The one §2 feature the repo lacks is exactly this
migration's target: **calling contexts** `c∈C`, where locals are `(v,c)` and
context-sensitive globals are `(st_p,c)`. Their *contexts-as-globals* encoding maps
onto the existing `'g::finite` named-global machinery — see "Context dimension"
below. (Their actual contribution, *update rules* / per-origin widening, is a
separate, larger follow-on tracked by OQ-34 / `update-rules`; not this plan.)

---

## Why

The trace collecting semantics (`cfg_collect_trace`) is the proof foundation, but
the analyzer is proved against the state-based `cfg_collect`; traces enter only
via `alpha_last`, so the trace structure buys nothing in the soundness argument.
Globals are analyzed **flow-insensitively** (one unknown per global name, all
contributions joined), which is the coarsest part of the analysis.

This project recovers the lost precision the *right* way: index globals by a
finite **context** (a digest of the reaching trace). That is where the trace base
finally does work, and it upgrades the honest claim from "trace-based foundation"
to "history-sensitive analysis."

## What this is NOT

- **Not** a trace-valued domain (Approach A: `gamma :: 'b ⇒ trace set`, new
  lattice/transfers). That stays future work — see `TRACE_VALUED_DOMAIN_MIGRATION.md`.
- **Not** a solver change. `TD_side` is parametric in the unknown type;
  `(node, context)` unknowns are how context-sensitivity is normally done.

This is **Approach B**: change the *unknown space* (`pp → pp × 'd`), keep the
value domain, `gamma`, and transfer functions untouched.

## Foundation already in place

- `digest_env_sound`, `digest_read_sound`, `cfg_collect_trace_d`, `reaching_compat`
  (`Trace_Analysis_Sound.thy`) — the contract for a history-indexed env.
- `flat_env_is_digest_sound` — the trivial (constant-context) instance, proving
  the contract is realizable with no gap.
- `Example_Trace_Digest_Precision.thy` — a hand-built witness that a digest read
  is strictly tighter than the flat read.

~80% of the scaffolding exists. The missing piece is *one non-trivial context
computed through the real solver*.

## Phases (high level)

1. **Keystone correctness (OQ-32 / #46). DONE (2026-06-24).** The per-pp + global
   soundness is packaged into `mixed_flow_analysis_sound` (FS locals + FI globals),
   with the monotonicity precondition stated explicitly so it excludes the
   non-monotone conditional routing (`flag_etf`). `mixed_flow_analysis_optimal`
   additionally yields `least_part_post_solution` under `threefold_mono` +
   `cone_compatible_etf`. Baseline before adding precision.

2. **Context dimension.** Introduce the context-indexed unknown (`pp × 'd`,
   globals `gname × 'd`) and pick one concrete finite context — call-string `k`
   or branch-history. Define the digest function and compatibility relation.

   **Reuse the named-global machinery (PLDI §2 contexts-as-globals).** The cheapest
   realization sets `'g = pname × ctx` with `ctx` finite (bounded call-strings) and
   routes the procedure-entry contribution to slot `(p,c)` via the existing
   `route_combine` / `Side` path in `Sign_Named_Global_Eff.thy`. `'g::finite`
   *forces* the finite context set that length-`k` call-strings provide. The more
   faithful variant additionally changes the local unknown `pp → pp × ctx`.

   **Monotonicity is the gate — and the repo already documents the failure.**
   `flag_etf` (routing *conditional on an abstract value*) is proved *not*
   `mono_sides` (`flag_etf_mono_sides_unprovable … oops`): as `σ` grows the routed
   slot can flip. The identical hazard hits **value-based / functional contexts**.
   **Syntactic call-string contexts are value-independent ⇒ monotone** (like
   `named_etf`'s constant routing) and discharge the three `TD_side` preconditions
   from the generic per-tree lemmas. → Do bounded call-string contexts first;
   defer value-based contexts (need a monotone reformulation or extra machinery).

3. **Route through the solver.** Run the analysis over the context-indexed
   unknowns via the existing `side_analyse_eff` (no solver modification), and
   discharge `digest_env_sound` for the chosen context.

4. **Certify precision.** On a program with procedure calls, prove the
   context-indexed global read is *strictly* tighter than the flow-insensitive
   read — turning the toy witness into a result over the real pipeline.

5. **Theory + write-up (OQ-33 / #47).** Frame the construction as a **reduced
   cardinal power** `A → D` (Cousot 1979; Giacobazzi–Ranzato 1999) over a finite
   trace abstraction; at the finite limit this is verified trace partitioning.

## Out of scope / future

- Trace-property value domain (Approach A).
- `TD_side` precision lemmas / three-fold-monotonicity checker (OQ-31 / #45).
- Schwarz per-origin (write-side) globals comparison (OQ-34 / #48).

## Done when

`mixed_flow_analysis_sound` holds; a non-trivial context-indexed analysis runs
through `side_analyse_eff` and is certified sound *and* strictly more precise than
the flow-insensitive read on a call-bearing program; the reduced-cardinal-power
framing is written.
