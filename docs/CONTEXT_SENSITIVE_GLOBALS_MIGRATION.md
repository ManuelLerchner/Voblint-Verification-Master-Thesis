# Migration — context-sensitive (history-indexed) globals

Status: **PROPOSED.** High-level project plan, not a step list. Makes the trace
foundation *load-bearing* by adding a context dimension to globals — the thesis's
innovative core. Discussed and judged feasible (2026-06-23).

KB: `wiki/research/trace-precision-direction.md`, `wiki/concepts/reduced-cardinal-power.md`,
open questions OQ-30/OQ-32/OQ-33 (GitHub #44/#46/#47).

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

1. **Keystone correctness (OQ-32 / #46).** Package the existing per-pp + global
   soundness into a single `mixed_flow_analysis_sound` theorem (FS locals + FI
   globals), with the monotonicity precondition stated explicitly so it excludes
   the non-monotone conditional routing (`flag_etf`). Baseline before adding
   precision.

2. **Context dimension.** Introduce the context-indexed unknown (`pp × 'd`,
   globals `gname × 'd`) and pick one concrete finite context — call-string `k`
   or branch-history. Define the digest function and compatibility relation.

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
