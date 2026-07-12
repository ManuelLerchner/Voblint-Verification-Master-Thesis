# Next steps

Short-term work plan (updated 2026-06). Issues: `gh issue list --state open`.
Catalogue: `docs/OPEN_PROBLEMS.md`. Architecture: `docs/ROADMAP.md`.

---

## Where we are

**Done**

- Full IP soundness chain: IMP2 with procedures -> interprocedural CFG -> `cfg_collect` -> side-effecting TD solver -> `trace_analysis_sound` / `reaching_global_read_sound`.
- Sign and Interval domain end-to-end on the standalone effectful path: `side_sign_analysis_sound`, `side_ivl_analysis_sound`, executable `sign_exec_sound_collecting` via `Exec_Bridge`.
- **Effectful spine is the sole spine** (2026-06-18): all pure-only solver files (`TD_Side_IP_Soundness`, `TD_Side_IP_Interface`, `TD_Side_IP_Bounds`, `TD_Side_IP_Mono`) deleted; `side_cfg_T_ip_eff` is the only equation system; shim mono in `TD_Side_Eff_Soundness`, transport in `Exec_Bridge` via direct fold simulation.
- **0 sorries** in `src/`.
- **`sound_domain`/`abstract_domain` → type classes** (2026-06-23): `locale sound_domain` and `locale abstract_domain` replaced by `class sound_domain` and `class abstract_domain`; `gamma` is now a single class operation; `gamma_state`/`widen_state` are global definitions with `⟦_⟧` notation; Sign and Interval instantiated via `instantiation` blocks; `backward_domain` drops the `γ` parameter; solver theorems require only `'a::sound_domain` constraints. `Update_rules.N` shadow clash fixed via `hide_const (open)` in `Abstract_Domain`, `Sign_Domain`, `Interval_Domain`.
- Trace semantics (`cfg_collect_trace`) + projection (`alpha_last`) + soundness morphism.
- **Goblint-style context-indexed unknowns** — the `(node, context)` mechanism is modeled and verified, not pending. `context_domain` locale (`Context_Domain.thy`) mirrors Goblint's `Spec` D/G/C interface; `cfg_collect_ctx` + `context_analysis_sound`/`digest_env_sound`/`digest_read_sound` are the context collecting semantics and soundness contract; the semantic entry-state instance is **sound and strictly precise and computed** (`semantic_entry_store_ctx_analysis_sound`, `entry_store_context_precision_witness`). See "Context-sensitivity status" below.
- AFP IMP2 bridge + VCG co-existence example.
- Classical (intra) spine extracted to sibling repo `voblint-formalization-classical`.

**Explicit hypotheses (out of scope by design)**

| ID | Assumption | Stance |
| --- | --- | --- |
| P1 | `side_cfg_solve_dom_eff … (cfg_exit …)` | Vendor's obligation. `TD_side` is vendored from `td-verification`; its termination is not our proof obligation. Our result is conditional soundness: *if* the solver terminates, the abstract result is sound. See `docs/NON_GOALS.md`. |

---

## Now — start here

**Primary: [#17 — Thesis writing](https://github.com/ManuelLerchner/voblint-formalization/issues/17)**

The IP soundness chain is complete. `side_cfg_solve_dom` (P1) is explicitly
out of scope — a vendor hypothesis, not ours. Write up.

**Alternatives**

- **NONDET_HAVOC** — add `x := random()` to the language; first nondeterministic construct, demonstrates pipeline extensibility. See `docs/NONDET_HAVOC_MIGRATION.md`.
- **Digest fork S1 (Track A call-strings)** — *optional breadth, POSTPONE.* Adds a computed k-call-string context alongside the entry-state context that already exists. Not a prerequisite for the core claim; see "Context-sensitivity status".

---

## Next goals (short horizon)

| Priority | Goal | Payoff |
| --- | --- | --- |
| 1 | **Thesis writing** | Core chain proved; write-up is the blocker |
| 2 | NONDET_HAVOC | Language extension; demonstrates pipeline extensibility |
| 3 | Digest fork S1 (Track A call-strings) | Faithfulness breadth, not a blocker — context-sensitivity already modeled |
| 4 | Interval domain | Second numeric domain; same scaffold |

**Defer unless scope expands**

- Octagon domain — 4–6 weeks min; see `docs/ROADMAP.md` for difficulty notes.
- Session split (Core / Stretch) — needs import refactor.

---

## Context-sensitivity status (Goblint `(node, context)`)

**Modeled and verified.** Goblint solves over `(node, context)` unknowns
(`type lv = MyCFG.node * S.C.t`, `FromSpec` functor in
[`constraints.ml`](https://github.com/goblint/analyzer/blob/master/src/framework/constraints.ml));
context is selected *call-only* via `Spec.context : man -> fundec -> D.t -> C.t`,
and globals are a separate flow-insensitive `V.t -> G.t` side store. This
formalization already captures that mechanism:

- **Unknown space** `(pp + 'g) × 'c` fed to the vendored `TD_side` (= `FromSpec`).
- **`context_domain` locale** (`Context_Domain.thy`) mirrors the `Spec` D/G/C
  interface: `start_context`/`prep`/`ctx_sel`/`entdg`/`cmp`, call-only routing.
- **Sound + strictly precise + computed** semantic entry-state instance:
  `semantic_entry_store_ctx_analysis_sound` (`TD_Side_Eff_Ctx_Sound.thy`),
  `entry_store_context_precision_witness` (`Example_Entry_Store_Context_Precision.thy`),
  plus a finite value-derived context (`Example_Finite_Sign_Context_Analysis.thy`).
- **Contract**: `cfg_collect_ctx` + `context_analysis_sound` /
  `digest_env_sound` / `digest_read_sound`.

**Sufficient for the core thesis claim.** The verified pipeline already has a
Goblint-shaped, sound, strictly-more-precise context layer. The remaining items
are **faithfulness polish**, not blockers:

- **D/G/C boundary + `R_read` discipline** — feed `ctx_sel` a pre-loss routing
  read instead of the joined `side_env_cmp` view; dissolves the documented `fctx`
  negative result. Real research; see `ROUTE_A7_GOBLINT_CONTEXT_DESIGN_STUDY.md`.
- **Computed k-call-string (Track A)** — optional breadth; the textbook context
  scheme, currently only hand-built (`Example_Trace_Digest_Precision.thy`). Plan
  in `TRACE_BASED_FORK_MIGRATION.md` (A1–A5).
- **Context-bounding lifters** (Context Gas / Loopfree Callstring / Context
  Widening) — future work; our finiteness is `'c::finite` + the P1 `solve_dom`
  hypothesis. See the [Context Gas paper](https://link.springer.com/content/pdf/10.1007/s10009-025-00803-3.pdf).

**Recommendation: POSTPONE.** Not the next required implementation — the
necessary layer exists. Land the thesis first; if one more faithful increment is
wanted afterward, Track A call-strings is the smallest.

> **Thesis-facing:** The formalization already captures Goblint-style
> context-indexed unknowns. Further work would improve breadth and fidelity, but
> is not required for the core verified pipeline.

---

## Suggested week

```text
Day 1–2:  Thesis prose (IP soundness + trace semantics chapter) from docs/PROOF_OVERVIEW.md
Parallel:  P1 (solve_dom total correctness) — closes last TD hypothesis
Later:     Interval domain OR digest precision — one of, not both
```

---

## Thesis milestone (next "done" slice)

> IP trace soundness with **only `side_cfg_solve_dom`** as explicit hypothesis,
> plus thesis chapter covering `trace_analysis_sound` / `reaching_global_read_sound`.

---

## References

- `docs/OPEN_PROBLEMS.md` — P1, bridge diagram
- `docs/PROOF_PHASES.md` — sorry inventory, completed milestones
- [GitHub Project 8](https://github.com/users/ManuelLerchner/projects/8) — board view
