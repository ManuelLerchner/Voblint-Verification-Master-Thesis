# Migration — ghost instrumentation and assertion checking (Track C)

Status: **FUTURE / PLANNED.** Executable validation layer on top of trace/context
semantics — **not** a replacement for `TRACE_CONTEXT_ANALYSIS_MIGRATION.md`.
Makes Level-A observables visible as ordinary program checks and validates that a
**computed** context-indexed analyzer proves assertions the flat analyzer cannot.

**Depends on:** `TRACE_CONTEXT_ANALYSIS_MIGRATION.md` B0 (minimum); B3 on at least
one track for payoff **D6** (`ghost_validation_payoff`). Action-labelled traces
(M3.5 Slice 1) for write-site ghosts (Ex2, last-writer).

| Related doc | Role |
| --- | --- |
| `TRACE_CONTEXT_ANALYSIS_MIGRATION.md` | declarative semantics + context solver (Tracks A/B) |
| `TRACE_CONTEXT_BRIDGE_MIGRATION.md` | `cfg_collect_ctx`, Level A/B spine (§2.1) |
| `Example_Trace_Digest_Precision.thy` | declarative precision witness (Ex0) |
| `IMP2_VCG_Example.thy` | precedent for executable interoperability |

KB: `wiki/concepts/digests.md`; thesis stretch axis (see `docs/THESIS_SCOPE_MEMO.md`).

**Agent prompt (Track C):** After `TRACE_CONTEXT` B3, implement `GHOST_INSTRUMENTATION`
I0→I1→I3 (Phase 1). Phase 2 payoff = `ghost_validation_payoff` on Ex5 with
**computed** `analyse_ctx`, not hand `envd`. G1: `cmp`/γ for abstract ghosts;
equality only for exact manual last-writer.

---

## 1. Goal

Make trace-derived semantic facts **testable** in Goblint style:

```text
trace-derived fact  →  ghost instrumentation  →  abstract interpretation  →  __goblint_check proven
```

Trace semantics can express e.g. `last_writer(tr, g) = W1`. C-level assertions only
talk about values (`g == 1`). Ghost variables bridge the gap:

```c
g = 1;
__ghost_lw_g = W1;
// ...
if (__ghost_lw_g == W1) { __goblint_check(g == 1); }
```

The analyzer runs on the instrumented program; soundness theorems link proven checks
back to **original** program properties (via non-interference + tracking).

---

## 2. Two phases (do not conflate)

| Phase | Purpose | Ghost updates | Payoff |
| --- | --- | --- | --- |
| **Phase 1 — Spec witness** | Explain Level-A observables | **Manual** in source | G0, G1, semantic link to `last_write_collect` |
| **Phase 2 — Analyzer validation** | Test computed analysis | **Generated** from B2 `update_ctx` | **D6:** `ghost_validation_payoff` |

Phase 1 alone is **pedagogy** (re-states declarative theorems operationally).
Phase 2 is the **validation** contribution — same instrumented program, two analyzers.

Do **not** claim the thesis RQ is reopened by Phase 1; Phase 2 is stretch after
`context_analysis_sound` lands.

---

## 3. Mapping to Level A / Level B

From `TRACE_CONTEXT_ANALYSIS_MIGRATION.md` §2.1:

```text
Level A observable (last_writer, call_stack, …)
        │
        ▼  encode in store
Ghost variables (__ghost_lw_g, __ghost_call_ctx, …)
        │
        ▼  incremental update (manual → generated update_ctx)
Level B digest dg  tracked by ghost updates
        │
        ▼
cfg_collect_ctx / context_analysis_sound  (declarative)
        │
        ▼
checks_proven env  (operational)
```

| Trace observable | Ghost variable | Level |
| --- | --- | --- |
| Last writer of `g` | `__ghost_lw_g` | A (+ write-pp encoding) |
| Call-string id | `__ghost_call_ctx` | B (k-CFA) |
| Abstract entry-state id | `__ghost_entry_ctx` | B (semantic) |
| Branch/path id | `__ghost_path` | A/B |
| Taint source | `__ghost_taint_x` | A |

---

## 4. Soundness obligations

### G0 — Ghost non-interference (mandatory)

Ghost instrumentation must not change real program behaviour.

```isabelle
theorem ghost_noninterference:
  "project_real_traces (cfg_collect_trace instrumented_g S v)
   ⊆ cfg_collect_trace original_g (project_real_states S) v"
```

Informally: erase ghost fields from stores/traces → recover original collecting
semantics. Without G0, checks apply to the wrong program.

### G1 — Ghost tracking (links ghosts to Level A)

Ghost store values **encode** the digest; they need not be equal to `encode (dg tr)`
for abstract/finite digests. Use the same compatibility relation as
`reaching_compat` / `cfg_collect_ctx`:

**General (abstract / finite digest):**

```isabelle
theorem ghost_tracks_digest:
  "trace_witness instrumented_g S v tr
   ⟹ cmp (decode_ghost (ghost_digest (last tr))) (dg tr)"
```

Equivalently (γ-shaped): the concrete digest on the trace is contained in the
ghost variable's concretization:

```isabelle
theorem ghost_tracks_digest_gamma:
  "… ⟹ dg tr ∈ γghost (ghost_digest (last tr))"
```

Here `ghost_digest` projects ghost fields from the store; `γghost` is the sign/interval
lift of finite context ids; `cmp` is the same relation used in `trace_witness_d`.

**Exact (manual last-writer with write-pp constants):**

Use **equality** only when the ghost encodes an exact observable (Phase 1 manual
instrumentation):

```isabelle
theorem ghost_last_writer_tracks_trace_exact:
  "… ⟹ get_ghost_lw (last tr) g = encode_pp (last_writer tr g)"
```

**Phase 1:** prove exact tracking for manual last-writer; `cmp`/γ tracking for
call-string / entry-state ghosts.
**Phase 2:** prove **generated** updates satisfy the same obligation as B2
`context_step_refines_dg` (incremental ghost refines whole-trace `dg`).

### G2 — Check soundness (two theorems)

**G2a — Specification (Phase 1):**

```isabelle
theorem ghost_check_sound_spec:
  assumes "checks_proven env"
  assumes "ghost_tracks_digest …"
  assumes "ghost_noninterference …"
  shows "trace_property_holds original_program"
```

**G2b — Analyzer validation (Phase 2):**

```isabelle
theorem ghost_check_validates_analyzer:
  assumes "context_analysis_sound … envd"
  assumes "checks_proven (analyse_instrumented …)"
  shows "…"  (* links to cfg_collect_ctx / digest_read_sound *)
```

Checks prove **sufficiency** (analyzer over-approximates enough), not necessity.

### G3 — Generic check soundness

```isabelle
theorem checks_proven_sound:
  assumes "analysis_sound g S env"
  assumes "checks_proven env"
  shows "all_runtime_checks_hold g S"
```

`checks_proven env ⟺ ∀ check_pp. ∀ s ∈ γ(env check_pp). bval (check_condition check_pp) s`.

---

## 5. Pipeline

```text
Original program
        │
        ▼
Ghost instrumentation (manual → generated)
        │
        ▼
compile_prog → CFG
        │
        ▼
Abstract interpretation (flat OR context-indexed)
        │
        ▼
checks_proven env ?
        │
        ▼
G0 + G1 + G2 → original program property
```

---

## 6. Stages

### I0 — Ghost syntax and convention

- Reserved names: `__ghost_*` (or explicit `is_ghost` metadata on `vname`).
- Real projection: `project_real_store`, `project_real_states`.
- Ghost constants: `LW_G_W1`, `CTX_C1`, etc.

**Acceptance:** ghosts in IMP2 stores; projection ignores them; builds green.

### I1 — Check semantics (`__goblint_check`)

Before ghosts — derisk the check layer alone.

- Encode `__goblint_check(b)` as distinguished CFG point or `EA_Assume` marker.
- `checks_at g`, `check_condition v`, `checks_proven env`.
- Prove `checks_proven_sound` for one trivial assert (no ghosts).

**Acceptance:** `checks_proven_sound`; one non-ghost example passes.

### I2 — Manual ghost examples (Phase 1)

No automatic instrumenter. Hand-written programs in IMP2 notation (cf.
`Example_Inc_Proc.thy`).

**Acceptance:** parse, compile, analyse, extract checks.

### I3 — Last-writer ghost layer

Per global write at site `W`:

```c
g = e;
__ghost_lw_g = W;
```

**Acceptance:** `ghost_noninterference`; `ghost_last_writer_tracks_trace_exact` (on
action traces when available); Ex1–Ex3 check theorems.

### I4 — Context/digest ghosts (Phase 1 + link to Track A/B)

```c
__ghost_call_ctx = push_call(__ghost_call_ctx, CALLSITE);
__ghost_entry_ctx = encode_entry(abstract_state);
```

**Acceptance:** `ghost_tracks_digest` for one finite `dg`; `k=0` / unit collapses
to flat.

### I5 — Phase 2 payoff — flat vs context on same program

On instrumented Ex4/Ex5/Ex6, with **computed** `analyse_ctx` / `side_analyse_*_d`
(Track A/B B3 — not hand-built `envd`):

```isabelle
definition nonvacuous_checks where
  "nonvacuous_checks env check_pts ⟷
     (∀v ∈ check_pts. env v ≠ bot)"

theorem ghost_validation_payoff:
  "checks_proven (analyse_ctx ex5)
   ∧ ¬ checks_proven (analyse_flat ex5)
   ∧ nonvacuous_checks (analyse_ctx ex5) {check_W1, check_W2}"
```

This is the executable payoff: context analyzer proves guarded checks the flat
analyzer cannot, and guards are **reachable** (not vacuous — see D5, R4).

Per-guard reachability lemma (deliverable, not only risk mitigation):

```isabelle
theorem ghost_guard_reachable:
  "env check_W1 ≠ bot ∧ env check_W2 ≠ bot"
```

Prove for each Ex4/Ex5/Ex6 guard of interest before claiming D5.

### I6 — Automatic instrumentation (optional)

```text
program → instrument(program, update_ctx) → instrumented_program
```

Generated ghost updates = same `update_ctx` as B2 (`context_step_refines_dg`).
Structural proof that I3 manual patterns are instances.

**Acceptance:** generated Ex1–Ex3 match manual; G1 follows from B2.

---

## 7. Example programs

Cross-link: declarative twins in `TRACE_CONTEXT_ANALYSIS_MIGRATION.md` §11 (Ex0–Ex5).

### Ex1 — Branch last-writer

```c
if (nondet()) { g = 1; __ghost_lw_g = W1; }
else           { g = 2; __ghost_lw_g = W2; }

if (__ghost_lw_g == W1) { __goblint_check(g == 1); }
if (__ghost_lw_g == W2) { __goblint_check(g == 2); }
__goblint_check(g == 1 || g == 2);
```

**Semantic:** `last_write_collect(g, read) = {W1, W2}`. Flat: `g ∈ {1,2}` only.

**Target:** `src/Formalization/Examples/Example_Ghost_Last_Writer.thy`

---

### Ex2 — Same value, different provenance (canonical slide)

```c
if (nondet()) { g = 1; __ghost_lw_g = W1; }
else           { g = 1; __ghost_lw_g = W2; }

__goblint_check(g == 1);   /* flat proves */
if (__ghost_lw_g == W1) { __goblint_check(g == 1); }
if (__ghost_lw_g == W2) { __goblint_check(g == 1); }
```

**Point:** flat cannot distinguish provenance; `last_write_collect = {W1,W2}`.

---

### Ex3 — Interprocedural last-writer

```c
void a() { g = 10; __ghost_lw_g = WA; }
void b() { g = 20; __ghost_lw_g = WB; }
/* main calls a or b; guarded checks at read */
```

**Theorems:** `ex3_checks_proven`; links to `cfg_collect_ctx` per writer id.

---

### Ex4 — Call-context ghosts (↔ context migration Ex1–Ex2)

```c
void f(int x) {
  if (__ghost_call_ctx == C1) { __goblint_check(x == 0); }
  if (__ghost_call_ctx == C2) { __goblint_check(x == 1); }
  g = x;
}
```

**Phase 2:** The flat analyzer is **not** expected to prove guarded checks unless it
tracks the **correlation** between `__ghost_call_ctx` and `x`. A flow-insensitive
join on `x` alone loses that correlation even if `__ghost_call_ctx` appears in the
store — the issue is missing context indexing, not path splitting per se.
Context-indexed / `side_analyse_d` analysis keeps `(pp, ctx)` apart and should
prove both guards; flat `analyse` should fail (D5).

---

### Ex5 — Product: call ctx × last-writer (↔ Ex5 product digest)

Same write site `W_SET`, different call contexts — last-writer alone joins.

**Phase 2 target for D5:** `ghost_validation_payoff` on Ex5 — product ctx proves
both guards; flat fails; `ghost_guard_reachable` for each guard.

---

### Ex6 — Semantic entry-state ghost (↔ context migration Ex3)

`__ghost_entry_ctx = ENTRY_X0` / `ENTRY_X1` at call; proves `x == 0` / `x == 1` in `f`
where 1-CFA would still join.

---

## 8. Proof deliverables

| ID | Theorem | Phase |
| --- | --- | --- |
| D1 | `checks_proven_sound` | I1 |
| D2 | `ghost_noninterference` | I3 |
| D3a | `ghost_last_writer_tracks_trace_exact` | I3 (exact) |
| D3b | `ghost_tracks_digest` / `ghost_tracks_digest_gamma` (`cmp`/γ) | I4 |
| D4 | `ex1_checks_proven`, `ex3_checks_proven`, … | I2–I4 |
| D5 | `ghost_guard_reachable` (per Ex4/Ex5 guard) | I5 |
| D6 | `ghost_validation_payoff` (computed analyzer) | I5 |
| D7 | `history_sensitive_checks_and_precise` (capstone, optional) | I5 |

**D6 — executable payoff (preferred final shape):**

```isabelle
theorem ghost_validation_payoff:
  "checks_proven (analyse_ctx ex5)
   ∧ ¬ checks_proven (analyse_flat ex5)
   ∧ nonvacuous_checks (analyse_ctx ex5) interesting_check_points"
```

**D5 — anti-cheating (guards not vacuous):**

```isabelle
theorem ghost_guard_reachable:
  "env check_W1 ≠ bot ∧ env check_W2 ≠ bot"
```

Required for each guarded check cited in D6; listed separately so vacuity cannot
be overlooked (R4).

Capstone (optional):

```isabelle
theorem history_sensitive_checks_and_precise:
  "ghost_validation_payoff ex5
   ∧ links_to cfg_collect_ctx …"
```

---

## 9. Risks

| ID | Risk | Mitigation |
| --- | --- | --- |
| R1 | Hand ghosts make checks too easy | Phase 2 + generated `update_ctx`; state spec vs validation |
| R2 | No non-interference | G0 mandatory before precision claims |
| R3 | Domain cannot prove equalities | Sign/constants first; interval; no relational checks early |
| R4 | Guarded checks vacuous (ctx unreachable) | **D5** `ghost_guard_reachable`; part of **D6** `nonvacuous_checks` |
| R5 | Checks = sufficiency only | Same soundness direction as rest of pipeline |
| R6 | Scope creep vs closed RQ | Track C = stretch; declarative chain remains primary |

---

## 10. Dependencies and order

```text
TRACE_CONTEXT B0
        │
        ├─ I0, I1 (checks only — can start early)
        │
TRACE_CONTEXT B3 (one track)
        │
        ├─ I5, D5–D6 (`ghost_guard_reachable` + `ghost_validation_payoff`)
        │
M3.5 action traces
        │
        └─ I3 last-writer write-pp (full Ex2 story)

Recommended:
  I0 → I1 → I2 (Ex1 simple) → I3 + G0/G1 → I4
  → wait for B3 → I5 + D5 + D6
  → I6 optional
```

---

## 11. Out of scope

- Full Goblint assertion front-end / SV-COMP harness.
- Proving checks are **necessary** (only sufficiency).
- Ghost layer without declarative `context_analysis_sound` (Phase 2).
- Relational / octagon checks until domain exists.
- Replacing `digest_env_sound` proofs — Track C **complements**, not substitutes.

---

## 12. See also

- `docs/TRACE_CONTEXT_ANALYSIS_MIGRATION.md` — Tracks A/B, Level A/B, Ex0–Ex5
- `docs/SEIDL_TRACE_MIGRATION_HANDOFF.md` — M3.5 action traces for write sites
- `docs/NON_GOALS.md` — `solve_dom` assumed; no optimality
- `src/Formalization/Pipeline/Trace_Analysis_Sound.thy` — `digest_read_sound`
- `src/VIMP/IMP2_VCG_Example.thy` — executable validation precedent
