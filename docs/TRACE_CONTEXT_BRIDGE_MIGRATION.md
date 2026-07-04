# Migration — trace-to-context bridge (semantic layer)

> **Agent entry point:** `TRACE_CONTEXT_ANALYSIS_MIGRATION.md` (umbrella). This file
> holds B0–B2 detail only.

Status: **PARTIALLY DONE (Track B path, batch-sealed).** B0 (`alpha_ctx`,
`cfg_collect_ctx`, `context_collect_sound`) and B2 (`context_transfer` locale,
`trace_witness_ctx`, `context_step_refines_dg`, `trace_witness_ctx_last_in_cfg_collect_ctx`)
are in the repo and batch-green. B1 was not needed for Track B (post-fixpoint
induction factored through `trace_witness` + `pull_ctx` pullback instead). B3 is
done for Track B — see `SEMANTIC_CONTEXT_MIGRATION.md`. Track A (digest / k-CFA)
has not started; B2 will need a second instance for call-string digests.

KB: `wiki/research/trace-precision-direction.md`, `wiki/concepts/digests.md`.

---

## Problem statement

Three levels are often conflated:

| Level | Carrier | What the solver stores today |
| --- | --- | --- |
| 1 — traces | `pp ↦ trace set` | nothing |
| 2 — stores | `pp ↦ store set` | (via `α_last`) |
| 3 — abstract | `pp ↦ abs_state` | yes (`env v`) |

**Trace `lfp` as concrete semantics ≠ history-sensitive solver.** Precision requires
a finite history key in the fixpoint state:

```text
cfg_collect_trace : pp ↦ trace set
        │
        ├─ α_ctx / α_digest
        ▼
context collecting : (pp, c) ↦ store set
        │
        ▼
context solver : (pp, c) ↦ abs_state
```

`alpha_last_cfg_collect_trace_le` justifies **flat** soundness only. The
history-sensitive target is a **context abstraction theorem** (below).

---

## What already exists

| Artifact | File | Role |
| --- | --- | --- |
| `trace_witness`, `cfg_collect_trace` | `CFG_Collect_Trace.thy` | concrete trace semantics (inductive) |
| `trace_witness_d`, `reaching_compat` | `CFG_Collect_Trace.thy` | digest-refined traces |
| `digest_env_sound`, `digest_read_sound` | `Trace_Analysis_Sound.thy` | analyzer contract at `(pp, digest)` |
| `flat_env_is_digest_sound` | `Trace_Analysis_Sound.thy` | flat `env` is trivial `envd` |
| `digest_beats_flat` | `Example_Trace_Digest_Precision.thy` | precision witness (hand-built `envd`) |

`digest_env_sound` is already the right **solver soundness shape**, but stated over
`reaching_compat` + `alpha_last` without naming the intermediate semantics.

---

## Target definitions (CFG layer)

Add to `CFG_Collect_Trace.thy` (or sibling `CFG_Collect_Context.thy`):

```isabelle
definition alpha_ctx ::
  "(trace ⇒ 'c) ⇒ ('c ⇒ 'c ⇒ bool) ⇒ trace set ⇒ 'c ⇒ store set" where
  "alpha_ctx dg cmp T c =
     {last tr | tr. tr ∈ T ∧ cmp (dg tr) c}"

definition cfg_collect_ctx ::
  "(trace ⇒ 'c) ⇒ ('c ⇒ 'c ⇒ bool) ⇒ cfg ⇒ store set ⇒ pp ⇒ 'c ⇒ store set" where
  "cfg_collect_ctx dg cmp g S v c =
     alpha_ctx dg cmp (cfg_collect_trace g S v) c"
```

**Relationship to existing names:**

```text
reaching_compat dg cmp c g S v  =  {tr ∈ cfg_collect_trace g S v. cmp (dg tr) c}
alpha_ctx dg cmp (cfg_collect_trace g S v) c
  =  alpha_last (reaching_compat dg cmp c g S v)
```

So `digest_env_sound` rephrases as:

```text
∀ v c.  cfg_collect_ctx dg cmp g S v c  ⊆  γ (envd v c)
```

**Flat collapse** (sanity): if `cmp _ _ = True`, join over `c` recovers
`alpha_last (cfg_collect_trace …)`; if `envd v c = env v`, recover flat soundness.

---

## Target soundness theorem (pipeline layer)

After a context-indexed solver produces `env :: pp ⇒ 'c ⇒ abs_state`:

```isabelle
theorem context_analysis_sound:
  assumes post_fp: "… is_post_fixpoint … env"
  shows "cfg_collect_ctx dg cmp g S v c ⊆ γ (env v c)"
```

Specializations:

| Instance | `dg` / `cmp` | Solver source |
| --- | --- | --- |
| Flat | constant digest | today's `trace_analysis_sound` |
| k-call-string | call-string extract + prefix `cmp` | `TRACE_BASED_FORK` S3–S4 |
| Entry-state semantic | `enter#` projection | `SEMANTIC_CONTEXT_MIGRATION` S1–S2 |

The **bridge lemma** each instance needs (incremental context tracks `dg`):

```text
∀ trace step.  cmp (update_ctx (dg trace) step) (dg (trace @ step))
```

(or the combine variant for IP). This is the design crux flagged as R2/R3 in
`TRACE_BASED_FORK_MIGRATION.md` and as `enter_ctx` soundness in
`SEMANTIC_CONTEXT_MIGRATION.md`.

---

## Stages

### B0 — Context collecting semantics (small, do first)

- Add `alpha_ctx`, `cfg_collect_ctx`.
- Prove the **main compatibility lemma** with existing digest infrastructure:

```isabelle
lemma cfg_collect_ctx_reaching_compat:
  "cfg_collect_ctx dg cmp g S v c =
   alpha_last (reaching_compat dg cmp c g S v)"
```

- Further algebra lemmas:
  - `cfg_collect_ctx` monotone in trace-set refinement;
  - `cfg_collect_trace_d_subset` ⇒ context collecting only shrinks;
  - flat collapse (`cmp = (λ_ _. True)` or `envd v c = env v`).
- Repackage `digest_env_sound` as `context_collect_sound` (one-line unfold of
  `cfg_collect_ctx_reaching_compat` + `digest_env_sound_def`).

**Acceptance:** no `sorry`; no solver changes; `isabelle build` green on
`Voblint_CFG` + `Trace_Analysis_Sound`.

### B1 — Optional `lfp` characterization (proof interface only)

**Do not replace `trace_witness`.** Add a functional mirror, following the
`cfg_collect_F` / `cfg_witness` pattern in `CFG_Collect.thy`.

**Combine rule must match `trace_witness` verbatim** (this is the single
authoritative home for the compressed-combine caution; other docs point here).
In `CFG_Collect_Trace.thy` the `trace_witness.combine` conclusion is
**compressed** (callee entry store not duplicated):

```isabelle
(* trace_witness.combine — CFG_Collect_Trace.thy *)
tau @ tl rho @ [<last tau|last rho>]
```

with premise `hd rho = enter_state (last tau)`. Do **not** use `tau @ rho @ …`
unless you also change the inductive rule and re-check every `last` proof
(`trace_witness_last_in_cfg_collect`, digest combine, examples). The repo is on
the compressed form; B1 copies it.

```isabelle
definition cfg_collect_trace_F ::
  "cfg ⇒ store set ⇒ (pp ⇒ trace set) ⇒ pp ⇒ trace set" where
  "cfg_collect_trace_F g S X v =
     { [s] | s. v = cfg_entry g ∧ s ∈ S }
   ∪ { tr @ [s'] | u a tr s'.
        (u,a,v) ∈ edges g ∧ tr ∈ X u
        ∧ edge_step a (last tr) = Some s' }
   ∪ { tau @ tl rho @ [<last tau|last rho>] | c ex tau rho.
        (c,ex,v) ∈ combines g ∧ tau ∈ X c ∧ rho ∈ X ex
        ∧ hd rho = enter_state (last tau) }"

definition cfg_collect_trace_lfp where
  "cfg_collect_trace_lfp g S = lfp (cfg_collect_trace_F g S)"
```

Prove:

```isabelle
lemma cfg_collect_trace_F_mono: "mono (cfg_collect_trace_F g S)"

lemma trace_witness_iff_lfp:
  "trace_witness g S v tr ⟷ tr ∈ cfg_collect_trace_lfp g S v"
```

(or set equality `cfg_collect_trace g S = cfg_collect_trace_lfp g S`).

**Why add it:** enables standard post-fixpoint induction for B2/B3 proofs
(`cfg_collect_ctx … c ⊆ γ (env v c)` via `lfp` + abstraction homomorphism).

**Why skip it for now:** does **not** improve solver precision; adds proof bulk
(monotonicity, combine case, post-fixpoint ↔ witness). Flat soundness already
closes via `alpha_last_cfg_collect_trace_le`.

**Recommendation:** add B1 **when** proving B3 (solver soundness against
`cfg_collect_ctx`) or when the thesis argues "trace-level abstract interpretation."
Skip if the thesis only cites the inductive witness.

**Acceptance:** equivalence lemma; `cfg_collect_trace` definition unchanged;
existing theorems untouched (re-prove via alias if desired, not required).

### B2 — Incremental context refines `dg` (design crux)

Parametric locale `Context_Step` fixing:

- `dg :: trace ⇒ 'c`, `cmp :: 'c ⇒ 'c ⇒ bool`;
- `update_ctx :: 'c ⇒ edge_action ⇒ store ⇒ 'c` (or edge-indexed variant);
- soundness: incremental update simulates appending one step to a witness trace;
- combine: `combine_ctx` sound w.r.t. `trace_witness` combine rule (watch k-CFA
  truncation — R2/R3 in fork migration).

First instance: bounded k-call-string. Second: semantic entry-state (`enter_ctx`).

**Acceptance:** `context_step_refines_dg` (name TBD), no `sorry`.

### B3 — Solver soundness against `cfg_collect_ctx`

Wire B2 into the context-indexed equation system (either fork's
`(pp × 'd)` unknowns or semantic migration's `(pp + 'g) × 'c`). Prove B3's
`context_analysis_sound` (or recover `digest_env_sound` as corollary).

**Acceptance:** `'c = unit` (or `k = 0`) recovers today's flat result;
non-trivial instance proves `digest_env_sound` / `context_collect_sound`.

### B4 — Precision witness

Reuse `digest_beats_flat` template; for semantic contexts mirror in S3 of
`SEMANTIC_CONTEXT_MIGRATION.md`.

---

## Dependencies

```text
B0 ──▶ B3
B1 (optional) ──▶ B3   [proof convenience]
B2 ──▶ B3
B3 ──▶ B4

Parallel implementation tracks (share B0–B2 semantics):
  TRACE_BASED_FORK_MIGRATION  (k-call-string, mono back-end)
  SEMANTIC_CONTEXT_MIGRATION  (entry-state, warrowing back-end)
```

| Stage | Size | Axis |
| --- | --- | --- |
| B0 context collecting defs | **small** | CFG |
| B1 lfp equivalence | moderate (optional) | CFG |
| B2 incremental `dg` bridge | **large** | CFG + instance |
| B3 solver soundness | large (per track) | Analysis |
| B4 precision witness | small | Examples |

---

## What this does not do

- **Does not** make the flat solver history-sensitive by itself.
- **Does not** replace `trace_witness` (inductive rules stay the operational spec).
- **Does not** prove optimality / least abstraction of trace collecting.
- **Does not** choose between mono (fork) and warrowing (semantic) back-ends —
  that stays in the respective implementation migrations.

---

## See also

- `docs/TRACE_BASED_FORK_MIGRATION.md` — digest-indexed unknowns, k-call-string
- `docs/SEMANTIC_CONTEXT_MIGRATION.md` — entry-state contexts, warrowing
- `docs/CONTEXT_SENSITIVE_GLOBALS_MIGRATION.md` — high-level thesis framing
- `docs/thesis/trace-pivot-and-history-sensitive-globals.md` — chapter narrative
- `src/CFG/Collecting/CFG_Collect_Trace.thy` — `trace_witness`, `reaching_compat`
- `src/Formalization/Pipeline/Trace_Analysis_Sound.thy` — `digest_env_sound`
