# M1 — Computed k-call-string contexts

Status: **PLANNED, not started.** Optional Goblint-faithfulness breadth. Lands on a
worktree branch off `main`; `main` stays green throughout.

> **Not the same thing (2026-07-29).** `Example_Interval_DG_CallString.thy`
> (`Voblint_Examples`) is a *different*, smaller call-string instance, built on
> the DG/`Activation_Backbone` route (`SEIDL_CONTEXT_LIFECYCLE_MIGRATION.md`
> G1/G2), not on the `CallString k`/digest/`TD_side` machinery this doc plans.
> It routes `twice`'s two calls by call site (`enterc u ctx s = u`, unbounded
> depth, no truncation, no monotonicity re-proof for a partitioned unknown
> space) and proves `activation_collect_sound` for that one program. It
> satisfies neither this doc's A0–A5 stages nor its precision/termination
> obligations (R1–R6), and does not reduce this doc's remaining scope.

Detail parent: `TRACE_BASED_FORK_MIGRATION.md` (Track A, slices A1–A5, review
obligations R1–R6). Umbrella: `TRACE_CONTEXT_ANALYSIS_MIGRATION.md` (shared
semantic layer B0–B2, target-theorem ladder T1–T12). This doc is the
self-contained migration plan; it does not restate the semantic-layer proofs, it
consumes them.

---

## 1. Goal and motivation

Produce a **computed** context-sensitive analyzer whose calling context is a
length-`k` call string, running on the vendored `TD_side` solver, and prove it
sound and *strictly* more precise than the flow-insensitive analyzer on a
call-bearing program.

Today the repo has context-sensitivity via **semantic entry-state** contexts
(Track B, done and sound). It does **not** have the textbook Goblint context —
the bounded call string — as a computed instance. The only call-string-flavoured
precision result is hand-built (`Example_Trace_Digest_Precision.thy`), not run
through the solver. M1 closes that: the most recognizable Goblint context,
end-to-end, `by eval`.

The payoff over Track B is not precision on any single program (entry-state
contexts are at least as precise) but **fidelity and monotonicity**: call strings
are value-independent, so the analysis keeps the *monotone* `TD_side` back-end and
retains `least_partial_post_solution` (optimality), which the warrowing Track B
gives up.

## 2. Relation to Goblint

Goblint solves over `(node, context)` unknowns:

- `type lv = MyCFG.node * S.C.t`, lifted by the `FromSpec` functor —
  [`src/framework/constraints.ml`](https://github.com/goblint/analyzer/blob/master/src/framework/constraints.ml).
- `LVar = VarF (S.C)`, `GVar = GVarF (S.V)` — locals keyed by context, globals by
  name.
- Call-string is one configurable `C.t`; the framework bounds it with the
  Loopfree Callstring / Context Gas lifters (`src/lifters`, [Context Gas, STTT
  2025](https://link.springer.com/content/pdf/10.1007/s10009-025-00803-3.pdf)).

M1 realizes the `C.t = k-call-string` instance with the finiteness supplied by
construction (`'d::finite` via bounded length), not by a lifter — the lifters are
M3.

**Fidelity caveat.** Goblint's *default* context hashes richer `D.t` state into
`C.t`; the pure call string is a faithful *subset*, and the richer semantic form
already exists as Track B. M1 adds the syntactic-history axis, not the whole
Goblint context menu.

## 3. Current status in the Isabelle formalization

**Reusable (done):**

| Artifact | File | Role for M1 |
| --- | --- | --- |
| `cfg_collect_ctx`, `cfg_collect_ctx_reaching_compat`, `cfg_collect_ctx_subset_flat` | `src/CFG/Collecting/CFG_Collect_Trace.thy` | context collecting semantics M1 proves soundness against |
| `context_step_refines_dg` | `src/CFG/Collecting/CFG_Collect_Trace.thy` | B2 incremental-digest bridge; instantiate for call strings |
| `digest_env_sound`, `digest_read_sound` | `src/Formalization/Pipeline/Trace_Analysis_Sound.thy` | the analyzer contract (parametric in `dg`, `cmp`) |
| `flat_env_is_digest_sound` | same | conservativity baseline (k=0 collapse target) |
| `digest_beats_flat`, `digest_env_sound_concrete` | `src/Formalization/Examples/Digest/Example_Trace_Digest_Precision.thy` | hand-built precision witness; M1 replaces "hand-built" with "computed" |
| `context_domain` locale | `src/Analysis/Generic/Solver/Context/Context_Domain.thy` | `Spec`-shaped interface; call-string is one interpretation |
| keyed generator `side_cfg_T_eff_cmp_st`, `unit_combine_tree_cmp_ctx_st` | `TD_Side_CFG.thy`, `Exec_Cmp_Bridge.thy` | the `(pp × 'c) + 'g` equation-system builder |
| finite-context executable run pattern | `Example_Finite_Sign_Context_Analysis.thy` | template for the compiled-CFG `by eval` run |
| compile pattern (`imp_prog`, `compile_prog`, CFG lemmas) | `Example_Inc_Proc.thy` | example programs Ex1/Ex2 |

The scaffolding is ~80% present: semantic layer, contract, generator, executable
context runs all exist. The missing piece is one non-trivial *call-string* context
computed through the solver.

## 4. Missing pieces

- A `CallString k` interpretation of the digest interface: `dg :: trace => 'd`
  extracting the (bounded) call string, `cmp` = prefix/equality, `'d::finite`.
- The B2 bridge specialized to k-truncation: incremental per-edge context update =
  `dg` on the whole trace (with k-truncation agreement).
- The digest-indexed equation system re-discharging the three `TD_side`
  monotonicity preconditions (`is_mono_eq` / `mono_sides` / `mono_deps`) for the
  partitioned unknown space.
- A compiled two-call (or two-caller) program with a *proved* strict-inclusion
  precision theorem (`one_callstring_separates_callers`), not a `value` printout.

## 5. Dependencies

- **Semantic layer B0–B2** (`TRACE_CONTEXT_BRIDGE_MIGRATION.md`): mostly DONE
  (`cfg_collect_ctx`, `context_step_refines_dg`). Confirm the call-string
  instance discharges B2 before A2.
- **Independent of M2 and M3.** M1 does not touch the transfer/publication
  discipline (M2) and gets finiteness by fiat (M3 replaces the fiat with lifters).
- Downstream: **M3b (Loopfree Callstring lifter) depends on M1** — it needs a
  call-string context to bound.

## 6. Risks and proof obligations

| ID | Obligation / risk | Severity | Mitigation |
| --- | --- | --- | --- |
| R1 | `solve_dom` for partitioned unknowns — inherited or new hypothesis? | Med | keep P1 as the vendor hypothesis over `(pp × 'd) + 'g`; `'d::finite` bounds the index set |
| R2 | k-truncation: incremental digest equals `dg` on the whole trace | Med | prove `context_step_refines_dg` instance with explicit truncation lemma |
| R3 | combine must **over-approximate** compatible caller partitions, not invert the push exactly at depth ≥ k | **High** | `combine_ctx` joins compatible callers; never an exact pop — the primary soundness hazard |
| R4 | `digest_env_sound` parametric in `(dg, cmp)` | Low | already parametric; confirm no hidden `'c = unit` specialization |
| R5 | precision = proved theorem, not evaluated inequality | Med | state `gamma (envd …) ⊂ gamma (env …)` as a lemma; `by eval` only the endpoints |
| S2.5 | `k = 0` reproduces the flat analyzer | Low (gate) | prove before any precision claim |

Monotonicity is *not* at risk: syntactic call strings are value-independent, so the
routing is constant in `σ` (like `named_etf`'s constant routing), unlike the
value-dependent `flag_etf` which is provably not `mono_sides`
(`flag_etf_mono_sides_unprovable … oops`).

## 7. Concrete stages (independently buildable commits)

Each stage is one green, sorry-free commit on the worktree branch.

| Stage | Commit | Content |
| --- | --- | --- |
| **A0** | `feat(ctx): CallString digest locale skeleton` | `'d` = bounded call string type (`'pname list` truncated to `k`), `finite` instance, `dg`/`cmp` signatures with `sorry` placeholders |
| **A1** | `feat(ctx): CallString interpretation of the digest interface` | `dg` extracts/truncates the call string from a trace; `cmp` = prefix-or-equal; prove `dg`/`cmp` abstract the call structure. No solver. |
| **A2** | `feat(ctx): incremental call-string transfer + B2 bridge` | `update_ctx` (push on `EA_Enter`, truncate at `k`), `combine_ctx` (join compatible callers); prove the `context_step_refines_dg` instance |
| **A3** | `feat(ctx): call-string-indexed equation system` | lift `side_cfg_T_*` to `(pp × 'd) + 'g`; re-discharge `is_mono_eq`/`mono_sides`/`mono_deps`; deliver executable `side_analyse_*_d` |
| **A4** | `feat(ctx): soundness of the computed call-string analyzer` | `context_analysis_sound ⇒ digest_env_sound` for the computed `envd`; discharge R3 combine over-approx |
| **A5g** | `test(ctx): k=0 collapses to flat` | conservativity gate `context_k0_eq_flat` (or soundness-equivalence) — **before** A5 |
| **A5** | `feat(ctx): call-string precision witness` | compiled Ex1 (`G := x` across two call sites) or Ex2 (two callers); `one_callstring_separates_callers` as a proved strict inclusion |

## 8. Deliverables and exit criteria

- **Per stage:** `isabelle build` green on the touched session, no `sorry`.
- **A1:** `CallString` locale + interpretation; `dg`/`cmp` abstraction lemmas.
- **A2:** `context_step_refines_dg` for call strings (with k-truncation lemma).
- **A3:** executable `side_analyse_*_d`; the three monotonicity lemmas.
- **A4:** `context_analysis_sound` instance ⇒ `digest_env_sound` for computed `envd`.
- **A5:** `one_callstring_separates_callers` — a **proved** `⊂`, plus the k=0 gate.
- **Track exit:** a compiled call-bearing program on which the computed
  call-string read is certified sound and strictly tighter than the
  flow-insensitive read.

## 9. Expected impact

- **Executability:** preserved. `'d::finite` + monotone system code-generates
  through `Exec_Bridge`; the witness is `by eval`.
- **Soundness:** additive. New `context_analysis_sound` instance; the flat
  analyzer remains the k=0 special case (`flat_env_is_digest_sound`). No existing
  theorem changes.
- **Precision:** strict gain on call-bearing programs where distinct call
  sites/callers were joined flow-insensitively. Bounded by k; deeper recursion
  folds into the truncated context (that is where M3's Context Gas would take
  over).

## 10. Classification

**Optional / Goblint-faithfulness breadth.** Not thesis-critical (semantic
context-sensitivity is already certified). It adds the single most recognizable
Goblint context as a computed, optimal-back-end instance. Self-contained, low
research risk, textbook.
