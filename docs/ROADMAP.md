# Roadmap

**This file does not list issues, lemmas, or sorries.** Those drift. It points to the live sources of truth and records *stable* architectural directions.

---

## Source-of-truth pointers

| What you want | Where to look |
| --- | --- |
| Open work items, dependencies, status | **[GitHub Project 8](https://github.com/users/ManuelLerchner/projects/8)** |
| Active issues, labels, milestones | `gh issue list --state open` |
| Live sorry inventory | `rg -n '^\s*sorry' src/ \| rg -v '\.thy~'` |
| **Next session / week plan** | `docs/NEXT_STEPS.md` |
| All declared lemmas/theorems | `rg -n '^(lemma\|theorem) ' src/` |
| Soundness chain narrative | `docs/PROOF_OVERVIEW.md` |
| Per-stage workflow | `docs/PROOF_OVERVIEW.md` (lemma spine) + `src/*/README.md` (per-layer) |
| Catalogued repo problems (P1–P10) by file:line | `docs/OPEN_PROBLEMS.md` |
| CFG representation decision | `docs/cfg-representation.md` |
| HOL-IMP differences | `docs/HOL_IMP_COMPARISON.md` |
| Comparison to Blazy/Pichardie/Verasco | KB: `~/git/goblint-formalization-kb/wiki/concepts/blazy-2013-value-analysis.md` and `wiki/concepts/verasco.md` |

---

## Label scheme (GitHub)

| Group | Labels | Meaning |
| --- | --- | --- |
| Phase | `phase:core` / `phase:stretch` / `phase:thesis` | Where the work lives in the proof-architecture phasing |
| Type | `type:proof` / `type:refactor` / `type:docs` / `type:code-gen` | Kind of work |
| Source | `source:blazy-2013` | Inspired by Blazy et al. SAS 2013 (arXiv:1304.3596) |

Filter examples:

```bash
gh issue list --state open --label phase:core
gh issue list --state open --label source:blazy-2013
gh issue list --state open --label phase:stretch --label type:proof
```

Dependency arrows live on the issues themselves (GitHub's native `blockedBy`/`blocking`). The Project 8 Roadmap view shows them when the *Dependencies* layer is on.

---

## Stable architectural directions

Issue numbers are deliberately omitted — they go stale. The directions remain even as individual issues open, close, or get renamed.

### Core soundness chain (done in code)

Collecting spec + post-fixpoint + TD side bridge (B3–B4 in `docs/OPEN_PROBLEMS.md`) are proved.
Sign pipeline is closed end-to-end (`proc_global_side_sign_analysis` / `side_sign_analysis_sound`)
modulo one named TD hypothesis (P1: `side_cfg_solve_dom_eff`).

### Semantics and pipeline (current)

- **Spec:** `cfg_collect` (IP state) and `cfg_collect_trace` (IP trace) at every program point; `cfg_runs_to` is exit-projected sugar.
- **Canonical soundness:** `trace_analysis_sound` (no termination premise); `reaching_global_read_sound` (per-variable read).
- **Mixed-flow theorem:** `mixed_flow_analysis_sound` / `mixed_flow_analysis_optimal` for effectful TD_side equation systems.
- **Exit corollary:** `side_sign_analysis_sound` (sign domain).
- **Operational:** `pstep` in `IMP2_Proc.thy`; `cfg_runs_to` in `CFG_Collect_Runs.thy`.
- **Showcase:** `Example_Trace_Digest_Precision.thy` — digest vs. flat precision comparison.

### Trace-based analyzer fork (planned)

Full digest-partitioned analyzer (one abstract state per `(pp, digest)`), still executable on `TD_side`. The trace contract (`digest_env_sound` / `digest_read_sound`) already exists and is proved realizable by the flat collapse (`flat_env_is_digest_sound`); the fork produces a *tighter* `envd`. Approach A (digest-indexed unknowns), first instance k-call-string. Plan + slices + exit criteria: `docs/TRACE_BASED_FORK_MIGRATION.md`. Single-threaded precursor to thread-modular work.

### Domain stretch

Interval is the next instance. Octagon is the relational stretch. Both fit the existing `sound_domain` / `abstract_domain` locale chain. **Interval pipeline is the architectural template**: once instantiated, octagon and any further domains follow the same scaffold provided the `vname ⇒ 'a abs_state` pointwise lifting is adequate. For domains where it is not (e.g. octagons over DBMs), see "Two-layer split" below.

### Blazy 2013 (arXiv:1304.3596) — adopted directions

The repo's `sound_domain` locale and HOL `fun`-instance lifting already match Blazy 2013's minimalist `adom` interface and `NonRelDom.make` functor, free of charge. Four paper patterns are queued as additive extensions on the issue tracker (search label `source:blazy-2013`):

1. **Backward transformers + iterative `assume` refinement** (§5.2). Forward-only `tf_assume` cannot infer dual bounds from chained comparisons (`if (0 ≤ x ∧ x < y ∧ y < z ∧ ... ∧ v < 10)`). Adding `tf_backward_*` and a bounded forward+backward fixpoint iteration recovers tight bounds. Precision win on interval.
2. **Direct product → reduced product locales** (§3.3 + §5.3). Direct product is γ-intersection; reduced product adds a `reduction` operator. Useful once a second numerical domain is around (interval + octagon).
3. **`range` query interface** (§5.1). Separates "what is the abstract value of this expression?" from "how does this transition update the state?". Used internally by `assume`; thesis-narrative win.
4. **Decidable post-fixpoint checker** (§4 translation-validation pattern). Not needed for soundness — AFP TD is verified — but cheap to add and pedagogically valuable as a contrast point to the verified-solver approach.

Two larger refactors are queued but not committed to:

- **Two-layer split** of `num_value_domain` (scalar) from `env_domain` (environment-level). Currently collapsed via the HOL `fun`-instance. Needed if and only if relational domains require their own `env_domain` instance (octagons do; intervals do not).
- **Sparse environment representation** (`vname ⇀ 'a` with implicit-⊤ default, à la `AbTree.make`). Executability + dead-code-elimination win. Subsumes part of P9.

Out of scope: memory layer (`mem_dom`, §6) — IMP2 has no pointer/memory model; signed/unsigned reduced product — IMP2 uses ℤ; translation-validated Bourdoncle — repo's AFP TD is strictly stronger.

### Octagon / relational domains — flagship stretch

**Value.** Relational numerical abstraction (octagons à la Miné: `x − y ≤ c`, `x + y ≤ c`) is the next major precision step beyond intervals. There is **no existing Isabelle/HOL formalization of octagons in AFP**, so a clean implementation here is a publishable artifact on its own (separate AFP entry: `Octagon_Domain`) in addition to being a thesis stretch goal. The reduced product Octagon × Interval is the canonical demonstration that the repo's pipeline scaffold handles relational and non-relational domains uniformly.

> ⚠️ **This is the hardest open work item.** Realistic estimate: **4–6 weeks of focused effort**, of which roughly 2 weeks is architectural plumbing in this repo before any octagon theory is touched. Do **not** estimate this as "another domain like interval".

#### Why it is difficult

1. **Architectural mismatch with the pointwise lifting.** The repo's `'a abs_state = vname ⇒ 'a` is per-variable: every abstract state is a pointwise function from variable names to a single-variable abstract value. Sign, interval, parity, congruence — all of these fit. **Octagons do not.** A DBM (difference-bound matrix) tracks bounds on `xᵢ − xⱼ` and `xᵢ + xⱼ` for every variable pair; the natural type is **whole-state**, not per-variable. The HOL `fun :: sup` / `fun :: bot` instances that give us `sound_domain` "for free" do not apply. Either the `env_domain` interface is split into a relational variant (the principled fix; see "Two-layer split" above), or octagon ships with a bespoke `abs_state` type and a parallel pipeline plumbing path (the bypass).

2. **DBM canonical closure.** Octagon soundness depends on operating on **strongly closed** DBMs (Floyd-Warshall closure adapted for the doubled variable set used by octagons). Closure has subtle invariants — strong closure differs from regular shortest-path closure because of the `x + y` constraints — and many algorithmic shortcuts in the literature trade precision for speed in ways that need explicit soundness proofs. Closure must be re-established after every transfer function. Getting this right in Isabelle is a real proof, not a paste from a textbook.

3. **Join is non-trivial.** Unlike intervals where join is bounds-min/bounds-max, the DBM join is **pointwise max on closed forms** but the result is **not automatically closed**. So either join re-closes (cost: closure pass per join, plus the soundness of "join-then-close = sound join") or the soundness statement carries closure as an invariant on inputs (cost: every transfer fn must promise to return closed DBMs). The trade-off touches every lemma.

4. **Widening on DBMs is heuristic.** The standard widening (interval-style widening on each bound, plus a closure pass — or not, depending on whether you want stability) has several variants in the literature. Picking one and proving it sound for the chosen closure invariant adds another layer.

5. **Transfer functions are richer.** Assignment `x := y + c` updates an entire row/column of the DBM, not a single cell. Constraint-based `assume` (`x − y ≤ k`) directly refines one DBM entry but then needs closure to propagate. Backward transformers (cf. Blazy 2013 §5.2) are significantly harder than for intervals because every DBM entry potentially constrains every other — there is no "operand-local" reasoning.

6. **Reduced product with interval is mandatory.** Octagon alone misses single-variable bounds that interval catches trivially (octagon expresses `x ≤ c` only as `x − 0 ≤ c` if `0` is a tracked variable, which it usually is not). The reduced product is what makes octagon useful in practice. So the soundness story is **not** just `octagon_pipeline_sound`; it is `(octagon × interval)_pipeline_sound` with a reduction operator proved sound.

7. **No reusable Isabelle prior art.** Verasco has convex polyhedra (different structure, uses an untrusted VPL library validated a-posteriori by Farkas certificates — a different design point). HOL-IMP has none. The closest references are Miné's PhD and the pen-and-paper SAS / VMCAI literature; mechanization is from scratch.

#### Phasing

The recommended path (encoded in the GitHub DAG):

```
Interval partial-corr  →  Interval pipeline  →  Two-layer split (refactor)
                                            →  Backward transformers
                                            →  Direct product  →  Reduced product
                                                                         ↓
                                                                      Octagon
```

Skipping the two-layer split is possible (route (a) bypass), but it sets a precedent for every future relational domain (zones, polyhedra) to repeat the bespoke-plumbing pattern. The split is upfront cost amortised across all future relational work.

#### Scope decision the supervisors should make

The thesis is defensible at **two scope levels**:

- **Scope A: interval pipeline closed + Blazy-2013 precision extensions** (backward transformers, iterative `assume`, reduced product with interval × sign). Polished, finished, ~3–4 months. Octagon is acknowledged as future work with the difficulty notes above.
- **Scope B: full octagon end-to-end with reduced product**. Significantly more ambitious; ~6–8 months minimum. Strong defensibility if it lands; high risk of running over.

Both are legitimate. The choice should be explicit before the two-layer split lands, because the refactor is only worth its cost if octagon (or another relational domain) actually follows.

### Total correctness

Gated on P5 (vendored `TD_warrow_mono_term` demands `finite (UNIV :: 'pp set)`). Three routes documented in `docs/OPEN_PROBLEMS.md` §P5. Partial correctness with named TD assumptions is a defensible thesis stance.

### Thesis writeup

`docs/PROOF_OVERVIEW.md` is the prose-level pipeline-narrative source. The thesis chapter lifts from it; cross-references to `.thy` files are by file path, not by lemma name (those drift; `rg` finds them).

---

## How to keep this file current

Edit when:

- A *stable* decision changes (e.g., "we are dropping IMP2 in favour of HOL-IMP `Abs_Int2`").
- A new architectural direction enters or leaves the queue.
- A pointer above breaks.

Do **not** edit for:

- Individual issue progress (use GitHub).
- Lemma renames or sorry counts (use `rg`).
- New issues that fit an existing direction.
