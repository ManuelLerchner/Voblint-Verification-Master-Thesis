<!-- markdownlint-disable-file MD025 -->

# Migration: array syntax for the source language

Status: **PLANNED, NOT STARTED** 2026-06-13. Follow-on to
`docs/AFP_IMP2_REBASE_MIGRATION.md`. The bridge to AFP IMP2 is built
array-*ready* but the source language is scalar-only; this migration adds array
variables + indexing so IMP2's array algorithms (e.g. the tutorial `array-sum`)
become expressible, runnable, and analyzable.

## Why now

`docs/AFP_IMP2_REBASE_MIGRATION.md` Phase 3 anchored soundness to AFP IMP2's
standard big-step semantics, and `src/IMP2/IMP2_VCG_Example.thy` shows the loop
`vcg_cs` ⊕ `backward_sim` composition working end to end. But that example is
**scalar**: our expressions only ever read array index `0`
(`to_imp2_aexp (V x) = Vidx x (N 0)`), so a program touching `a[l]` for a
runtime index `l` cannot be written in `IMP2_Proc.com` at all. That is a
language-scope boundary, not a proof gap. Closing it is the precondition for any
array analysis.

## The crux decision: store representation

Everything downstream is determined by one choice. Current state:

```
store = vname => int                 (* src/IMP2/IMP2_Syntax.thy *)
```

IMP2's state is `vname => int => int` (every variable is an array). The scalar
store embeds as a constant array (`embed s = (%x i. s x)`) and projects back at
index 0 (`proj0 S = (%x. S x 0)`). Three options:

| Option | Store | Bridge | Pipeline ripple | Precision ceiling |
| --- | --- | --- | --- | --- |
| **A. Full array store** | `vname => int => int` (= IMP2's) | `embed`/`proj0` collapse to (near) identity | **Large** — every `store` use in semantics/CFG/domains/solver/soundness re-typed | array-native |
| **B. Two-namespace store** | scalars `vname => int` + arrays `vname => int => int` | bridge merges the two halves into IMP2's unified state | medium — scalar proofs mostly untouched, arrays added in parallel | array-native, but split bookkeeping |
| **C. Array-smashing only** | option A or B store, but domain keeps one abstract cell per array | as A/B | medium | index-insensitive (e.g. "all cells ≥ 0", not `a[i]`-precise) |

Recommendation: **A for the concrete layer, C then a stretch to index-sensitive
for the abstract layer.** Option A makes the bridge nearly an isomorphism on the
array fragment (the cleanest correspondence and the strongest soundness
statement), at the cost of a one-time re-typing sweep. Option B's split-state
bookkeeping leaks into every layer and into the bridge's `combine_states`; not
worth it. The abstract-domain precision is a separate, later dial (C first).

## Phases (bottom-up, each batch-green before the next)

### Phase A1 - concrete layer + bridge

`src/IMP2/IMP2_Syntax.thy`, `IMP2_SmallStep.thy`, `IMP2_Proc.thy`,
`IMP2_Bridge.thy`:

- `store = vname => int => int`.
- `aexp`: add `Vidx vname aexp` (read `s x (aval i s)`); the scalar `V x`
  becomes sugar for `Vidx x (N 0)` (keeps existing programs working).
- `com`: add `ArrAssign x i a` (`x[i] := a`), and optionally `ArrCpy`/`Clear`
  to match IMP2. `aval`/`bval`/`pstep` extended for the array cases.
- Bridge: `to_imp2_aexp (Vidx x a) = Syntax.Vidx x (to_imp2_aexp a)`;
  `embed`/`proj0` become identity (or thin wrappers) once the store types match,
  so `aval_to_imp2_sim`/`bval_to_imp2_sim` and `backward_sim` carry over with the
  array cases added to each induction.

Watch: `backward_sim`'s `AssignIdx` case currently hard-codes index `0`
(`proj0_Assign`); generalise to an arbitrary computed index. The `proj0`-based
invariant relaxes to plain equality of states once the store types coincide.

Exit: array programs are expressible; `backward_sim` re-proved for the array
fragment; `IMP2_VCG_Example`-style array program (e.g. `array-sum`) verifiable
with `vcg_cs` and pulled back via `backward_sim`. **No abstract analysis yet.**

### Phase A2 - array-smashing abstract domain

`src/Analysis/Domains/`:

- One abstract value per array variable (index-insensitive "smashing"):
  `gamma_arr (a#) = { f. ALL i. f i : gamma (a#) }`.
- Transfer functions: `x[i] := a` weak-updates (joins) the array's abstract
  cell; `Vidx x i` reads it. Reuse the existing scalar lattice per cell.
- Soundness: the smashing concretisation is a Galois connection over the new
  store; slot into the existing `Constraint_System` / `cfg_collect` soundness
  with the array transfer-fn cases.

Exit: sound array analysis; provable facts are index-insensitive (e.g. "every
element of `a` is non-negative"), not `a[i]`-relational.

### Phase A3 (stretch) - index-sensitive domain

Array segmentation (Cousot-Cousot-Logozzo 2011) or the Blazy-2013-style
partitioning already on the backlog. Enables per-index / relational facts
(`a[0..<l]` summed). This is research-grade and orthogonal to A1/A2; keep it on
the issue tracker, not the critical path.

## Risks

- **Re-typing sweep (A1).** Changing `store` touches every theory that mentions
  it. Do it as a single mechanical pass with the build as the gate; do not mix
  with semantic changes. Expect churn in CFG/Equations/Solver signatures even
  though their *logic* is unchanged.
- **`V x` sugar.** Keeping `V x = Vidx x (N 0)` preserves existing scalar
  programs and proofs; if instead `V` is dropped, every existing example and the
  scalar `IMP2_VCG_Example` must be rewritten. Keep the sugar.
- **Smashing imprecision (A2).** Tutorial `array-sum` proves a per-index sum;
  array-smashing cannot. Set expectations: A2 buys *soundness* for array
  programs, not the precision of IMP2's VCG. Precision is A3.
- **Scope creep.** A1+A2 is the deliverable for "array-ready analysis". A3 is a
  separate research effort; do not let it block A1/A2.

## First slice

Phase A1 only: re-type `store`, add `Vidx` + `ArrAssign`, re-prove the bridge
agreement lemmas and `backward_sim` array cases, then port a scalar
`IMP2_VCG_Example` to an array variant. Gate on a green `Voblint_IMP2` build
before touching the analysis layers.
