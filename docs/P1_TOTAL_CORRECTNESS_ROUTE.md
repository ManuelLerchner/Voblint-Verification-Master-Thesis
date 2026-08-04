# P1 `solve_dom` — total-correctness route analysis

Status: **closed as non-goal** (GitHub #14). Discharging `solve_dom` so
soundness becomes unconditional is a declared non-goal (`docs/NON_GOALS.md`).
This route map stays as a reference: it records why the last TD hypothesis
resists a quick discharge and what each route would cost, in case a later
phase revisits the scope decision (`docs/THESIS_SCOPE_MEMO.md`).

## What P1 is

The main pipeline theorems (`pipeline_invariant_sound`, `pipeline_sound_path`,
`goblint_sign_sound`, `goblint_interval_sound`) carry one explicit TD hypothesis:

```isabelle
assumes td_solve_dom: "\<And>v. TD_plain.solve_dom (make_rhs_tree ...) v"   -- P1
```

`solve_dom x` (vendored `TD_plain.thy:67`) asserts the solver's `iterate_dom`
reaches a fixpoint when rooted at `x`. It is an **operational termination
obligation on the vendored solver**, not a gap in the soundness proofs:
`td_analyse_collect_sound_at` already gives "if the solver terminates at `v`, its
result is sound at `v`". P1 closes the "if".

## Why it does not fall out

The vendored termination theorem
`TD_warrow_mono_term.TD_warrow_terminating` discharges `solve_dom`, but its
locale requires (vendored `Basics.thy:756`):

```isabelle
finite_vars: "finite (UNIV :: 'x set)"
```

i.e. the **type** of unknowns must be finite. In this repository unknowns are
program points, `pp = nat` (`CFG_Def.thy`), an infinite type. The CFG has only
finitely many *reachable* points, but that is a finite *set*, not a finite
*type* — so the locale cannot be instantiated as-is. This is **P5**, and P1 is
gated on it.

## Routes

### (a) Finite program-point type — principled

Build the CFG and constraint system over a finite type of (reachable) program
points instead of `nat`, then instantiate `TD_warrow_mono_term` directly.

- **Pro:** reuses the vendored termination theorem wholesale; gives a clean
  generic total-correctness statement.
- **Con:** retypes `pp` across `CFG_Def`, the path/collecting layers, and the
  solver bridge. `pp = nat` is currently load-bearing: `cfg_edges_list` uses
  `sorted_list_of_set (edges g)` and the derived `predecessor_list` drives the TD
  core (`rhs_eq_fold_predecessor_list`). A finite-type retype must re-establish
  the linear order and the predecessor machinery. Multi-week, touches the spine.
- Building block (not yet proved): `finite (edges g) \<Longrightarrow>` the set of
  reachable points is finite — needed to justify carving out the finite subtype.

### (b) Direct `solve_dom` on the reachable subgraph — bespoke

Prove `solve_dom (make_rhs_tree ...) v` directly by a well-founded argument over
the finite reachable subgraph rooted at `v`, bypassing the global `finite UNIV`.

- **Pro:** no spine retype; stays in `nat`.
- **Con:** re-derives, outside the vendored locale, the monotone-progress /
  destabilization-bounded argument the vendored proof already makes. Effectively
  re-proving solver termination for the specific RHS shape. High effort, fragile
  against vendored solver changes.

### (c) Keep P1 explicit — partial correctness (recommended for the thesis)

State `solve_dom` as a named, documented hypothesis and prove **partial
correctness**: *if* the solver terminates at each queried point, the result is
sound. This is the current state and a defensible thesis stance — the soundness
contribution is independent of solver termination, and the vendored solver is the
adjacent verified-solver work (Tilscher et al., NASA FM 2026), not this thesis's
object of study.

- **Pro:** zero additional risk; the explicit hypothesis is honest and small.
- **Con:** the headline theorem is conditional. Mitigated by stating P1
  prominently and pointing at the vendored termination result it would discharge.

## Recommendation

**Route (c) for the thesis**, with route (a) named as the principled path to total
correctness if a later phase wants it. Routes (a) and (b) are both genuine
multi-week efforts; neither is "polish". Do not attempt a partial (a)/(b) and
leave a half-retyped spine — that is worse than a clean explicit hypothesis.

If total correctness becomes a hard requirement, route (a) is preferred: it
reuses the vendored termination theorem rather than re-proving it, and the
finite-subtype refactor is reusable infrastructure (it also unblocks executable
end-to-end runs, P9).
