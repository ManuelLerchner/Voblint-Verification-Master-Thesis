# P1 `solve_dom` — total-correctness route analysis

Status: **closed as non-goal** (GitHub #14). Discharging `solve_dom` so
soundness becomes unconditional is a declared non-goal (`docs/NON_GOALS.md`).
This route map stays as a reference: it records why the last TD hypothesis
resists a quick discharge and what each route would cost, in case a later
phase revisits the scope decision (`docs/THESIS_SCOPE_MEMO.md`).

## What P1 is

The end-to-end endpoints (`unit_dg_analysis`'s `source_sound` and
`result_node_sound_of_terminates` in `Unit_DG_Analysis.thy`, and the routed
`*_of_terminates` theorems in `Routed_Live_Keys.thy`) carry one solver
hypothesis:

```isabelle
assumes solves: "terminates ugs p"
```

`terminates` is `solve_dom` at the program's root query (vendored
`TD_plain.thy:67`: the solver's `iterate_dom` reaches a fixpoint). A caller
derives it from the executable solver returning (`terminates_of_solve_c`), so
for a concrete program it is discharged by evaluation. It is an **operational termination obligation on the vendored
solver**, not a gap in the soundness proofs: the endpoints already give "if the
solver returns at `x`, its result is sound". P1 would close the "if" for every
program.

## Why it does not fall out

The vendored termination theorem
`TD_warrow_mono_term.TD_warrow_terminating` discharges `solve_dom`, but its
locale requires (vendored `Basics.thy:756`):

```isabelle
finite_vars: "finite (UNIV :: 'x set)"
```

i.e. the **type** of unknowns must be finite. In this repository unknowns are
program points paired with a context, plus global keys; `pp = cfg_node`
(`CFG_Def.thy`) numbers statements by `nat`, so the type is infinite. The CFG has only
finitely many *reachable* points, but that is a finite *set*, not a finite
*type* — so the locale cannot be instantiated as-is. This is **P5**, and P1 is
gated on it.

## Routes

### (a) Finite program-point type — principled

Build the CFG and constraint system over a finite type of (reachable) program
points instead of `cfg_node`, then instantiate `TD_warrow_mono_term` directly.

- **Pro:** reuses the vendored termination theorem wholesale; gives a clean
  generic total-correctness statement.
- **Con:** retypes `pp` across `CFG_Def`, the collecting layers, the equation
  generator and the solver bridge, and must re-establish every executable
  enumeration of nodes and edges over the new type. Multi-week, touches the
  spine.
- Building block (not yet proved): `finite (edges g) \<Longrightarrow>` the set of
  reachable points is finite — needed to justify carving out the finite subtype.

### (b) Direct `solve_dom` on the reachable subgraph — bespoke

Prove `solve_dom` for the generated equation system directly, by a well-founded
argument over the finite reachable subgraph rooted at the query, bypassing the
global `finite UNIV`.

- **Pro:** no spine retype; stays in `cfg_node`.
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
finite-subtype refactor is reusable infrastructure.
