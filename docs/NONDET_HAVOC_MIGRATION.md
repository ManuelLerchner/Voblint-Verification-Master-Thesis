# Nondeterministic Havoc (`random()`) Migration

Status: **PLANNED** (not started). Authored 2026-06-19.

## Goal

Add a nondeterministic integer source to the source language so a single
incoming store can leave a program point as an unbounded set of stores. Surface
syntax `x := random()`; one store entering the havoc edge yields `{ s(x := v) |
v }`. This is the first genuinely nondeterministic construct in the pipeline —
every existing edge is a deterministic function.

We model `random()`, **not** `input()`: each call is independently arbitrary,
with no ordering or consumption. That removes any oracle/stream state and keeps
`store = vname => int` unchanged across every layer.

## Decisions on record

- **`random()` over `input()`.** Stateless havoc, no input stream, so no
  `store`-type surgery. `input()` would tempt an oracle-stream design
  (`store x int stream`) that threads through every layer.
- **Atomic assignment `x := random()`, not a `random()` aexp leaf.** A
  nondeterministic subexpression would break `aval :: aexp => store => int`
  (`src/IMP2/IMP2_Expr.thy`) as a total function, poisoning every
  expression-evaluation proof. The nondeterministic unit is the whole RHS:
  a dedicated statement `Havoc vname` / edge action `EA_Havoc vname`.
  `aval` / `bval` stay total and deterministic.
- **Genuine set-valued semantics, not pre-chosen oracle.** The trace layer's
  `edge_step :: edge_action => store => store option` becomes set-valued so the
  fan-out happens at the havoc node, matching the intended semantics.
- **`pstep_deterministic` weakens to havoc-free programs.** It is used in
  exactly one place (`src/IMP2/IMP2_Proc.thy`, local lemma `n`), so the blast
  radius is small.

## Where determinism is baked in today

| Layer | File | Construct | Status |
| --- | --- | --- | --- |
| Source semantics | `src/IMP2/IMP2_Proc.thy:43` | `pstep` Assign -> `s(x := aval a s)`; `pstep_deterministic` :74 | needs relational `Havoc` rule |
| Expr | `src/IMP2/IMP2_Expr.thy:18` | `aval :: aexp => store => int` | unchanged (atomic decision) |
| CFG action | `src/CFG/CFG_Def.thy:38` | `datatype edge_action` | add `EA_Havoc` |
| Concrete collecting | `src/CFG/Collecting/CFG_Collect_Edges.thy:12` | `edge_collect :: edge_action => store set => store set` | already set-valued; add one clause |
| Trace | `src/CFG/Collecting/CFG_Collect_Trace.thy:27` | `edge_step :: ... => store option` | refactor to `store set` (main proof cost) |
| Abstract | `src/Analysis/Domains/Sign_Exec.thy:57` | `sign_tf_st` per-action transfer | `EA_Havoc x -> top` |

The store-set collecting layer (`edge_collect`) is **already** set-valued, so it
expresses fan-out structurally today. The only layer that structurally cannot
fan out is the trace layer (`edge_step` is a function) — that is the real work.

## Migration slices (dependency order)

### Slice 1 — base language (plumbing)

- `src/IMP2/IMP2_Proc.thy`: add `com` constructor `Havoc vname`. Add relational
  `pstep` rule `Havoc: pstep Pi (Havoc x, s, frs) (SKIP, s(x := v), frs)` for all
  `v` (introduces the first nondeterministic `pstep` rule). Add
  `inductive_cases HavocSE`.
- Restrict `pstep_deterministic` to a `havoc_free :: com => bool` predicate;
  repair local lemma `n`.

### Slice 2 — CFG action threading (mechanical)

- `src/CFG/CFG_Def.thy:38`: add `EA_Havoc vname`; re-derive `countable`.
- Add the missing clause in every theory that matches exhaustively on
  `edge_action` (15 files): `CFG_GraphViz` (pretty-print `x := random()`),
  `CFG_Prune`, `Exec_CFG`, `IMP2_Proc_to_CFG`, the collecting theories, the
  analysis transfers, the examples. Each is a single new case.
- `src/CFG/IMP2_Proc_to_CFG.thy`: compile `Havoc x` -> `(n, EA_Havoc x, n+1)`.

### Slice 3 — concrete collecting (mechanical)

- `src/CFG/Collecting/CFG_Collect_Edges.thy:12`:
  `edge_collect (EA_Havoc x) S = { s(x := v) | s v. True }`.
- Re-check `edge_collect_mono`, `edge_collect_empty_set`.

### Slice 4 — trace layer (main proof work; do in isolation)

- `src/CFG/Collecting/CFG_Collect_Trace.thy`:
  - `edge_step :: edge_action => store => store set` (drop `option`; `None`
    becomes `{}`, a deterministic step becomes a singleton, `EA_Havoc x s = {
    s(x := v) | v }`).
  - `edges_trace :: ... => store => trace set` folding over the step set: one
    start store -> the set of all traces produced by every havoc resolution.
  - Repair `edge_collect_single`, `lift` / `alpha_last`
    (`alpha_last (cfg_collect_trace g S v) = cfg_collect_paths g S v`),
    `edges_trace_global_frame` and its corollary.

### Slice 5 — IP collecting + adequacy

- `src/CFG/Collecting/CFG_Collect_IP*.thy`: thread `EA_Havoc` through
  `cfg_collect_ip` / `cfg_collect_trace_ip` and the `pstep` adequacy bridge
  (`CFG_Collect_IP_Adeq`). The relational `Havoc` `pstep` rule must match the
  `EA_Havoc` collecting fan-out.

### Slice 6 — abstract transfer + soundness

- `src/Analysis/Domains/Sign_Exec.thy:57`:
  `sign_tf_st (EA_Havoc x) s = update_st s x STop`. Prove the soundness /
  commutation case (`gamma_sign STop = UNIV`, so `{ s(x:=v) | v } <=
  gamma (update top)`).
- Mirror the new case in `Constraint_System`, `Constraint_System_Sound`,
  `TD_Side_CFG`.

### Slice 7 — showcase example

See below. Lands in `src/Formalization/Examples/`.

Slices 1-3 build green with no observable fan-out beyond collecting; slice 4 is
the dedicated proof slice; 5-6 follow existing per-action patterns.

## Showcase example: absolute value of a random input

The point of the example: the analyzer proves a **universal** property over an
infinite set of traces (`y >= 0` for every random draw) — exactly what abstract
interpretation buys over concrete trace enumeration. It exercises all three new
behaviours at once: havoc (`STop`), assume-edge narrowing, and a sound join.

```
x := random();        // x : STop          (havoc -> top)
if (x > 0) {
  y := x;             // assume x > 0  =>  x : SPos,  y : SPos
} else {
  y := 0 - x;         // assume x <= 0 =>  0 - x >= 0,  y : SNonNeg
}
// join: y : SPos  join  SNonNeg  =  SNonNeg
// => analyzer certifies  y >= 0  for ALL random inputs
```

On the 7-element sign lattice (`SBot SNeg SNonPos SZero SNonNeg SPos STop`) the
join lands exactly on `SNonNeg`, so the post-fixpoint at the merge point
soundly states `y >= 0`. The havoc'd `x` stays `STop`; precision is recovered
on `y` purely through the assume edges. A concrete, trace-by-trace checker
cannot establish this (the trace set is infinite); the analyzer does it in one
abstract pass.

Stretch (interprocedural variant, once slices 1-6 land): havoc a global, pass
it through a parameterless procedure that clamps it, and certify the global is
`SNonNeg` after the call — showcasing havoc across the IP boundary.

## Open risks

- **Slice 4 projection proofs.** `lift` / `alpha_last` currently rely on
  `edge_step` being a function; the `option -> set` refactor is the one place a
  one-line repair will not suffice. Budget this as a standalone slice.
- **Exhaustiveness churn.** Adding an `edge_action` constructor forces a new
  case in ~15 theories. Mechanical, but each must build before slice 4.
- **Determinism callers.** Confirm nothing downstream of `pstep_deterministic`
  silently assumed totality of `edge_step` beyond the one known caller.
