# Keyed context generator — framed `EA_Enter`, filtered from the intra fold

Historical note: the `TD_Side_Eff_Ctx_Sound` / `side_env_ctx` path discussed in this plan has been deleted. Shared helpers now live in `TD_Side_Eff_Ctx_Shared`.

Status: **DONE.** Authored + executed 2026-07-01. `Voblint_Formalization`
batch-green, no sorry, ASCII gate clean. Touches the keyed-global context
generator (`side_cfg_T_eff_cmp` / `_st`), the `sound_effectful_transfer` locale,
and the sign instance + two context examples.

This is a redesign, not a defect fix: it changes how call-enter flow enters the
context-sensitive equation system, and adds a new transfer-contract obligation
that every future domain must discharge.

## Problem

The keyed context generator (`side_cfg_T_eff_cmp`, `TD_Side_Eff_Cmp_Gen.thy`)
builds each context slot `(v, c)` by folding the abstract transfer over the CFG
**predecessors** of `v`, relabelling locals to the context copy `(w, c)` and
routing globals to the keyed slot `gkey c`. Procedure entries are ordinary CFG
nodes with an incoming `EA_Enter` edge, so the fold treated the enter edge like
any other predecessor.

Two consequences, both bad:

1. **Duplicated interprocedural flow.** `EA_Enter` flow reaches a callee-entry
   node *both* through the intra predecessor fold *and* through the `combine`
   edge that a caller uses to seed the callee. The same call is encoded twice.

2. **Precision pollution.** The intra fold reads the caller's abstract state
   under the *callee's* context key. In the finite sign-context example
   (`Example_Finite_Sign_Context_Analysis.thy`) this joins the two activations
   of `f` — `GH := G` under `G = SZero` and under `G = SPos` — into a single
   `SNonNeg` slot. The keyed context type is finite and distinct per call site,
   yet the enter-fold merged the callee slots anyway.

The obvious fix — drop `EA_Enter` from the predecessor fold — **breaks
soundness on its own.** `side_cfg_T_eff_cmp_collect_sound` discharges
`post_fixpoint_sound_at_eff` (`TD_Side_Eff_Sound.thy`), whose `step_le`
obligation quantifies over **every** edge, enter included (the collecting
semantics threads `EA_Enter` via `edge_collect EA_Enter S = enter_state` S`).
Remove enter from the fold and the per-edge bound`side_cfg_T_eff_cmp_edge_le`
loses its only proof route (`memtree`: the edge tree is a member of the fold).
Nothing bounds the callee-entry node.

## Observation

`enter_state` (`VIMP_Globals.thy`) has a stronger semantic property than a
generic edge transfer:

```
enter_state s = (λn. if is_global n then s n else 0)
```

Entering a procedure **resets locals to a fresh frame and preserves only
globals.** The abstract enter transfer inherits this shape. For sign
(`enter_sign`, `Sign_Domain.thy`):

```
enter_sign σ = (λx. if is_global x then σ x else STop)
```

So the reassembled enter output factors as a **context-independent fresh local
frame joined with the globals**:

```
etf_full (etf_enter etf u) σ  ≤  fresh_frame ⊔ glob_env σ
```

The old `sound_effectful_transfer` locale gives only the *lower* (soundness)
bound `etf_sound_enter` (`enter_state s ∈ γ(…)`). It never states this *upper*
bound. That upper bound is exactly what lets us discharge a filtered enter edge
from a fixed seed instead of from the fold.

## Solution

Four coordinated changes.

1. **New contract — `sound_effectful_transfer_framed`** (`Constraint_System.thy`).
   Extends `sound_effectful_transfer` with a `fresh_frame` parameter and the
   upper bound

   ```
   etf_enter_framed_le:
     inr_slot_locals_bot σ ⟶ inl_slot_globals_bot σ ⟶
       etf_full (etf_enter etf u) σ ≤ fresh_frame ⊔ glob_env σ
   ```

   Companion invariant `inl_slot_globals_bot` (dual of the existing
   `inr_slot_locals_bot`): local unknowns carry `⊥` in their global components —
   true of the generator's solutions because every edge tree ends in a
   `restrict_local` answer. It absorbs the caller's (bot) global passthrough in
   the enter frame.

2. **Filter enter + seed a fresh frame** (`side_cfg_T_eff_cmp`,
   `TD_Side_Eff_Cmp_Gen.thy`; mirrored in `side_cfg_T_eff_cmp_st`,
   `Exec_Cmp_Bridge.thy`). The intra fold now runs over
   `non_enter_predecessor_list` (`CFG_Def.thy`), and frame-entry nodes seed
   `fresh_frame` into `acc0`:

   ```
   acc0 = (if v = cfg_entry g then bot0 ⊔ restrict_local s0 else bot0)
          ⊔ (if is_frame_entry g v then fresh_frame else ⊥)
   ```

   Callee-entry inflow now comes only from the `combine` edge (globals) plus the
   fresh-frame seed (locals).

3. **Split enter / non-enter soundness** (`TD_Side_Eff_Cmp_Gen.thy`).
   `side_cfg_T_eff_cmp_edge_le` gains an `a ≠ EA_Enter` premise (proof unchanged
   otherwise — the filtered fold still contains every non-enter edge). New
   `side_cfg_T_eff_cmp_enter_le` handles the enter edge from the framed contract:
   the frame-entry seed places `fresh_frame ≤ σ(Inl(v, ctx))`, the framed bound
   caps the enter output, and the preserved globals land in the keyed slot.
   `side_cfg_T_eff_cmp_collect_sound` case-splits on the edge action and feeds
   the two lemmas into `post_fixpoint_sound_at_eff`.

4. **Discharge the contract per domain.** Sign: `fresh_frame_sign` +
   `sign_sound_etf_unit_framed` (`Sign_Side_Soundness.thy`). Interval does not
   use the keyed generator, so it needs nothing.

## Consequences

- **Cleaner generator.** Call flow has exactly one encoding: `combine` for the
  interprocedural edge, the fresh-frame seed for the callee's locals. The intra
  fold is purely intra.

- **Better proof decomposition.** Enter and non-enter edges are separate lemmas
  with separate justifications (framed contract vs. fold membership), instead of
  one bound straining to cover both. The soundness of dropping the enter edge is
  now a *stated obligation* (`etf_enter_framed_le`), not an implicit hope.

- **Executable precision restored.** `Example_Finite_Sign_Context_Analysis.thy`
  now proves, by `eval`, the separated result the finite context type always
  deserved:

  | slot | before | after |
  | --- | --- | --- |
  | `Inr GZero` `GH` | `SNonNeg` | **`SZero`** |
  | `Inr GPos` `GH` | `SNonNeg` | **`SPos`** |
  | join-all `GH` | `SNonNeg` | `SNonNeg` |

  The `sign st` keyed run (`Exec_Sign_Cmp_Keyed_Gen_Run.thy`) improves too: with
  a seeding combine (`kgen_combine_st`) the pure `G = SZero` context is now
  precise (`SZero`, was `SNonNeg`). Its second activation still merges to
  `SNonNeg` — not a soundness gap, but because that run keys on the
  *flow-insensitive* global (`restrict_global_st` of the joined caller), so its
  context itself is `SNonNeg`. Per-call-site separation is exactly what the
  finite-context example demonstrates; the `st` run documents the contrast.

- **Future domains only instantiate the framed locale.** Any domain that wants
  to ride the keyed context generator proves one lemma —
  `sound_effectful_transfer_framed etf fresh_frame` — for its enter transfer.
  For a domain whose enter resets locals to a constant top-of-frame and keeps
  globals (the normal shape), `fresh_frame` is the constant local frame and the
  bound is a one-line case split on `is_global`.

## A subtlety worth recording

Callee-entry globals must come from **somewhere** once the enter edge is
filtered. "Excluded enter flow is subsumed by combine handling" holds only for
combines that explicitly seed the callee context —
`unit_combine_tree_cmp_ctx_st` (finite example) and `kgen_combine_st` both emit
`Side callee_ctx (restrict_global caller)`. A non-seeding combine would starve
the callee (every global reads `⊥`). This is a real coupling: **filtering enter
is sound at the generator level unconditionally, but only *useful* when paired
with a seeding combine.** The generator soundness theorem does not depend on the
combine seeding (it uses the conservative keyed combine shape); the executable
precision does.

## Files

- `src/Analysis/Generic/Equations/Constraint_System.thy` — `inl_slot_globals_bot`,
  `sound_effectful_transfer_framed`.
- `src/Analysis/Generic/Solver/TD_Side_Eff_Cmp_Gen.thy` — filtered fold + seed,
  enter/non-enter split, re-threaded `collect_sound`.
- `src/Analysis/Generic/Solver/Exec_Cmp_Bridge.thy` — executable mirror.
- `src/Analysis/Generic/Solver/Context/Goblint/Read/Support/TD_Side_Eff_Ctx_Shared.thy` —
  `inl_slot_globals_bot_ctx`.
- `src/Analysis/Instances/Sign/Sign_Side_Soundness.thy` — `fresh_frame_sign`,
  `sign_sound_etf_unit_framed`.
- `src/Analysis/Instances/Sign/Exec_Sign_Cmp_Keyed_Gen_Run.thy` — seeding combine,
  refreshed witnesses.
- `src/Formalization/Examples/Example_Finite_Sign_Context_Analysis.thy` — precise
  witnesses.
