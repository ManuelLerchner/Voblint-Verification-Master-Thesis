<!-- markdownlint-disable-file MD025 -->

# Migration: rebase soundness onto AFP IMP2 (one-way bridge)

Status: **PLANNED** 2026-06-12. Implements part 2 of
`docs/AFP_IMP2_REUSE_DECISION.md`. Not started.

## Goal

State the analyzer's soundness against AFP IMP2's *standard* concrete semantics
instead of our bespoke `aval`/`bval`/small-step. We keep our structural,
executable `aexp`/`bexp` for the analyzer; we add a **one-way bridge** into IMP2
and prove our semantics agrees with IMP2's along it.

Direction is strict: structural -> IMP2. We never read IMP2's reflected
`int => int => int` operators back, so the analyzer stays executable (see the
executability rationale in `AFP_IMP2_REUSE_DECISION.md`).

## What this buys (and what it does not)

| Buys | Does not buy |
| --- | --- |
| Soundness vs a recognized, AFP-blessed semantics | Any dedup - the expression layer is ~30 lines either way |
| Array-*readiness*: IMP2's state and `Vidx` are array-native | Array *analysis* - the abstract domain, `Vidx` transfer fns, and their soundness are net-new regardless of IMP2 |
| Additive growth toward arrays (one constructor + one clause per side) | A drop-in replacement for our domains/CFG/solver - those are untouched |

## The type mismatch (grounded)

Ours (`src/IMP2/IMP2_Syntax.thy`, `IMP2_SmallStep.thy`):

```
store = vname => int                                  -- scalar
aexp  = BaseN AExp.aexp | Plus | Minus | Times        -- structural, Nipkow leaves
bexp  = BaseB BExp.bexp | Not | And | Or | Less | Eq
aval :: aexp => store => int
bval :: bexp => store => bool
```

IMP2 (`~/afp/thys/IMP2/basic/Syntax.thy`, `Semantics.thy`):

```
pval = int   val = int => pval   state = vname => val   -- every var is an array
aexp = N int | Vidx vname aexp | Unop (int=>int) | Binop (int=>int=>int)
bexp = Bc bool | Not bexp | BBinop (bool=>bool=>bool) | Cmpop (int=>int=>bool)
aval :: aexp => state => pval
bval :: bexp => state => bool
```

Two structural gaps to bridge:

1. **Operators**: our tags `Plus/Minus/Times/Less/Eq/And/Or` -> IMP2's reflected
   `Binop (+)`, `Cmpop (<)`, `BBinop (&)`, etc. Forward only; trivial.
2. **State**: our scalar `vname => int` -> IMP2's array `vname => (int => int)`.
   Embed a scalar as an index-agnostic constant array. Our expressions never
   index, so the array dimension is inert.

## Plan (three layers, bottom-up)

### Phase 1 - expressions + state (small, do first to de-risk)

New theory `src/IMP2/IMP2_Bridge.thy`:

```
fun to_imp2_aexp :: "aexp => IMP2.aexp"      -- recurse; helper for Nipkow BaseN subtree
fun to_imp2_bexp :: "bexp => IMP2.bexp"
definition embed :: "store => IMP2.state"     -- embed s = (%x i. s x)

lemma aval_to_imp2: "aval e s = IMP2.aval (to_imp2_aexp e) (embed s)"
lemma bval_to_imp2: "bval b s = IMP2.bval (to_imp2_bexp b) (embed s)"
```

Watch items:

- `BaseN` wraps a whole Nipkow `AExp.aexp` (with its own `Plus`), so
  `to_imp2_aexp` needs an inner `AExp.aexp => IMP2.aexp` helper handling
  `N/V/Plus`. Same for `BaseB`.
- Our `V x` (= `BaseN (AExp.V x)`) maps to `Vidx x (N idx0)`. Confirm IMP2's
  default scalar index (`Syntax.thy` "Default Array Index", line ~124) and reuse
  that constant rather than hardcoding `0`.
- `embed` makes the array constant, so the chosen index never matters; the
  agreement proofs should go through by structural induction + `simp`.

Exit: both agreement lemmas proved, no `sorry`, batch-green.

### Phase 2 - commands

`to_imp2_com :: com => IMP2.com` (`src/IMP2/IMP2_Proc.thy` `com`, `frame = store`).
Map our command constructors to IMP2's. Lift `embed` through assignments and
control flow. Surface a per-command agreement (assignment updates one variable's
array at the default index).

### Phase 3 - small-step / collecting simulation (the bulk)

Show our small-step (or `cfg_collect`) simulates IMP2's semantics under
`to_imp2_com` / `embed`, then re-state the top-level soundness theorem against
IMP2's semantics. This is where the real proof effort sits; expect helper lemmas
on `embed` commuting with state updates.

Exit: the headline soundness theorem reads "sound w.r.t. AFP IMP2", batch-green.

## Build infrastructure

`ROOT` parent is `HOL-IMP`; it pulls `TD` + `Dijkstra_Shortest_Path`. The bridge
adds a dependency on the AFP `IMP2` session. Add it to the session imports and
pass `-d ~/afp/thys` (already in the build command). Heap refresh after the
`ROOT` change.

## Risks

- **Default-index handling.** If IMP2's scalar convention is not a clean
  constant, `embed` and the `V` clause get fiddly. Verify in Phase 1 before
  building on it.
- **Nipkow leaf recursion.** `BaseN`/`BaseB` wrap full Nipkow subtrees; the
  helper must be total and agree with `AExp.aval`/`BExp.bval`. Easy to get the
  `Plus` clause right, easy to forget it exists.
- **Scope creep into arrays.** Arrays are *out of scope* for this migration. The
  bridge is built array-ready; adding array constructors + an abstract array
  domain is separate, later work. Do not let "array-ready" pull array analysis
  into this slice.
- **Phase 3 size.** The command/collecting simulation is the cost center. If it
  balloons, hoist `embed`-commutation helpers rather than widening `auto`.

## First slice

Scaffold `src/IMP2/IMP2_Bridge.thy` with the two definitions and two agreement
lemmas stubbed to `sorry`, via I/Q; fill via the I/Q inner loop; batch-gate when
file-clean. Do not touch Phases 2-3 until Phase 1 is green.
