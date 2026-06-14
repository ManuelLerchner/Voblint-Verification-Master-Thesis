<!-- markdownlint-disable-file MD025 -->

# Migration: rebase soundness onto AFP IMP2 (one-way bridge)

Status: **PHASE 1-3 DONE (route 2b)** 2026-06-13. Implements part 2 of
`docs/AFP_IMP2_REUSE_DECISION.md`. Bridge theory `src/IMP2/IMP2_Bridge.thy` is
batch-green in session `Voblint_IMP2`. The scope-semantics divergence found
during Phase 2 is **resolved** (route 2b): our concrete semantics zero locals on
scope/call entry exactly like IMP2, and our `is_global` (`IMP2_Globals`) now
matches AFP IMP2's `is_global` (`Syntax`) on the nose (empty name + `G…` are
global), so `combine_states`/`enter_state` correspond under `proj0` with no
side condition. Phase 3 is done: `backward_sim` proves every terminating AFP
IMP2 big-step run of a translated source program is reproduced by our
frame-stack small-step semantics (`pruns_to`), read back through `proj0`. This
is the direction soundness transfer needs (analyzer sound for all our runs +
every IMP2 run is one of ours ⇒ analyzer sound for IMP2).

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

Ours (`src/IMP2/IMP2_Syntax.thy`, `IMP2_Expr.thy`):

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

**DONE.** `IMP2_Bridge.thy` defines `embed`, `nip_aexp`/`nip_bexp` (Nipkow
leaf recursion), `to_imp2_aexp`/`to_imp2_bexp`, and proves `aval_to_imp2`,
`bval_to_imp2` (via `aval_nip`/`bval_nip`). Default index is IMP2's `Syntax.N 0`
(confirmed in `Syntax.thy` line 129). Heavy name clashes (`aexp/bexp/aval/bval/
N/V/Bc/Plus/Not/And/Less`) are handled by qualifying every IMP2 constructor
with `Syntax.` and every Nipkow leaf with `AExp.`/`BExp.`. Note `( * )` trips
the comment lexer inside quotes, so `Times` uses the `times` constant.

### Phase 2 - commands

`to_imp2_com :: com => IMP2.com` (`src/IMP2/IMP2_Proc.thy` `com`, `frame = store`).
Map our command constructors to IMP2's. Lift `embed` through assignments and
control flow. Surface a per-command agreement (assignment updates one variable's
array at the default index).

**DONE.** `to_imp2_com` maps SKIP/Assign/Seq/If/While/Scope/Call/Restore;
`Assign x a -> AssignIdx x (N 0) (to_imp2_aexp a)`, `Call p -> PCall p`,
runtime-only `Restore -> SKIP` (never reached on source). `to_imp2_pi` wraps
each procedure body in `Syntax.Scope` (IMP2 `PCall` has no scope of its own;
our `Call` save/restores locals via the frame stack, so the scoping must live
in the translated body). `proj0 S = (%x. S x 0)` reads each array back at the
default index (`proj0_embed : proj0 (embed s) = s`). Per-command agreement:
`to_imp2_Assign_bigstep` (IMP2 big-step of a translated assignment from an
embedded state) and `proj0_Assign` (projecting that result recovers our scalar
update `s(x := aval a s)`).

**Phase 3 foundation (proved here, batch-green).** `embed` is *not* preserved
by IMP2 array assignment (a write touches only index 0), so the command-level
invariant must be the projection relation `proj0 S = s`, not `S = embed s`.
Since translated expressions only read index 0, the expression agreement
generalises to that relation: `aval_to_imp2_sim`, `bval_to_imp2_sim` (via
`aval_nip_sim`/`bval_nip_sim`). These are the reusable core for the Phase 3
simulation and recover the embed lemmas through `proj0_embed`.

### Phase 3 - small-step / collecting simulation (the bulk)

Show our small-step (or `cfg_collect`) simulates IMP2's semantics under
`to_imp2_com` / `embed`, then re-state the top-level soundness theorem against
IMP2's semantics. This is where the real proof effort sits; expect helper lemmas
on `embed` commuting with state updates.

Exit: the headline soundness theorem reads "sound w.r.t. AFP IMP2", batch-green.

**DONE (route 2b).** Proved in `src/IMP2/IMP2_Bridge.thy`, batch-green:

- `is_global_eq`: our `is_global` agrees with AFP IMP2's everywhere (the
  `IMP2_Globals` definition was aligned to IMP2's `Syntax.is_global`, adding the
  empty-name case). Hence `proj0_combine_states`
  (`proj0 <S|T> = <proj0 S|proj0 T>`) and `proj0_null_combine`
  (`proj0 <<>|s> = enter_state (proj0 s)`) hold unconditionally.
- `source_com` / `source_pi`: a source program (resp. procedure table) contains
  no runtime-only `Restore`.
- Frame-stack infrastructure in `IMP2_Proc.thy`: `pstep_frame_extend(_cfg)`,
  `psteps_frame_extend(_cfg)`, `psteps_frame_mono` (extra frames appended at the
  bottom survive any step), `pruns_to_Scope`, `pruns_to_Call`,
  `pruns_to_Scope_Call` (a `Scope` body and a `Call` to the same body have the
  same terminating runs).
- **`backward_sim` (the bulk):** `big_step (to_imp2_pi pi) (to_imp2_com c, S) T`,
  `source_pi pi`, `source_com c` ⟹ `pruns_to pi c (proj0 S) (proj0 T)`. By rule
  induction on IMP2's big-step derivation via the split-format `big_step_induct`;
  each rule maps to the matching `pruns_to` combinator. The program is generalised
  per case (IMP2's `PScope` rule changes it), carried as a `P = to_imp2_pi pi`
  premise (`backward_sim_aux`); the four runtime-only IMP2 commands (`ArrayCpy`,
  `CLEAR`, `Assign_Locals`, `PScope`) are vacuous (outside the range of
  `to_imp2_com`).

This is the backward direction needed to transfer the analyzer's existing
soundness (stated against `pruns_to`/`cfg_collect`) to AFP IMP2's standard
concrete semantics: the analyzer over-approximates all our runs, and every
terminating IMP2 run is one of ours. Composing with the pipeline soundness in
the top session is a one-liner with no further obligation on the analyzer side.

#### Phase 3 status - GATED on a scope-semantics decision (RESOLVED)

Phase 2 surfaced a genuine **concrete-semantics divergence** between our
small-step (`src/IMP2/IMP2_Proc.thy`) and IMP2's big-step, on *local scoping*:

| | entry | exit |
| --- | --- | --- |
| Our `Scope c` / `Call p` | locals kept (body runs in caller's store `s`) | `<fr\|s'>` - restore caller locals, commit callee globals |
| IMP2 `SCOPE c` | locals **zeroed** (`<<>\|s>`) | `<s\|s'>` - restore caller locals, commit callee globals |

The exit halves match; the **entry halves do not**. IMP2 hands the body fresh
zeroed locals; we hand it the caller's locals. The two semantics therefore
agree only on the *scope-free* fragment, or on programs that write every local
before reading it. A naive `to_imp2_com (Scope c) = Scope (to_imp2_com c)` is
thus **not** a faithful big-step simulation in general. This is a design gap the
original plan did not anticipate - it is not closable by proof effort alone.

A second, independent cost: our language has no big-step semantics, only the
frame-stack small-step `pstep` (and `pruns_to`). A forward simulation
`pruns_to ==> IMP2.big_step` needs either Seq/If/While decomposition
(inversion) lemmas for `pruns_to`, or a parallel structural big-step plus the
standard small-step <-> big-step equivalence. Either is bounded but sizable.

**Decision needed before Phase 3 proceeds** (pick one):

1. **Scope-free fragment only.** Add a `scope_free` predicate, prove forward
   simulation for it (frame stack stays `[]`), restate soundness for the
   intraprocedural core. Honest, smaller, but does not cover procedures.
2. **Reconcile entry semantics.** Either (a) translate `Scope c` to
   `Assign_Locals <<>> ;; to_imp2_com c ;; Assign_Locals (caller locals)` so the
   IMP2 side does *not* zero - i.e. model our "keep locals" scope explicitly; or
   (b) change our `Scope`/`Call` to zero locals on entry to match IMP2 (a
   semantics change to our language, with downstream proof churn). Full
   procedure coverage, larger.
3. **Defer.** Keep the bridge at the expression + assignment + projection
   granularity (current state) and treat the command/collecting simulation as a
   tracked follow-up.

The expression and assignment foundations needed by *any* of these routes are
already proved and batch-green (`aval_to_imp2_sim`, `bval_to_imp2_sim`,
`to_imp2_Assign_bigstep`, `proj0_*`). Recommendation: **route 1** first (lands
the intraprocedural restatement cleanly), then route 2(a) for procedures.

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
