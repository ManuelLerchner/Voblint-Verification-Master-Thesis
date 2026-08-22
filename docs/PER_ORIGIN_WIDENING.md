# Per-origin widening (executable, as a domain lift)

A sibling solver discipline that stores one abstract value **per write origin** and widens
those cells independently, reading their join. Built to test whether per-origin widening
recovers precision on the recursive interval example — executably and mechanically checked.

**Result up front:** it does **not**, and the origin split is not the deciding factor. The
dominant precision loss on globals was the missing widening bot-law (fixed separately); the
residual loss is the flow-insensitive global side slot. See *Evaluation* below.

## Why not the vendored rule

The vendored `TD` solver already has a `warrowing_per_origin` update rule, but it does **not
code-generate**: `by eval` raises `Interrupt_Breakdown` inside
`update_global_warrowing_per_origin` (`vendor/td-verification/Update_rules.thy`). That is the
whole of OPEN_PROBLEMS **P11**. So per-origin widening had to be realised another way.

## The construction (domain lift, not a new solver)

Per-origin widening is realised as a **thin adapter** that lifts an existing equation
system's value domain, then runs the *ordinary* Apinis warrowing solver. No new solver, no
new code generator.

| Layer | File | Content |
| --- | --- | --- |
| domain | `src/Analysis/Generic/Domain/Origin_State.thy` | `('a,'b) origin_st`: value-per-origin map, implicit `⊥` default, assoc-list rep. Full lattice + warrowing instance stack. `collapse_origins` = join over all origins. Widening is per-origin pointwise, **guarded** so an all-`⊥` cell stays `⊥` (needed for quotient well-definedness). |
| adapter | `src/Analysis/Generic/Solver/Exec/Origin_Lift.thy` | `lift_tree` rewrites a strategy tree: reads (`QueryL`/`QueryG`) `collapse_origins` the origin map, writes (`Answer`/`Side`) `inject_origin` at the evaluated unknown's origin, transfers unchanged. `origin_lift_eqs`, `TD_side_per_origin_widen_solve`, `read_per_origin`. |
| example | `src/Soundness/Examples/Digest/Example_Interval_Recursion_Origin.thy` | Runs it on the recursive interval program; compares to monovariant warrowing; GraphViz. |

The solver's own pointwise widening on `origin_st` **is** per-origin widening, and with
finitely many origins it terminates — so `by eval` runs it directly.

## Soundness status

The reduction carrying ordinary warrowing soundness through the lift is proved for the
**local right-hand side**:

- `traverse_lift_tree`: `traverse_rhs (lift_tree org t) σ' = inject_origin org (traverse_rhs t (collapse_origins ∘ σ'))`.
- `collapse_eq_origin_lift`: collapsing a lifted equation's result recovers the original
  transfer on collapsed reads verbatim.

The remaining half of the `part_post_solution` transport (`sides_of_rhs`, `dep_L`) follows
the same shape and is the open mechanization noted in P11.

## Evaluation — evidence, not expectation

On the recursive interval program (`void p(){ if (G<3){ G:=G+1; p() } else { G:=G } }`), with
origin = program point (`org_of = id`, the finest split that code-generates):

- **Terminates and `eval`s** — unlike the value-digest solve (P12), which breaks down.
- **`G` = `[0,+inf]`** — machine-checked: `rec_per_origin_still_widens_to_top` and
  `rec_per_origin_matches_monovariant` (`by eval`) prove the observable `G` equals monovariant
  warrowing's `[0,+inf]`. Per-origin widening is **no more precise** than the monovariant solve.

**Where the precision is (and is not) lost.** The barrier is **not** primarily `collapse_origins`.
The mechanized breakdown, in order of impact:

- **Lower bound — fixed by the widening bot-law, unrelated to origins.** Interval widening now
  carries `⊥ ▽ x = x`. Without it, `⊥` is the empty interval `[+inf,-inf]`, so an unguarded widen
  from `⊥` jumped straight to the top interval, topping **every** global on its first write —
  `G := 5` with no loop gave `[-inf,+inf]`. That was the dominant loss and had nothing to do with
  per-origin widening. With the bot-law the lower bound is exact (`0`) for both solves.
- **Upper bound — lost because the global side slot is flow-insensitive.** `G` is a single
  flow-insensitive side slot. The guard `G < 3` refines the *read* flow-sensitively, but the
  increment's write-back to the slot is unguarded, so `F([0,+inf]) = [0,+inf]` is a genuine
  fixpoint. No value-domain machinery shrinks it.
- **Per-origin widening is orthogonal.** It separates the recursion's *writes* into their own
  cells (that terminates and works), but the observable is `collapse_origins` and every cell tops
  the same way, so the collapse equals the monovariant value. Origin-separated *reads* would not
  help under a per-program-point origin either: the increment must read its own origin, because the
  previous recursion depth shares its program point — so no reader breaks the self-loop. Per-origin
  becomes relevant only if the **side semantics** changes (flow-/context-sensitive slots).
- **Real narrowing is enabled and helps locals, but not this global.** Interval narrowing (fill an
  infinite bound of the widened value from the guard-refined value) is a real operator, not the
  identity. It recovers *locals* (`while(x<20){x:=x+1}` → `[0,20]` under *every* update rule) via the
  guard filter. On the flow-insensitive global there is nothing to descend to, so `G` stays `[0,+inf]`.
  It does **not** cause divergence: the full build is green with it on. (An earlier note blamed
  narrowing for the `rec_digest` breakdown — that was wrong; the breakdown is the bot-law keeping `G`
  precise so the value-keyed digest churns a bucket per depth, and it happens with narrowing on or off.)

This is the honest, executable conclusion: **per-origin widening, as a value-domain lift, does not
recover precision on recursive globals — and neither does narrowing (though narrowing does sharpen
locals).** The real barrier is the **flow-insensitive global side slot**; a finite upper bound needs
context/origin-sensitive **reads** of the slot (a side-semantics change). A gas-bounded narrowing
solver (`update_global_bounded_narrowing`, TD Listing 9) was probed and, even with real narrowing,
still yields `[0,+inf]` on this global, so it is not the missing piece either.
