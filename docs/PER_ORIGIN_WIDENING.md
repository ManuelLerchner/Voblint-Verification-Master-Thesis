# Per-origin widening (executable, as a domain lift)

A sibling solver discipline that stores one abstract value **per write origin** and widens
those cells independently, reading their join. Built to test whether per-origin widening
recovers precision on the recursive interval example — executably and mechanically checked.

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
| example | `src/Formalization/Examples/Digest/Example_Interval_Recursion_Origin.thy` | Runs it on the recursive interval program; compares to monovariant warrowing; GraphViz. |

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
- **`G` still widens to the top interval** — machine-checked:
  `rec_per_origin_still_widens_to_top` and `rec_per_origin_matches_monovariant` (`by eval`)
  prove the observable `G` equals monovariant warrowing's `[-inf,+inf]`.

**Where the precision is lost.** Per-origin widening separates the recursion's *writes* into
their own cells — that part works. But every transfer **reads** `collapse_origins`, the join
over *all* origins, including the recursive edge's own cell. So at depth `k` the increment
reads the already-merged `[0,k]`, writes `[1,k+1]` to its single origin cell, and that cell
climbs unbounded → widened to top. The origin split never breaks the self-loop because the
read re-merges it first. Recovering per-depth precision needs origin-separated **reads** (a
relational, per-origin transfer), not just per-origin widening — beyond a value-domain lift.

This is the honest, executable conclusion: **per-origin widening, as a value-domain lift with
a finite origin, does not recover precision on unbounded recursion.** It is a real,
mechanically-checked negative, and it localises the barrier precisely (collapse-on-read).
