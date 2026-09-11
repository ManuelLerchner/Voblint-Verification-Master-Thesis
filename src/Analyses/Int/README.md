# Analyses / Int

`Voblint_Analysis_Int` is `int_dom`: the reduced product of Sign, Interval, Parity and
Congruence. It is the only domain here whose components can talk to each other, and
that exchange — refinement — is what this session is about.

It is parented on `Voblint_Nonrelational` and lists the four component sessions, so it
is the one analysis session that sees more than its own domain, by construction.

## Vocabulary

| Term | Meaning |
| --- | --- |
| reduced product | a product lattice where components may sharpen one another. Without that exchange it would be a plain product and no more precise than its parts run separately. |
| reduction step | a function on `int_dom` that is *exact* — `int_reduction_step` requires it to preserve the concretization while descending the order, so a sharpened component never drops a concrete state |
| `Refine_Never` | disable cross-component reduction. Native component filters remain active; Congruence alone has nontrivial arithmetic inverses for addition, subtraction, and multiplication. |
| `Refine_Once` | one reduction round per composite operation |
| `Refine_Fixpoint` | iterate reduction to a fixpoint. The production default. |
| distributed information | a fact no single component holds: Congruence's `6 (mod 0)` plus Interval's `[0,10]` pin a value neither pins alone |

## The layer chain

```text
Int_Domain              the four-component record and its concretization
Int_Refinement          exactness of reduction steps; one refinement round
Int_Refinement_Control  the three refine modes
  -> Int_Arithmetic / Int_Backward / Int_Warrowing   mode-aware forward, backward,
                                                     and componentwise widen/narrow
  -> Int_Transfer -> Int_Exec                        transfer bundles; executable carrier
  -> Int_Sound                                       the spec and its soundness
  -> Int_Exec_Sound                                  mode-parameterized raw runtime API
  -> generated/Int_Analyses                          the context policies over that route
                                                     (generated; see below)
  -> Int_Solver_Analyses                             their reports at Apinis warrowing
  -> Int_Classify                                    check discharge
  -> generated/Int_Assembly                          the unit-context route, four
                                                     disciplines, mode pinned
  -> Int_Checks                                      the published names and the report
  -> Int_Entry                                       the production endpoint, and its
                                                     soundness at int_dom
```

At the unit context Int publishes all four disciplines, as Interval does: its
Interval component has infinite ascending chains, so a loop-carried value needs
Apinis warrowing to terminate, and that is the production default.

Public result and report entry points select `Refine_Fixpoint` with Apinis
warrowing. Lower runtime layers retain the mode parameter for comparisons and
regression witnesses.

## Worked example: `if (y + 1 == 3) { x := 1 } else { x := 0 }`

The guard gives `y + 1 = 3`. Backward filtering inverts `+` and hands the leaf `y` a
candidate. What each mode then does with it:

- `Refine_Never` — Congruence narrows `y` to `2 (mod 0)` on its own; Sign, Interval and
  Parity learn nothing, so `y` stays `STop`/`top`/`PTop`.
- `Refine_Once` — one round pushes the congruence singleton into the other three, and
  `y` becomes `SPos`/`[2,2]`/`PEven`/`2 (mod 0)`: exact.
- `Refine_Fixpoint` — the same, here. One round already sufficed *for this guard*.

`Exec_Int_DG_Run` (Examples/Int) proves the `Refine_Never` and `Refine_Once` results by
real solver runs and closes with `dgExI_never_ne_once`; `Refine_Fixpoint` is the CLI's
mode, so its result is pinned by the CLI regression. That `Once` equals `Fixpoint` here
is not a general fact: `refinement_round_is_progressive` in `Example_Int_Domain` is a
witness where a further round still makes progress.

## Widening

`Int_Warrowing` is exactly componentwise — Interval's own accelerating widen and narrow
surface through and no reduction runs afterwards. That is deliberate: a concrete
counterexample there shows that running `refine` after `narrow` (which is Goblint's own
choice) would break the solver's `narrow_ge` bracket.

## The two contextual configurations

`generated/Int_Analyses.thy` is machine-written from `assembly/analyses.yaml`,
so the orientation a reader needs lives here rather than in a header the
generator owns.

Neither contextual policy has a pipeline of its own. Both are interpretations
of `routed_dg_analysis`, which owns the equation system, the solve, the covered
keys, the reader, the result table, the contextual report and the
activation-indexed soundness endpoint. Int supplies its own implementation and
facts, the routing functions, the solver, and the published names.

Int is the domain where two axes meet, and they stay independent.

`mode` is Int's refinement axis and it stays **free** in the registrations.
Every obligation the assembly asks for is discharged by one of Int's own
mode-generic facts — `int_is_sound_transfer_for`, `int_tf_st_for_commute`,
`int_dom_enter_st_for_commute`, `int_cinit_gamma`, the two classifier laws — so
each registration holds at an arbitrary `refine_mode`. Only the published
constants pin `Refine_Fixpoint`, where a config-driven caller needs one
concrete choice. That is what keeps the arbitrary-mode API from narrowing: it
is not a second layer maintained alongside a pinned one, it is the same
registration read at a free parameter.

Solver discipline is the second axis. Each context is registered twice, at
always-join and at Apinis warrowing, and the two differ in no argument but the
solve.

A call string is the last `k` call sites on the stack. `cs_route` never reads
the state it is handed, which makes `fun_route_activation_collect_sound` the
applicable endpoint. The entry-state run keys a callee on the abstract values
its formals hold on entry, and `exec_formals_route` does read that state, so
`entry_state_activation_collect_sound` applies there instead — its
admitted-context relation is the one the entry answer induces rather than the
graph of a function on stores.

Because `mode` and `k` are both free, neither contextual registration can be a
`global_interpretation`: that form cannot leave a parameter free. Both are
plain interpretations inside a `context fixes` block, and the published
constants apply the pipeline directly rather than renaming it through
`defines`. The context-insensitive run is the opposite case — `Int_Assembly`
pins the mode and therefore can use `global_interpretation` with `defines`.

Int carries no emptiness predicate of its own. The shared assembly pins the
bottom test to the program's declaration predicate and proves it agrees with
the semantic emptiness test.
