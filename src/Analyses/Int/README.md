# Analyses / Int

`Voblint_Analysis_Int` is `int_dom`: the reduced product of Sign, Interval, Parity and
Congruence. It is the only domain here whose components can talk to each other, and
that exchange — refinement — is what this session is about.

It is parented on `Voblint_Analysis_Base` and lists the four component sessions, so it
is the one analysis session that sees more than its own domain, by construction.

## Vocabulary

| Term | Meaning |
| --- | --- |
| reduced product | a product lattice where components may sharpen one another. Without that exchange it would be a plain product and no more precise than its parts run separately. |
| reduction step | a function on `int_dom` that is *exact* — `int_reduction_step` requires it to preserve the concretization while descending the order, so a sharpened component never drops a concrete state |
| `Refine_Never` | no exchange. Only Congruence still narrows, since it is the one component with a real arithmetic inverse. |
| `Refine_Once` | one reduction round per composite operation |
| `Refine_Fixpoint` | iterate reduction to a fixpoint. The production default. |
| distributed information | a fact no single component holds: Congruence's `6 (mod 0)` plus Interval's `[0,10]` pin a value neither pins alone |

## The layer chain

```text
Int_Domain        the four-component record and its concretization
Int_Refinement    exactness of reduction steps; the three refine modes
  -> Int_Arithmetic / Int_Backward / Int_Warrowing   mode-aware forward, backward,
                                                     and componentwise widen/narrow
  -> Int_Transfer -> Int_Exec                        transfer bundles; executable carrier
  -> Int_Sound                                       the spec and its soundness
  -> Int_Exec_Sound                                  the arbitrary-program runtime API,
                                                     fixed at Refine_Fixpoint
  -> Int_Analyses                                    the context policies over that route
  -> Int_Classify / Int_Checks                       check discharge and the report
```

## Worked example: `if (y + 1 == 3) { x := 1 } else { x := 0 }`

The guard gives `y + 1 = 3`. Backward filtering inverts `+` and hands the leaf `y` a
candidate. What each mode then does with it:

- `Refine_Never` — Congruence narrows `y` to `2 (mod 0)` on its own; Sign, Interval and
  Parity learn nothing, so `y` stays `STop`/`top`/`PTop`.
- `Refine_Once` — one round pushes the congruence singleton into the other three, and
  `y` becomes `SPos`/`[2,2]`/`PEven`/`2 (mod 0)`: exact.
- `Refine_Fixpoint` — the same, here. One round already sufficed *for this guard*.

`Exec_Int_DG_Run` (Examples/Int) proves all three by real solver runs, and closes with
`dgExI_never_ne_once` and `dgExI_once_eq_fixpoint`. That `Once` equals `Fixpoint` here
is not a general fact: `refinement_round_is_progressive` in `Example_Int_Domain` is a
witness where a further round still makes progress.

## Widening

`Int_Warrowing` is exactly componentwise — Interval's own accelerating widen and narrow
surface through and no reduction runs afterwards. That is deliberate: a concrete
counterexample there shows that running `refine` after `narrow` (which is Goblint's own
choice) would break the solver's `narrow_ge` bracket.
