# Analyses / Congruence

`Voblint_Analysis_Congruence` is the residue-class domain: values known modulo some
integer. It is the one domain here that is **not a selectable analysis**. It has no
transfer functions, no equation system and no check discharge, and `analysis_domain`
has no constructor for it.

It exists as the fourth component of `int_dom`, the reduced product in
`Voblint_Analysis_Int`. That is also why this session is small: a component needs a
lattice, arithmetic, a widening/narrowing pair and a backward filter, and nothing else.

## Vocabulary

| Term | Meaning |
| --- | --- |
| congruence | a value constrained to one residue class: `x = r (mod m)`. `m = 0` pins a single integer; `m = 1` constrains nothing. |
| normalized | the canonical representative of a class, so equal constraints have equal representations and the order is decidable (`Congruence_Lattice`) |
| backward filter | narrowing a congruence from a known result, e.g. `x + 1 = 3` gives `x = 2`. Congruence is the component with a genuine arithmetic inverse, which is why it is the only one `Refine_Never` still narrows. |

## Files

| File | What |
| --- | --- |
| `Congruence_Domain.thy` | the type and its concretization |
| `Congruence_Lattice.thy` | normalization, order, join and meet |
| `Congruence_Warrowing.thy` | widening and narrowing, needed because the modulus is unbounded |
| `Congruence_Arithmetic.thy` | modular `+`, `-`, `*` on residue classes |
| `Congruence_Backward.thy` | the inverse direction: what a known result tells you about an operand |

## Worked example

`x` is unconstrained; `y := x * 2` is `0 (mod 2)`; `z := y + 1` is `1 (mod 2)`. The
forward direction is `Congruence_Arithmetic`. Now suppose a guard establishes
`z = 7`: `Congruence_Backward` runs the same arithmetic in reverse and narrows `y` to
`6 (mod 0)`, a singleton. Inside `int_dom` that singleton is then handed to the other
three components by refinement, which is how a congruence fact sharpens an interval —
see `Example_Int_Backward` for the composite version, and
`Example_Congruence_Arithmetic` / `Example_Congruence_Backward` for this component on
its own.
