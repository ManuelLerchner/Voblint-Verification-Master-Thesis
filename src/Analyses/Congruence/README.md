# Analyses / Congruence

`Voblint_Analysis_Congruence` is the residue-class domain: values known modulo
some integer. It fills two roles at once. It is a selectable analysis, with its
own transfer functions, executable carrier, equation system and check discharge,
an `analysis_domain` constructor, and a whole-program run at every context
policy and global update rule. It is also the fourth component
of `int_dom`, the reduced product in `Voblint_Analysis_Int`, where it carries
the modular facts none of the other three components can express.

The component role needs only a lattice, arithmetic, a widening/narrowing pair
and a backward filter. Everything listed below `Congruence_Backward` in the file
table exists for the selectable role.

## What the comparison operators do, and what they could do

`congruence_lt` and `congruence_eqb` decide pairs of singletons (`m = 0`).
The six VIMP comparisons use these queries directly: `>` reverses the operands,
`<=` and `>=` complement the appropriate strict-order query, and `!=` complements
equality. Singleton ordering is exact; genuinely unbounded classes carry no
definite ordering information.

Equality has a remaining precision gap:

- an even integer never equals an odd one, so `congruence_eqb` can answer
  `Some False` whenever the two residue classes are disjoint ---
  `r1 != r2 (mod gcd m1 m2)` --- and not only when both collapse to a point;

`min` and `max` return the join of their arguments, since either result must be
one of the operands.

Division by a nonzero singleton retains an exact quotient class when the
divisor divides both the residue and modulus. For example, `3 (mod 12)`
divided by `3` becomes `1 (mod 4)`; divided by `-3`, it becomes `3 (mod 4)`.
Otherwise division keeps exact singleton results and falls back to top.
Division by zero follows VIMP's totalization and yields zero.

Judging the domain by its comparison operators undervalues it in any case. Congruence
is there to carry modular information --- alignment, stride, access patterns --- which
is what makes it the one component whose arithmetic inverses still narrow under
`Refine_Never`.

A warrowing rule buys it nothing, though every registration accepts one. Its widening
is plain join: the modulus only ever coarsens, so an ascending chain is a divisor chain
and terminates without acceleration.

## Vocabulary

| Term | Meaning |
| --- | --- |
| congruence | a value constrained to one residue class: `x = r (mod m)`. `m = 0` pins a single integer; `m = 1` constrains nothing. |
| normalized | the canonical representative of a class, so equal constraints have equal representations and the order is decidable (`Congruence_Lattice`) |
| backward filter | narrowing a congruence from a known result, e.g. `x + 1 = 3` gives `x = 2`. Congruence is the only component with genuine inverses for `+`, `-` and `*` --- Sign's and Interval's are the identity --- so under `Refine_Never` it is the only one that narrows through arithmetic. |

## Files

| File | What |
| --- | --- |
| `Congruence_Domain.thy` | the type and its concretization |
| `Congruence_Lattice.thy` | normalization, order, join and meet |
| `Congruence_Warrowing.thy` | the `warrowing` instance the TD solver's sort requires (widening is join, narrowing keeps the left argument), then the `numeric_domain` instance, which needs it |
| `Congruence_Arithmetic.thy` | modular `+`, `-`, `*` on residue classes |
| `Congruence_Backward.thy` | the inverse direction: what a known result tells you about an operand |
| `Congruence_Special.thy` | `Min`/`Max` return an operand, so both answer with the join of their arguments; `Nondet_Int` lands at `top` |
| `Congruence_Transfer.thy` | one abstract operation per edge kind the framework can hand a domain, and their `sound_transfer_for` contract |
| `Congruence_Exec.thy` | the same eight operations on the compact state the solver stores, each shown to agree with its abstract counterpart |
| `Congruence_Numeric_Queries.thy` | interprets the generic query interface at `congruence_lt`/`congruence_eqb`, so the check layer reads Congruence like any other domain |
| `Congruence_Sound.thy` | `congruence_cinit_gamma`: what the abstract state a run starts in describes |
| `Congruence_Classify.thy` | one interpretation of `abstract_check_domain`: the Boolean recursion over a check condition and its three-way verdict |
| `generated/Congruence_Analyses.thy` | generated from `manifests/analyses.yaml`: `congruence_rule`, the interpretation of the shared `unit_dg_analysis`, and `congruence_es_rule` and `congruence_cs_rule` for the entry-state and call-string configurations, all at any global update rule; see below |

## Worked example

`x` is unconstrained; `y := x * 2` is `0 (mod 2)`; `z := y + 1` is `1 (mod 2)`. The
forward direction is `Congruence_Arithmetic`. Now suppose a guard establishes
`z = 7`: `Congruence_Backward` runs the same arithmetic in reverse and narrows `y` to
`6 (mod 0)`, a singleton. Inside `int_dom` that singleton is then handed to the other
three components by refinement, which is how a congruence fact sharpens an interval —
see `Example_Int_Backward` for the composite version, and
`Example_Congruence_Arithmetic` / `Example_Congruence_Backward` for this component on
its own.

## The two contextual configurations

`generated/Congruence_Analyses.thy` is machine-written from `manifests/analyses.yaml`,
so the orientation a reader needs lives here rather than in a header the
generator owns.

Neither contextual policy has a pipeline of its own. Both are interpretations
of `routed_dg_analysis`, which owns the equation system, the solve, the covered
keys, the reader, the result table, the contextual report and the
activation-indexed soundness endpoint — for every domain at every policy. Congruence
supplies its own implementation and facts; the generator adds the routing
functions and the solver. Nothing else.

A call string is the last `k` call sites on the stack, so a procedure entered
from two places is analysed twice rather than once at the join. `cs_route`
never reads the state it is handed, which is what makes
`fun_route_activation_collect_sound` — the endpoint for a route that is a
function of the call site and the caller's context alone — the applicable one.
`k` is runtime data, so the registration leaves it free beside the rule
(`for k r`), and a caller applies the locale's constants to both.

The entry-state run keys a callee on the abstract values its formals hold on
entry. Here `exec_formals_route` does read the state it is handed — the callee
frame the routed generator has already entered — so the applicable endpoint is
`entry_state_activation_collect_sound`, whose admitted-context relation is the
one the entry answer induces rather than the graph of a function on stores.
That difference is why the executable route and its abstract counterpart
`formals_route_lifted_gen` are separate parameters.

The context-insensitive run is neither of these: it is `congruence_rule`, the
registration of the same assembly at the unit context.

Global keys differ per policy and are therefore parameters, not a fixed shape.
The call-string run keys at `call_string_gk`, shared with every other
call-string-keyed instance. The entry-state run keys at `routed_gk` —
`Analysis_Global` at `unit`, since Congruence publishes no named global of its own,
and `Activation_Seed` carrying a callee entry point with its routed context.
