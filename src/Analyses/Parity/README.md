# Analyses / Parity

`Voblint_Analysis_Parity` is the even/odd domain. It reuses the shared
non-relational evaluator and routed analysis spine while retaining its own
lattice, arithmetic, queries, and classification.

It also says things the other domains cannot. `y := x * 2` is even whatever `x` is
— a fact neither Sign nor Interval can express, since neither tracks divisibility.

## Vocabulary

| Term | Meaning |
| --- | --- |
| `parity` | the flat lattice `PEven`/`POdd` with top and bottom. Finite height, so the always-join solver suffices and no widening is needed. |
| `parity_cinit_gamma` | Parity's initial-state contract (`Parity_Sound`): a declared global starts at zero, which `PEven` describes exactly. Each registration's initial-state obligation cites it |
| `parity_rule.equations` / `parity_rule.solution` | the equation system a compiled program generates, and the solver's solution for it, at a global update rule `r` (`Parity_Analyses`) |
| classify | turning a solved abstract value into `Check_Proved`/`Check_Refuted`/`Check_Unknown` for one check condition (`Parity_Classify`) |

## The layer chain

```text
Parity_Domain      the lattice, order, and its concretization
  -> Parity_Special / Parity_Transfer   special calls; the transfer functions
  -> Parity_Exec                        executable transfer, on the finite-map carrier
  -> Parity_Sound                       what the initial abstract state describes
  -> Parity_Numeric_Queries             numeric queries used by check discharge
  -> Parity_Classify                    classification of one check condition
  -> generated/Parity_Analyses          the unit, entry-state and call-string
                                        registrations, each at any global update rule
```

`generated/Parity_Analyses` is written by `scripts/gen_analysis_assembly.py`
from `manifests/analyses.yaml`.

`Parity_Analyses` holds three `global_interpretation`s, each with the global
update rule `r` as a parameter: `parity_rule` of `unit_dg_analysis`
(`Shared/Result/Unit_DG_Analysis.thy`), and `parity_es_rule` and `parity_cs_rule`
of `routed_dg_analysis` for the two policies that route calls to more than one
context. Each discharges the same twelve obligations from Parity's transfer
contract, two commutation laws, the solver contract, the classifier contract and
the initial-state contract, and gets back the equation system, the solve, the
reader, the result table, the report and every soundness endpoint. Nothing in
this session builds a second copy of that pipeline.

Parity currently has no backward-domain interpretation. Branch transfer is the
conservative identity, so guards do not refine parity facts.

## Worked example

`Example_Parity_DG_Flagship` (Examples/Parity) compiles an even-step loop, generates
its equations through Parity's unit-context registration `parity_rule`
(`parity_rule.equations`), solves them at the always-join rule, and closes with
`parity_source_run_sound` — the same statement shape as Sign's `dgEx_source_run_sound`
(`Exec_Sign_DG_Run`) and Interval's `flagship_source_run_sound`. Nothing in that chain is
Parity-specific except the lattice.

`Example_Parity_Checks_Store_Only` (Examples/CLI, grouped with the other domains'
members of the same store-only trio) is the check-discharge witness: `y := x * 2` and `z := y + 1` land in
disjoint parity classes whatever the unconstrained `x` is, so one check is proved and
one refuted. A third, against another unconstrained value, is unknown — Parity has no
singleton, so it can never prove a positive equality.

## The two contextual configurations

`generated/Parity_Analyses.thy` is machine-written from `manifests/analyses.yaml`,
so the orientation a reader needs lives here rather than in a header the
generator owns.

Neither contextual policy has a pipeline of its own. Both are interpretations
of `routed_dg_analysis`, which owns the equation system, the solve, the covered
keys, the reader, the result table, the contextual report and the
activation-indexed soundness endpoint — for every domain at every policy. Parity
supplies its own implementation and facts; the generator adds the routing
functions and the solver. Nothing else.

Both are selectable from the CLI at every `--globals` rule: `--context entry-state`
and `--context call-string --context-depth K` for any `K >= 0`. `run_voblint` reads
`parity_es_rule` and `parity_cs_rule`, which take the global update rule as a
parameter. The choice matters little here: `parity` is a finite lattice whose `warrowing`
instance sets `widen = sup`, so a warrowing rule buys no termination the join
lacks.

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

The context-insensitive run is neither of these: it is `parity_rule`, the
registration of the same assembly at the unit context.

Global keys differ per policy and are therefore parameters, not a fixed shape.
The call-string run keys at `call_string_gk`, shared with every other
call-string-keyed instance. The entry-state run keys at `routed_gk` —
`Analysis_Global` at `unit`, since Parity publishes no named global of its own,
and `Activation_Seed` carrying a callee entry point with its routed context.
