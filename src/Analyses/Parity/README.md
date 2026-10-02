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
Parity_Warrowing   widening, narrowing, numeric_domain instance (lattice: Voblint_Domain.Parity_Lattice)
Parity_Domain      arithmetic, comparisons, and the expression evaluator
  -> Parity_Special / Parity_Backward  special calls; inverse operators and their certificate
  -> Parity_Transfer                    the parity_ops bundle and its one interpretation
  -> Parity_Exec                        executable transfer, on the finite-map carrier
  -> Parity_Sound                       what the initial abstract state describes
  -> Parity_Numeric_Queries             numeric queries used by check discharge
  -> Parity_Classify                    classification of one check condition
  -> generated/Parity_Analyses          the unit, entry-state and call-string
                                        registrations, each at any global update rule
```

`generated/Parity_Analyses` is written by `scripts/gen_analysis_assembly.py`
from `manifests/analyses.yaml`.

`Parity_Analyses` holds one `global_interpretation`, `parity_rule`, with the
global update rule `r` as a parameter: `dg_analysis_exec`
(`Shared/Result/DG_Analysis.thy`) at the unit route. It applies
`parity_tf.dg_analysis_execI`, which Parity's bundle certificate provides, and
discharges the six obligations left: the routing agreement, the seed key, the
solver contract and the initial-state contract. It gets back the equation system, the solve, the reader, the result table,
the report and the context-free soundness endpoints. The entry-state and
call-string runs are the CLI's combined registrations, `mcp_es_rule` and
`mcp_cs_rule` (`Voblint_CLI.MCP_Analyses`), which route calls to more than one
context for every active analysis at once; Parity's own registration still
matters there, since the combined state cites `parity_rule.comp_sound` and
`parity_rule.init_sound`.

Guards refine parity through `parity_refine_ops`: an equality that held gives
both sides the meet of their parities, a known sum or difference fixes one
operand's parity from the other's, and an odd product makes both factors odd.
An order comparison says nothing about parity and leaves the store unchanged.

## Worked example

`Example_Parity_DG_Flagship` (Examples/Parity) compiles an even-step loop, generates
its equations through Parity's unit-context registration `parity_rule`
(`parity_rule.equations`), solves them at the always-join rule, and closes with
`parity_source_run_sound` — the same statement shape as Sign's `dgEx_source_run_sound`
(`Exec_Sign_DG_Run`) and Interval's `flagship_source_run_sound`. Nothing in that chain is
Parity-specific except the lattice.

`tests/regression/18-parity/precision/05-check_trio.vimp` is the check-discharge witness: `y := x * 2` and `z := y + 1` land in
disjoint parity classes whatever the unconstrained `x` is, so one check is proved and
one refuted. A third, against another unconstrained value, is unknown — Parity has no
singleton, so it can never prove a positive equality.

## Parity in the entry-state and call-string runs

`generated/Parity_Analyses.thy` is machine-written from `manifests/analyses.yaml`,
so the orientation a reader needs lives here rather than in a header the
generator owns.

Parity's own generated file registers only the context-insensitive run,
`parity_rule`. The entry-state and call-string runs are the CLI's combined
registrations, `mcp_es_rule` and `mcp_cs_rule` (`Voblint_CLI.MCP_Analyses`),
which run every active analysis as fields of one state; Parity is one of
those fields whenever `Parity_Analysis` is in the activation list. Neither
policy has a pipeline of its own. Both are interpretations of
`dg_analysis`, which owns the equation system, the solve, the covered
keys, the reader, the result table, the contextual report and the
activation-indexed soundness endpoint — for every active combination at every
policy.

Both are selectable from the CLI at every `--globals` rule: `--context entry-state`
and `--context call-string --context-depth K` for any `K >= 0`, with Parity in
the activation. `run_voblint` reads `mcp_es_rule` and `mcp_cs_rule`, which take
the activation list and the global update rule as parameters. The choice
matters little here: `parity` is a finite lattice whose `warrowing` instance
sets `widen = sup`, so a warrowing rule buys no termination the join lacks.

A call string is the last `k` call sites on the stack, so a procedure entered
from two places is analysed twice rather than once at the join. `cs_route`
never reads the state it is handed, which is what makes
`fun_route_activation_collect_sound` — the endpoint for a route that is a
function of the call site and the caller's context alone — the applicable one.
`k` is runtime data, so the registration leaves it free beside the activation
and the rule (`for as k r`), and a caller applies the locale's constants to
all three.

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
call-string-keyed instance. The entry-state run keys at `global_unknown` —
`Analysis_Global` at `unit`, since Parity publishes no named global of its own,
and `Activation_Seed` carrying a callee entry point with its routed context.
