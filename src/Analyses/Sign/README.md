# Sign domain — 7-element sign lattice

The concrete sign domain uses the shared routing, result, and non-relational
interfaces described in [`../Shared/README.md`](../Shared/README.md).
Executable witnesses live under `src/Examples/Sign/`;
they demonstrate the domain, they are not part of the reusable instance.

| File | Role |
| --- | --- |
| `Sign_Warrowing.thy` | widening (join), narrowing (left argument), and the `numeric_domain` instance; the lattice itself is `Voblint_Domain.Sign_Lattice` |
| `Sign_Arithmetic.thy` | abstract arithmetic over signs |
| `Sign_Backward.thy` | backward guard/filter operators; names the sign `afilter_sign_st`/`bfilter_sign_st` executable mirror via `Exec_Backward` |
| `Sign_Special.thy` | `sign_min`/`sign_max`, the abstract implementation of the `Min`/`Max` special calls |
| `Sign_Numeric_Queries.thy` | Sign's instance of `sound_numeric_queries` |
| `Sign_Transfer.thy` | edge transfer record and transfer soundness |
| `Sign_Exec.thy` | executable transfer mirror + `tf_st_commute` commutation |
| `Sign_Sound.thy` | the `dg_spec` Sign supplies, its concretization, and `analysis_contract` — no context, no solver |
| `Sign_Classify.thy` | Sign instance of the generic check-discharge interface |
| `generated/Sign_Analyses.thy` | one `global_interpretation`, `sign_rule`, taking the global update rule `r` as a parameter: the shared `routed_dg_analysis_exec` at the unit route. Sign's transfer, entry state, solver and classifier go in; the equation system, the solve, the reader, the result table, the report and the soundness endpoints come out |

`generated/Sign_Analyses.thy` is written by `scripts/gen_analysis_assembly.py`
from `manifests/analyses.yaml`; edit those, not the theory.

Sign's soundness endpoints live here rather than in `Voblint_CLI` because
nothing in them needs to see another domain: `sign_rule.fun_route_source_sound`,
`sign_rule.fun_route_result_node_sound` and their siblings depend on Sign and on
the routed endpoints of `Voblint_Result`, both of which this session
already has. The combined CLI state still depends on this registration:
`MCP_Carrier` cites `sign_rule.comp_sound` and `sign_rule.init_sound` when it
proves the combined component and its initial state sound, whatever other
analyses run alongside Sign.

## Sign in the entry-state and call-string runs

`generated/Sign_Analyses.thy` is machine-written, so the orientation a reader
needs lives here rather than in the generated header.

Sign's own generated file registers only the context-insensitive run,
`sign_rule`. The entry-state and call-string runs are the CLI's combined
registrations, `mcp_es_rule` and `mcp_cs_rule` (`Voblint_CLI.MCP_Analyses`),
which run every active analysis as fields of one state; Sign is one of those
fields whenever `Sign_Analysis` is in the activation list. Neither policy has
a pipeline of its own. Both are interpretations of `routed_dg_analysis`, which
owns the equation system, the solve, the covered keys, the reader, the result
table, the contextual report and the activation-indexed soundness endpoint —
for every active combination at every policy.

A call string is the last `k` call sites on the stack, so a procedure entered
from two places is analysed twice rather than once at the join. `cs_route`
never reads the state it is handed, which is what makes
`fun_route_activation_collect_sound` — the endpoint for a route that is a
function of the call site and the caller's context alone — the applicable one.
`k` is runtime data, so the registration leaves it free beside the activation
and the rule (`for as k r`), and a caller applies the locale's constants to
all three: the call-string run, `mcp_cs_rule` with Sign active, answers
`mcp_cs_rule.result as k r gs p`.

The entry-state run keys a callee on the abstract values its formals hold on
entry. Here `exec_formals_route` does read the state it is handed — the callee
frame the routed generator has already entered — so the applicable endpoint is
`entry_state_activation_collect_sound`, whose admitted-context relation is the
one the entry answer induces rather than the graph of a function on stores.
That difference is the whole content of the routing-agreement obligation, and
it is why the executable route and its abstract counterpart
`formals_route_lifted_gen` are separate parameters.

The context-insensitive run is the third policy: it is `sign_rule`, Sign's own
registration of `routed_dg_analysis_exec` at the unit route.

## Why widening buys Sign nothing

The seven-element lattice has finite height, so every ascending chain
stabilises after a bounded number of steps and widening has nothing to
accelerate — a warrowing rule buys no termination that the plain join does not
already give. A caller may still select one: `sign_rule` takes the global
update rule as a parameter, and so do `mcp_es_rule` and `mcp_cs_rule` with
Sign active, so `--globals warrow` solves and is sound at Sign like every
other rule. Parity makes the same argument; Interval and the Int product are
the domains where widening earns its keep, because their carriers admit
unbounded ascending chains.

Global keys differ per policy and are therefore parameters, not a fixed shape.
The call-string run keys at `call_string_gk`, shared with every other
call-string-keyed instance. The entry-state run keys at `routed_gk` —
`Analysis_Global` at `unit`, since Sign publishes no named global of its own,
and `Activation_Seed` carrying a callee entry point with its routed context.
