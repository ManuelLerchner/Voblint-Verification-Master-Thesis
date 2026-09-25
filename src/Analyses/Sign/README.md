# Sign domain — 7-element sign lattice

The concrete sign domain uses the shared routing, result, and non-relational
interfaces described in [`../Shared/README.md`](../Shared/README.md).
Executable witnesses live under `src/Examples/Sign/`;
they demonstrate the domain, they are not part of the reusable instance.

| File | Role |
| --- | --- |
| `Sign_Lattice.thy` | 7-element sign lattice, order operations, concretization, and `numeric_domain` instance |
| `Sign_Arithmetic.thy` | abstract arithmetic over signs |
| `Sign_Backward.thy` | backward guard/filter operators; names the sign `afilter_sign_st`/`bfilter_sign_st` executable mirror via `Exec_Backward` |
| `Sign_Special.thy` | `sign_min`/`sign_max`, the abstract implementation of the `Min`/`Max` special calls |
| `Sign_Numeric_Queries.thy` | Sign's instance of `abstract_numeric_queries` |
| `Sign_Transfer.thy` | edge transfer record and transfer soundness |
| `Sign_Exec.thy` | executable transfer mirror + `tf_st_commute` commutation |
| `Sign_Sound.thy` | the `dg_spec` Sign supplies, its concretization, and `analysis_contract` — no context, no solver |
| `Sign_Classify.thy` | Sign instance of the generic check-discharge interface |
| `generated/Sign_Analyses.thy` | three `global_interpretation`s, each taking the global update rule `r` as a parameter: `sign_rule` of the shared `unit_dg_analysis` at the unit context, and `sign_es_rule` and `sign_cs_rule` of `routed_dg_analysis` at the entry-state and call-string contexts. Sign's transfer, entry state, solver and classifier go in; the equation system, the solve, the reader, the result table, the report and every soundness endpoint come out |

`generated/Sign_Analyses.thy` is written by `scripts/gen_analysis_assembly.py`
from `manifests/analyses.yaml`; edit those, not the theory.

Sign's soundness endpoints live here rather than in `Voblint_CLI` because
nothing in them needs to see another domain: `sign_rule.source_sound`,
`sign_rule.result_node_sound` and their siblings depend on Sign and on the
`unit_dg_analysis` endpoints of `Voblint_Result`, both of which this session
already has. `run_voblint` reads the same three registrations, and
`Voblint_CLI`'s table lemmas cite their facts.

## The two contextual configurations

`generated/Sign_Analyses.thy` is machine-written, so the orientation a reader
needs lives here rather than in the generated header.

Neither contextual policy has a pipeline of its own. Both are interpretations
of `routed_dg_analysis`, which owns the equation system, the solve, the covered
keys, the reader, the result table, the contextual report and the
activation-indexed soundness endpoint — for every domain at every policy. Sign
supplies its own implementation and facts; the generator adds the routing
functions and the solver. Nothing else.

A call string is the last `k` call sites on the stack, so a procedure entered
from two places is analysed twice rather than once at the join. `cs_route`
never reads the state it is handed, which is what makes
`fun_route_activation_collect_sound` — the endpoint for a route that is a
function of the call site and the caller's context alone — the applicable one.
`k` is runtime data, so the registration leaves it free beside the rule
(`for k r`), and a caller applies the locale's constants to both:
`sign_cs_rule.result k r gs p`.

The entry-state run keys a callee on the abstract values its formals hold on
entry. Here `exec_formals_route` does read the state it is handed — the callee
frame the routed generator has already entered — so the applicable endpoint is
`entry_state_activation_collect_sound`, whose admitted-context relation is the
one the entry answer induces rather than the graph of a function on stores.
That difference is the whole content of the routing-agreement obligation, and
it is why the executable route and its abstract counterpart
`formals_route_lifted_gen` are separate parameters.

The context-insensitive run is neither of these: it is `sign_rule`, the
registration of the same assembly at the unit context.

## Why widening buys Sign nothing

The seven-element lattice has finite height, so every ascending chain
stabilises after a bounded number of steps and widening has nothing to
accelerate — a warrowing rule buys no termination that the plain join does not
already give. A caller may still select one: `sign_rule`, `sign_es_rule` and
`sign_cs_rule` take the global update rule as a parameter, so `--globals warrow`
solves and is sound at Sign like every other rule. Parity makes the same
argument; Interval and the Int product are the domains where widening earns its
keep, because their carriers admit unbounded ascending chains.

Global keys differ per policy and are therefore parameters, not a fixed shape.
The call-string run keys at `call_string_gk`, shared with every other
call-string-keyed instance. The entry-state run keys at `routed_gk` —
`Analysis_Global` at `unit`, since Sign publishes no named global of its own,
and `Activation_Seed` carrying a callee entry point with its routed context.
