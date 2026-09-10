# Sign domain — 7-element sign lattice

The concrete sign domain uses the shared routing, result, and non-relational
interfaces described in [`../Shared/README.md`](../Shared/README.md).
Executable witnesses live under `src/Examples/Sign/`;
they demonstrate the domain, they are not part of the reusable instance.

| File | Role |
| --- | --- |
| `Sign_Lattice.thy` | 7-element sign lattice, order operations, concretization, and `sound_domain` instance |
| `Sign_Arithmetic.thy` | abstract arithmetic over signs |
| `Sign_Backward.thy` | backward guard/filter operators; names the sign `afilter_sign_st`/`bfilter_sign_st` executable mirror via `Exec_Backward` |
| `Sign_Special.thy` | `sign_min`/`sign_max`, the abstract implementation of the `Min`/`Max` special calls |
| `Sign_Numeric_Queries.thy` | Sign's instance of `abstract_numeric_queries` |
| `Sign_Transfer.thy` | edge transfer record and transfer soundness |
| `Sign_Exec.thy` | executable transfer mirror + `tf_st_commute` commutation |
| `Sign_Sound.thy` | the `dg_spec` Sign supplies, its concretization, and `sound_dg_spec_core` — no context, no solver |
| `Sign_Classify.thy` | Sign instance of the generic check-discharge interface |
| `Sign_Assembly.thy` | one `global_interpretation` of the shared `unit_dg_analysis`: Sign's transfer, entry state, always-join solver and classifier go in; the equation system, the solve, the reader, the result table, the report and every soundness endpoint come out |
| `generated/Sign_Analyses.thy` | the call-string and entry-state routed configurations — the two the assembly does not cover, because each routes calls to more than one context. Generated from `assembly/analyses.yaml`; see below |
| `Sign_Checks.thy` | the public runtime API: bindings onto the assembly, plus the per-origin solver sibling |
| `Sign_Entry.thy` | the production endpoint: `analyse_sign_report` over an arbitrary `imp_prog`, and its soundness theorems — `run_source_sound`/`collect_sound` (`Voblint_Soundness`) applied at Sign |

`Sign_Entry` is what `analyse` dispatches to, and it lives here rather than in
`Voblint_CLI` because nothing in it needs to see another domain: it depends on
Sign and on `Voblint_Soundness`, both of which this session already has. The
dispatcher restates its theorems over `analyse`; it does not prove them.

## The two contextual configurations

`generated/Sign_Analyses.thy` is machine-written, so the orientation a reader
needs lives here rather than in a header the generator owns.

Neither contextual policy has a pipeline of its own. Both are interpretations
of `routed_dg_analysis`, which owns the equation system, the solve, the covered
keys, the reader, the result table, the contextual report and the
activation-indexed soundness endpoint — for every domain at every policy. Sign
supplies its own implementation and facts, the routing functions, the solver,
and the published names. Nothing else.

A call string is the last `k` call sites on the stack, so a procedure entered
from two places is analysed twice rather than once at the join. `cs_route`
never reads the state it is handed, which is what makes
`fun_route_activation_collect_sound` — the endpoint for a route that is a
function of the call site and the caller's context alone — the applicable one.
`k` is runtime data, so no `global_interpretation` can fix it: the registration
is local to a context fixing `k`, and the published constants apply the
pipeline's own constants at `cs_route k`.

The entry-state run keys a callee on the abstract values its formals hold on
entry. Here `exec_formals_route` does read the state it is handed — the callee
frame the routed generator has already entered — so the applicable endpoint is
`entry_state_activation_collect_sound`, whose admitted-context relation is the
one the entry answer induces rather than the graph of a function on stores.
That difference is the whole content of the routing-agreement obligation, and
it is why the executable route and its abstract counterpart
`formals_route_lifted_gen` are separate parameters.

The context-insensitive run is neither of these: it is `Sign_Assembly`'s
`global_interpretation` of the same assembly at the unit context.

## Why Sign publishes no warrowing discipline

Sign publishes `Solver_Join` and `Solver_PerOrigin`, and no warrowing route at
either the unit or a contextual context. The seven-element lattice has finite
height, so every ascending chain stabilises after a bounded number of steps and
widening has nothing to accelerate — a warrowing rule would be mechanically
available and would buy no termination that the plain join does not already
give. The resolver follows proved capability, so it answers `None` there rather
than offering a route with no solved table or soundness corollary behind it.
This is the same reasoning Parity records for its own two disciplines; Interval
and the Int product are the domains where widening earns its keep, because
their carriers admit unbounded ascending chains.

Global keys differ per policy and are therefore parameters, not a fixed shape.
The call-string run keys at `call_string_gk`, shared with every other
call-string-keyed instance. The entry-state run keys at `routed_gk` —
`Analysis_Global` at `unit`, since Sign publishes no named global of its own,
and `Activation_Seed` carrying a callee entry point with its routed context.
