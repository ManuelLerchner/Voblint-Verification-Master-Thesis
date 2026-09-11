# Interval domain (`ivl`)

The interval domain uses the shared routing, result, and non-relational
interfaces described in [`../Shared/README.md`](../Shared/README.md).
Executable witnesses live under
`src/Examples/Interval/`.

| File | Role |
| --- | --- |
| `Interval_Bounds.thy` | extended integer bounds and bound operations |
| `Interval_Lattice.thy` | interval order, lattice, concretization, and `sound_domain` instance |
| `Interval_Warrowing.thy` | widening/narrowing operators and laws |
| `Interval_Arithmetic.thy` | abstract arithmetic over intervals |
| `Interval_Backward.thy` | backward guard/filter operators; names the interval `afilter_ivl_st`/`bfilter_ivl_st` executable mirror via `Exec_Backward` |
| `Interval_Transfer.thy` | edge transfer record and transfer soundness |
| `Interval_Domain.thy` | aggregate import façade and small domain demonstrations |
| `Interval_Exec.thy` | executable transfer mirror + commutation |
| `Interval_Special.thy` | the abstract implementation of the `Min`/`Max` special calls |
| `Interval_Numeric_Queries.thy` | Interval's instance of `abstract_numeric_queries` |
| `Interval_Point_Digest.thy` | the point abstraction: a slot is a point when it is a singleton interval |
| `Interval_Sound.thy` | the `dg_spec` Interval supplies, its concretization, and `sound_dg_spec_core` — no context, no solver |
| `Interval_Exec_Sound.thy` | raw unbuffered computation for an arbitrary VIMP program; no production soundness |
| `generated/Interval_Assembly.thy` | the context-insensitive route, as four interpretations of the shared `unit_dg_analysis` — one per update rule, with the lemmas proving all four solve the same system. Generated |
| `generated/Interval_Contextual_Assembly.thy` | the call-string and entry-state routed configurations, each registered at all four disciplines with Apinis warrowing as the default. Generated from `assembly/analyses.yaml`; see below |
| `Interval_Analyses.thy` | the presentation routing this domain publishes on top of them — the one part of Interval's contextual surface that is not derivable |
| `Interval_Solver_Analyses.thy` | the verdict reports of those two contextual configurations at the always-join, per-origin and warrowing-per-origin disciplines |
| `Interval_Classify.thy` | Interval instance of the generic check-discharge interface |
| `generated/Interval_Checks.thy` | the public result tables and check reports, bound to the assembly's four instances. Generated |
| `generated/Interval_Entry.thy` | the production endpoint: `analyse_interval_report` over an arbitrary `imp_prog`, and its soundness theorems — `run_source_sound`/`collect_sound` (`Voblint_Soundness`) applied at Interval. Generated |

## The two contextual configurations, and the one hand-written part

Interval is the one domain whose contextual surface does not generate
completely. `generated/Interval_Contextual_Assembly.thy` holds the
registrations -- both contexts, each at all four disciplines -- and the
call-string published constants, machine-written from `assembly/analyses.yaml`.
The first discipline listed for a context owns its unsuffixed binder, so the
generator refuses a list whose first entry is not the context's default. `Interval_Analyses.thy` survives as a hand-written
file because Interval publishes presentation routing on top of them — reading a
callee's context back out of a solved entry-state table — and that is not
derivable from registration data and should not be.

The mechanism is uniform across all five domains: every domain's contextual
registrations are generated. What differs is only whether the domain has
hand-written content left to host beside them. Interval does; Sign, Parity,
Congruence and Int do not, so for those four the generated theory carries the
`<Domain>_Analyses` name outright.

Neither contextual policy has a pipeline of its own. Both are interpretations
of `routed_dg_analysis`, which owns the equation system, the solve, the covered
keys, the reader, the result table, the contextual report and the
activation-indexed soundness endpoint.

A call string is the last `k` call sites on the stack. `cs_route` never reads
the state it is handed, which is what makes `fun_route_activation_collect_sound`
the applicable endpoint, and `k` being runtime data is why that registration
lives inside a `context fixes k` rather than a `global_interpretation`.

The entry-state run keys a callee on the abstract values its formals hold on
entry. `exec_formals_route` does read the state it is handed, so
`entry_state_activation_collect_sound` applies instead — its admitted-context
relation is the one the entry answer induces rather than the graph of a
function on stores. Interval's bottom-sensitive handling of that entry state,
and the covered-versus-uncovered distinction the result table draws, are
properties of the shared assembly rather than of this domain.

The context-insensitive run is neither of these: it is `Interval_Assembly`'s
`global_interpretation` of the same assembly at the unit context, at Apinis
warrowing, which is Interval's production default because always-join has no
termination guarantee on this lattice.
