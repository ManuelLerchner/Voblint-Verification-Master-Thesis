# Interval domain (`ivl`)

The interval domain uses the shared routing, result, and non-relational
interfaces described in [`../Shared/README.md`](../Shared/README.md).
Executable witnesses live under
`src/Examples/Interval/`.

| File | Role |
| --- | --- |
| `Interval_Lattice.thy` | lives in `Voblint_Domain` (`src/Abstract_Interpreter/Domain/Int/`): bounds, order, lattice, and concretization |
| `Interval_Warrowing.thy` | widening/narrowing operators and laws, then the `numeric_domain` instance, which needs them |
| `Interval_Arithmetic.thy` | abstract arithmetic over intervals |
| `Interval_Backward.thy` | inverse operators, `ivl_refine_ops`, and the `mono_refinement` certificate |
| `Interval_Transfer.thy` | the `ivl_ops` bundle and its one `mono_nonrelational_ops` interpretation, which derives the filters, branch, check classifier and transfer |
| `Interval_Domain.thy` | aggregate import façade and small domain demonstrations |
| `Interval_Exec.thy` | executable transfer mirror + commutation |
| `Interval_Special.thy` | the abstract implementation of the `Min`/`Max` special calls |
| `Interval_Numeric_Queries.thy` | Interval's instance of `sound_numeric_queries` |
| `Interval_Point_Digest.thy` | the point abstraction: a slot is a point when it is a singleton interval |
| `Interval_Sound.thy` | the `dg_spec` Interval supplies, its concretization, and `analysis_contract` — no context, no solver |
| `Interval_Classify.thy` | executable tests of the derived check classifier |
| `generated/Interval_Analyses.thy` | three `global_interpretation`s, each taking the global update rule `r` as a parameter: `interval_rule`, `interval_es_rule` and `interval_cs_rule`, each of the shared `dg_analysis_exec`, at the unit, entry-state and call-string contexts. Generated from `manifests/analyses.yaml`; see below |

## The contextual configurations

`generated/Interval_Analyses.thy` is machine-written from
`manifests/analyses.yaml`, so the orientation a reader needs lives here rather
than in a header the generator owns. The registry spells Interval's constants
with the `ivl` prefix (`ivl_tf_st_for`, `cinit_ivl_st`) while the registrations,
the classifier and the initial-state fact carry the domain name
(`interval_rule`, `interval_classify_check`, `interval_cinit_gamma`).

Neither contextual policy has a pipeline of its own. Both are interpretations
of `dg_analysis`, which owns the equation system, the solve, the covered
keys, the reader, the result table, the contextual report and the
activation-indexed soundness endpoint.

A call string is the last `k` call sites on the stack. `cs_route` never reads
the state it is handed, which is what makes `fun_route_activation_collect_sound`
the applicable endpoint, and `k` being runtime data is why that registration
leaves it free beside the rule (`for k r`).

The entry-state run keys a callee on the abstract values its formals hold on
entry. `exec_formals_route` does read the state it is handed, so
`entry_state_activation_collect_sound` applies instead — its admitted-context
relation is the one the entry answer induces rather than the graph of a
function on stores. Interval's bottom-sensitive handling of that entry state,
and the covered-versus-uncovered distinction the result table draws, are
properties of the shared assembly rather than of this domain.

The context-insensitive run is neither of these: it is `interval_rule`, the
registration of the same assembly at the unit context. Every registration takes
the rule as a parameter, and on this lattice the rule matters: the solver warrows
local unknowns under every rule, but a global side-effected around a loop can climb an
unbounded chain unless the rule warrows it too, as the CLI's default
`Globals_Warrow` (Apinis warrowing) does.
