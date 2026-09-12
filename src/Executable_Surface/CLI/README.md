# CLI

`Voblint_CLI` is where the domains meet again. Every analysis session below is
deliberately blind to its siblings; the dispatcher cannot be, so this session is
parented on `Voblint_Analysis_Int` and lists the other domain sessions.

That is the whole reason it is a session boundary rather than a folder: anything
importing it sees every domain, so what lives here should be only what genuinely
needs all of them.

Soundness is not one of those things. Each domain's entry point -- its runtime
API over an arbitrary `imp_prog`, paired with its production soundness theorems
-- depends on that domain and on the shared `Voblint_Result` endpoints, never on
a sibling, so it
lives in that domain's own analysis session (`Sign_Entry` in
`Voblint_Analysis_Sign`, and so on). What is left here is the part that really
does see all five.

## Vocabulary

| Term | Meaning |
| --- | --- |
| entry point | a domain's runtime API paired with its production soundness theorems, over an arbitrary `imp_prog`. Owned by the domain session, not this one. |
| plan | what `resolve_analysis_config` turns a config into: a legal (domain, solver, context) triple, or `None` |
| flat report | `check_report_entry list` — one verdict per check, no contexts |
| contextual report | one verdict per (check, context). Needed because a check can be `Dead` in one context and decided in another, which a flat verdict cannot express. |
| arithmetic diagnostic | a `/` or `%` occurrence whose divisor is classified as definitely or possibly zero, with its source point and occurrence index |
| context-expanded graph | one node per (program point, context) pair rather than one per point --- the only way a context-sensitive result is visible at all |
| `export_graph` | the neutral hand-off: clusters, nodes and edges, each with a kind and a status, and no colour, shape or label markup. What the OCaml renderers consume. |

## What is here

| File | What |
| --- | --- |
| `Analysis_Config.thy` | `analysis_config` (domain/solver/context selection) and the `analysis_plan` a configuration resolves to |
| `generated/Config_Tables.thy` | the resolver's support matrix: `resolve_analysis_config` and `valid_analysis_config` derived from it. Generated from `manifests/analyses.yaml`. |
| `generated/Dispatch_Tables.thy` | `analyse_with_solver`, the per-domain solver-discipline table, with its default-pairing lemmas. Generated from `manifests/analyses.yaml`. |
| `Dispatch_Carrier.thy` | one value type wide enough for every domain's state-carrying report |
| `Analyse_Dispatch.thy` | `analyse` and the public soundness corollaries restated over it |
| `Dispatch_Config.thy` | config-driven dispatch: `analyse_config`, `analyse_config_ctx`, `analyse_config_with_state` |
| `Analysis_Graph.thy` | the graph vocabulary: cluster/node/edge datatypes, the config record of caller hooks, node status and annotation, and the chosen context ordering |
| `Analysis_Graph_Build.thy` | `build_analysis_graph`: a solved result becomes clusters, nodes and routed edges |
| `Analysis_Graph_Wf.thy` | that what it builds is always well-formed --- distinct nodes, every edge between nodes that exist. The one theorem in the graph layer. |
| `Analysis_Graph_Naming.thy` | positional identifiers for nodes and clusters, plus the call-string context presentation |
| `Analysis_Graph_Export.thy` | the three readings handed out: canonical text snapshot, `export_graph`, check-report listing. The single import point for the four above. |
| `State_Report_Graph.thy` | the entry points that pair a solved run with a graph: per-node state labels, context-expanded graphs, check annotations |
| `State_Report_Entry_Ctx.thy`, `State_Report_Call_String.thy` | the context-expanded entry-state and call-string graphs |
| `Arithmetic_Diagnostics.thy` | arithmetic occurrences, extraction completeness, nonzero-divisor obligations, and structured diagnostics |
| `Analysis_Run.thy` | `run_voblint`: one configuration, run once, answering every view from one solve. The constant `export_code` exports. |
| `Analysis_Run_Sound.thy` | what a run proves about a run of the program, at the context-free configurations |
| `Analysis_Run_Ctx_Sound.thy` | the same at the entry-state and call-string configurations |
| `Analysis_Run_Solver_Sound.thy` | the same at an explicitly chosen solver discipline |
| `Analysis_Certified.thy` | one soundness statement over every configuration the CLI answers |

The hand-written configuration and dispatch matrices are regression theories,
so they live in `src/Examples/CLI/` rather than this production session.

The soundness statements here are the ones that belong nowhere else: a theorem about
`analyse` or `run_voblint` cannot live above the theory that defines it, and
`run_voblint` is the constant `export_code` exports. The corollaries in
`Analyse_Dispatch.thy` are each a `by (rule ...)` restatement of a domain theorem one
`analyse.simps` equation away, so they carry no proof of their own -- only the
instantiation that connects a runtime verdict to the theorem about it. The
`Analysis_Run_*` theories and `Analysis_Certified` carry that connection through to
`run_voblint`'s answer.

## Arithmetic diagnostics

`Analysis_Run` adds `out_diagnostics` to `analysis_output`, computed from the same
solved result used for checks and graph views. Every supported configuration
exposes the states needed for this query. At each point, the extractor visits
expressions on intra-edges and call edges: assignments, guards, arguments,
returns, special calls, and checks. It suppresses a matching `AssumeNot` guard
when the corresponding `Assume` edge already supplies that expression, while
retaining repeated arithmetic occurrences within an expression.

The extractor visits both operands of `&&` and `||`; it introduces no separate
short-circuit evaluation convention. Each obligation tests whether its divisor
differs from zero. Contextual runs classify each represented context before
aggregating: mixed safe and zero verdicts become possible warnings. Safe and
unreachable results produce no diagnostic.

The CLI renders `Check_Refuted` as `error` and `Check_Unknown` as `warning`, with
the containing statement's source position and the domain name. Neither verdict
establishes concrete reachability. The plain text report contains separate arithmetic and
assertion tables. Graph and HTML commands print messages to stderr, and HTML
also includes source-linked findings for each domain in a combined report;
they do not stop analysis or change its exit code.

`Analysis_Certified.run_voblint_arithmetic_safe` states the high-level contract:
under solver termination and an accepted answer, every divisor at a collected
point without diagnostics is nonzero. The theorem uses `out_diagnostics`
directly. Source-position pairing and message rendering remain handwritten
OCaml outside the proof. See the
[main README](../../../README.md#arithmetic-safety-from-an-empty-diagnostic-list)
for the full statement.

## Why the graph layer is here and not under `Analyses/Shared/`

`Analyses/Shared/`'s contract is what every concrete domain reuses. No domain uses
the graph layer and the graph layer uses nothing domain-specific, so placing it there
would put an island under a description that does not describe it. Its consumers are
the `State_Report_*` theories and `Analysis_Run` beside it here. Domain witnesses
cannot see this session, so graph shape is pinned CLI-observably by the golden
fixtures under `tests/regression/11-graph-snapshot/`.

Nothing here draws a picture. Isabelle stops at `export_graph`; DOT and HTML come
from `cli/dot_render.ml` and `cli/html_report.ml`, outside any theory and outside
any soundness claim.

## Why the selection surface is here and not under `Analyses/Shared/`

`analysis_domain`'s constructors are `Sign_Analysis`, `Interval_Analysis`,
`Int_Analysis`, `Parity_Analysis`, `Congruence_Analysis` — it names all five
domains, which is exactly what
the shared layer forbids ("nothing here may mention a concrete domain"). That layer is also an *ancestor*
of every domain session, so keeping it there put a datatype naming `Sign_Analysis`
inside a session `Voblint_Analysis_Sign` inherits from: not a cycle, but upside down.

Nothing under `src/Analyses/` ever depended on it. Deciding which (domain, solver,
context) triples are legal is the dispatcher's own contract, and `Analyse_Dispatch` is
the only theory that acts on it.

## Worked example

`--analysis interval --context entry-state` reaches `analyse_config_ctx`, which asks
`resolve_analysis_config` for a plan, gets `Plan_Interval_EntryState Solver_Warrow`, and
calls `analyse_interval_entry_state`. The same flags through `analyse_config` return
`None` on purpose — there is no honest flat report for a context-sensitive run. Drop
`--context` and both answer, `analyse_config` with the flat report the CLI prints.
