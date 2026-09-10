# CLI

`Voblint_CLI` is where the domains meet again. Every analysis session below is
deliberately blind to its siblings; the dispatcher cannot be, so this session is
parented on `Voblint_Analysis_Int` and lists the other domain sessions.

That is the whole reason it is a session boundary rather than a folder: anything
importing it sees every domain, so what lives here should be only what genuinely
needs all of them.

Soundness is not one of those things. Each domain's entry point -- its runtime
API over an arbitrary `imp_prog`, paired with its production soundness theorems
-- depends on that domain and on `Voblint_Soundness`, never on a sibling, so it
lives in that domain's own analysis session (`Sign_Entry` in
`Voblint_Analysis_Sign`, and so on). What is left here is the part that really
does see all four.

## Vocabulary

| Term | Meaning |
| --- | --- |
| entry point | a domain's runtime API paired with its production soundness theorems, over an arbitrary `imp_prog`. Owned by the domain session, not this one. |
| plan | what `resolve_analysis_config` turns a config into: a legal (domain, solver, context) triple, or `None` |
| flat report | `check_report_entry list` — one verdict per check, no contexts |
| contextual report | one verdict per (check, context). Needed because a check can be `Dead` in one context and decided in another, which a flat verdict cannot express. |
| context-expanded graph | one node per (program point, context) pair rather than one per point --- the only way a context-sensitive result is visible at all |
| `export_graph` | the neutral hand-off: clusters, nodes and edges, each with a kind and a status, and no colour, shape or label markup. What the OCaml renderers consume. |

## What is here

| File | What |
| --- | --- |
| `Analysis_Config.thy` | `analysis_config` (domain/solver/context selection), the canonical `resolve_analysis_config` legality-and-defaults resolver, and `valid_analysis_config` derived from it |
| `Analyse_Dispatch.thy` | `analyse`, `analyse_config`, `analyse_config_ctx`, the `analyse_with_solver` comparison surface, and the public soundness corollaries restated over `analyse` |
| `Analysis_Graph.thy` | the graph vocabulary: cluster/node/edge datatypes, the config record of caller hooks, node status and annotation, and the chosen context ordering |
| `Analysis_Graph_Build.thy` | `build_analysis_graph`: a solved result becomes clusters, nodes and routed edges |
| `Analysis_Graph_Wf.thy` | that what it builds is always well-formed --- distinct nodes, every edge between nodes that exist. The one theorem in the graph layer. |
| `Analysis_Graph_Naming.thy` | positional identifiers for nodes and clusters, plus the call-string context presentation |
| `Analysis_Graph_Export.thy` | the three readings handed out: canonical text snapshot, `export_graph`, check-report listing. The single import point for the four above. |
| `State_Report_Graph.thy` | the entry points that pair a solved run with a graph: per-node state labels, context-expanded graphs, check annotations |

The corollaries in `Analyse_Dispatch.thy` are the one kind of soundness statement
that belongs here and nowhere else: a theorem about `analyse` cannot live above the
theory that defines `analyse`, and `analyse` is the constant `export_code` exports.
Each is a `by (rule ...)` restatement of a domain theorem one `analyse.simps`
equation away, so it carries no proof of its own -- only the instantiation that
connects a runtime verdict to the theorem about it.

## Why the graph layer is here and not under `Analyses/Shared/`

It used to live in the session then called `Voblint_Analysis_Base` (now split into
`Analyses/Shared/`), whose contract is what every concrete domain reuses. No domain ever imported it --- not Sign, Interval, Int, Parity or
Relational --- and it imported nothing from Base either, so it sat there as an island
under a description that did not describe it.

Its real consumers are the two theories beside it here. Nothing forced the old
placement: `Voblint_Exec` already sees all seven of its imports. What kept it below
the domains was three Interval witnesses asserting graph structure from inside
`Voblint_Examples_Interval`, which cannot see this session. Those assertions were
dropped --- the graph shape they pinned is covered CLI-observably by the golden
fixtures under `tests/regression/11-graph-snapshot/`, and the soundness theorems
in those files are untouched.

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

`--domain interval --context entry-state` reaches `analyse_config_ctx`, which asks
`resolve_analysis_config` for a plan, gets `Plan_Interval_EntryState Solver_Warrow`, and
calls `analyse_interval_entry_state`. The same flags through `analyse_config` return
`None` on purpose — there is no honest flat report for a context-sensitive run. Drop
`--context` and both answer, `analyse_config` with the flat report the CLI prints.
