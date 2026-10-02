# CLI

`Voblint_CLI` is where the domains meet again. Every analysis session below is
deliberately blind to its siblings; `run_voblint` cannot be, so this session is
parented on `Voblint_Analysis_Int` and lists the other domain sessions.

That is the whole reason it is a session boundary rather than a folder: anything
importing it sees every domain, so what lives here should be only what genuinely
needs all of them.

A domain's own context-free registration is not one of those things. Its
solve, result table and report over an arbitrary `imp_prog`, paired with its
soundness endpoints, depend on that domain and on the shared `Voblint_Result`
locales, never on a sibling, so it lives in that domain's own analysis session
(`sign_rule` in the generated `Sign_Analyses` of `Voblint_Analysis_Sign`, and
so on). What does need all five is the combined run: `MCP_Analyses.thy` runs
every active analysis as a field of one state and proves the combination
sound for any distinct, nonempty activation, citing each active domain's own
`comp_sound` and `init_sound` facts. `run_voblint` reads that combined
registration -- `mcp_rule`, `mcp_es_rule` and `mcp_cs_rule` -- at every
context policy, whatever analyses are activated. What is left here is the
part that really does see all five.

## Vocabulary

| Term | Meaning |
| --- | --- |
| registration | an interpretation of `dg_analysis` at one context policy: its solve, result table and report paired with their soundness endpoints, over an arbitrary `imp_prog`. Each domain owns one context-free registration in its own session, parametric in the global update rule (`sign_rule`, and so on; Interval also keeps its own entry-state and call-string registrations for its example theories). The registrations `run_voblint` actually reads -- `mcp_rule`, `mcp_es_rule`, `mcp_cs_rule` -- run every active analysis at once and are owned here, parametric in the activation list besides. |
| configuration | what a caller chooses: an activation (a nonempty, distinct `analysis_domain list`), a `globals_rule` and a `context_mode`. Every well-formed combination is analysed; an empty activation or one naming an analysis twice is refused (`Invalid_Activation`). |
| global update rule | how the solver merges a value side-effected into a global unknown: joined, joined per origin, warrowed, or warrowed per origin (`globals_rule`). Local unknowns are warrowed at widening points under every rule. |
| flat report | `check_report_entry list` — one verdict per check, no contexts |
| contextual report | one verdict per (check, context). Needed because a check can be `Dead` in one context and decided in another, which a flat verdict cannot express. |
| arithmetic diagnostic | a `/` or `%` occurrence whose divisor is classified as definitely or possibly zero, with its source point and occurrence index |
| analysis report | what `run_voblint` answers: the compiled graph, the contexts, one semantic state per covered (point, context), the contexts each call enters, the check column and the diagnostics. `render_report` turns it into the run result a renderer reads. |
| check label | the `check_label` a source `Check l e` carries onto its `EA_Check l e` edge and its result row. The CLI parser sets it to the line and column of the check's keyword, so a renderer prints a row at its own label rather than pairing rows with parser positions by order. |

## What is here

| File | What |
| --- | --- |
| `Analysis_Config.thy` | `context_mode`, the context-policy selection datatype; `globals_rule` comes from `Voblint_Solver.Globals_Rule`. The analyses a caller may activate are named in the generated `analysis_domain` (below), a plain `analysis_domain list`. |
| `Dispatch_Carrier.thy` | each domain's injective ordering key for listing contexts, and how a field's state is shown; the value union itself is generated into `MCP_Carrier.thy` |
| `Arithmetic_Diagnostics.thy` | arithmetic occurrences, extraction completeness, nonzero-divisor obligations, and structured diagnostics |
| `generated/MCP_Carrier.thy` | generated from `manifests/analyses.yaml`: `analysis_domain`, one field per registered analysis in the combined state, and each analysis's own component, publication map, query and entry-state cases; proves nothing beyond citing each analysis's own registration |
| `MCP_Field.thy` | the two lemmas that turn one analysis's soundness on its own field of the combined state into soundness of that field, and show it leaves every other field alone -- stated once for any field, so the generated carrier only cites them |
| `MCP_Analyses.thy` | runs the active fields as one component, proves the combination sound for any distinct, nonempty activation, and registers it at every context policy: `mcp_rule`, `mcp_es_rule`, `mcp_cs_rule` |
| `Analysis_Run.thy` | `analysis_config`, the semantic `analysis_report`, its builder `report_of`, `analysis_report_of` (the one function that reads the context policy, solving with the executable `solve_c`), and `run_voblint`: one configuration, run once, answering `Invalid_Activation`, `Malformed_Program`, `No_Answer`, or one report. The constant `export_code` exports. |
| `Analysis_Render.thy` | `render_report`: the displayed `run_result` the adapters read, a projection no theorem reads |
| `Analysis_Run_Sound.thy` | what a configuration's table owes its report (`sound_table`), and the context-free table `mcp_rule_table` |
| `Analysis_Run_Ctx_Sound.thy` | the same at the entry-state and call-string tables, `mcp_es_rule_table`, `mcp_cs_rule_table` |
| `Analysis_Report.thy` | the report semantics `⟦res⟧_v`, `verdict_stores`, the CAPS queries and their theorems; `analysis_report_of_sound`, the one proof that splits on the context policy |
| `Analysis_Certified.thy` | the source-level theorems over every configuration `run_voblint` answers, with no termination premise |
| `Trace_Run.thy` | the solver trace in the exported code: traced code equations for routing and `analysis_report_of`, the readers a run hands the tracer, and the OCaml mapping of `trace_event` |

The soundness statements here are the ones that belong nowhere else: a theorem about
`run_voblint` cannot live above the theory that defines it, and `run_voblint` is the
constant `export_code` exports. Each table lemma cites the combined registration's
published facts at an arbitrary activation and rule, so it carries no domain reasoning
of its own -- only the instantiation that connects a runtime answer to the theorem
about it. `Analysis_Certified` carries that connection through to `run_voblint`'s answer.

## Arithmetic diagnostics

`Analysis_Run` fills `res_diagnostics` and each state's `state_diagnostics` from the
same solved result used for checks. Every configuration exposes the states needed
for this query. At each point, the extractor visits
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
under solver termination and an analysed answer, every divisor at a collected
point without diagnostics is nonzero. The theorem uses `res_diagnostics`
directly. Source-position pairing and message rendering remain handwritten
OCaml outside the proof. See the
[main README](../../../README.md#arithmetic-safety-from-an-empty-diagnostic-list)
for the full statement.

## Nothing here draws a picture

`run_voblint` stops at its structured result. The text report, DOT, graph snapshots
and HTML come from `cli/result/` and `cli/render/`, outside any theory and outside any
soundness claim; graph shape is pinned CLI-observably by the golden fixtures under
`tests/regression/11-graph-snapshot/`.

## Why the selection surface is here and not under `Analyses/Shared/`

`analysis_domain`'s constructors are `Sign_Analysis`, `Interval_Analysis`,
`Int_Analysis`, `Parity_Analysis`, `Congruence_Analysis` — it names all five
domains, which is exactly what
the shared layer forbids ("nothing here may mention a concrete domain"). That layer is also an *ancestor*
of every domain session, so keeping it there put a datatype naming `Sign_Analysis`
inside a session `Voblint_Analysis_Sign` inherits from: not a cycle, but upside down.

Nothing under `src/Analyses/` depends on it. Within this session, the generated
`MCP_Carrier` and `MCP_Analyses` case over it field by field to build and run the
combined state; `globals_rule` names no domain, so it lives with the solver in
`Voblint_Solver`.

## Worked example

`voblint --analysis interval --context entry-state FILE.vimp` names no `--globals`,
so `cli/entry/voblint_main.ml` picks `warrow` and calls
`run_voblint (Analysis_Config [Interval_Analysis] Globals_Warrow Ctx_EntryState) p`.
For a well-formed program and a valid activation that is `Analysed res`, the
report `analysis_report_of` builds; the CLI then renders it with
`render_report`. The equation for that cell hands
the solved run of `mcp_es_rule` at `[Interval_Analysis]` and `Globals_Warrow`
to `report_of`, which lists one state per covered
(point, entered argument context), the contexts each call enters, the check
column and the diagnostics. Its soundness is `mcp_es_rule_table` at
`as = [Interval_Analysis]` and `r = Globals_Warrow`, read through
`analysis_report_of_sound` and `run_voblint_source_sound`. `--globals join` changes only the rule
argument, and activating more analyses at once changes only the activation
list; the equation, the builder and the theorem are the same. Naming no
analysis, or the same one twice, answers `Invalid_Activation` instead of
running a solve.
