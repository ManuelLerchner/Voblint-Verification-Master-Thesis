# CLI

`Voblint_CLI` is where the domains meet again. Every analysis session below is
deliberately blind to its siblings; `run_voblint` cannot be, so this session is
parented on `Voblint_Analysis_Int` and lists the other domain sessions.

That is the whole reason it is a session boundary rather than a folder: anything
importing it sees every domain, so what lives here should be only what genuinely
needs all of them.

Soundness is not one of those things. Each domain's registrations -- the
solve, result table and report over an arbitrary `imp_prog`, paired with their
soundness endpoints -- depend on that domain and on the shared `Voblint_Result`
locales, never on a sibling, so they live in that domain's own analysis session
(`sign_rule`, `sign_es_rule` and `sign_cs_rule` in the generated `Sign_Analyses`
of `Voblint_Analysis_Sign`, and so on). What is left here is the part that
really does see all five.

## Vocabulary

| Term | Meaning |
| --- | --- |
| registration | a domain's interpretation of `unit_dg_analysis` or `routed_dg_analysis` at one context policy, with the global update rule as a parameter: its solve, result table and report paired with their soundness endpoints, over an arbitrary `imp_prog`. Owned by the domain session, not this one. |
| configuration | what a caller chooses: an `analysis_domain`, a `globals_rule` and a `context_mode`. Every combination is analysed; there is no default and no refused pairing. |
| global update rule | how the solver merges a value side-effected into a global unknown: joined, joined per origin, warrowed, or warrowed per origin (`globals_rule`). Local unknowns are warrowed at widening points under every rule. |
| flat report | `check_report_entry list` — one verdict per check, no contexts |
| contextual report | one verdict per (check, context). Needed because a check can be `Dead` in one context and decided in another, which a flat verdict cannot express. |
| arithmetic diagnostic | a `/` or `%` occurrence whose divisor is classified as definitely or possibly zero, with its source point and occurrence index |
| run result | what `run_voblint` answers: the compiled graph, the contexts, one state per covered (point, context), the contexts each call enters, the check column and the diagnostics. Everything a renderer reads. |

## What is here

| File | What |
| --- | --- |
| `Analysis_Config.thy` | `analysis_domain` and `context_mode`, the two selection datatypes that name domains and context policies; `globals_rule` comes from `Voblint_Solver.Globals_Rule` |
| `Dispatch_Carrier.thy` | one value type wide enough for every domain's abstract values, and an injective ordering key for listing contexts |
| `Arithmetic_Diagnostics.thy` | arithmetic occurrences, extraction completeness, nonzero-divisor obligations, and structured diagnostics |
| `Analysis_Run.thy` | `analysis_result`, one equation per domain and context policy over the rule-parametric registrations, and `run_voblint`: one configuration, run once, answering one structured result from one solve. The constant `export_code` exports. |
| `Analysis_Run_Sound.thy` | what a result's check column proves about a run of the program, and the context-free tables `sign_rule_table`, ... |
| `Analysis_Run_Ctx_Sound.thy` | the same at the entry-state and call-string tables, `sign_es_rule_table`, `sign_cs_rule_table`, ... |
| `Analysis_Certified.thy` | one soundness statement over every configuration `run_voblint` answers |

The soundness statements here are the ones that belong nowhere else: a theorem about
`run_voblint` cannot live above the theory that defines it, and `run_voblint` is the
constant `export_code` exports. Each table lemma cites one domain registration's
published facts at an arbitrary rule, so it carries no domain reasoning of its own --
only the instantiation that connects a runtime answer to the theorem about it.
`Analysis_Certified` carries that connection through to `run_voblint`'s answer.

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

Nothing under `src/Analyses/` depends on it: `analysis_result` in `Analysis_Run` is
the only definition that cases on it. `globals_rule` names no domain, so it lives with
the solver in `Voblint_Solver`.

## Worked example

`voblint --analysis interval --context entry-state FILE.vimp` names no `--globals`,
so `cli/entry/voblint.ml` picks `warrow` and calls
`run_voblint Interval_Analysis Globals_Warrow Ctx_EntryState p`. For a well-formed
program that is `Analysed (analysis_result Interval_Analysis Globals_Warrow
Ctx_EntryState p)`, with every abstract value rendered to a string. The equation
for that cell hands `interval_es_rule.result Globals_Warrow (declared_global p) p`
to `entry_state_run_result`, which lists one state per covered (point, entered
argument context), the contexts each call enters, the check column and the
diagnostics. Its soundness is `interval_es_rule_table` at `r = Globals_Warrow`,
read through `run_voblint_certified_source_sound`. `--globals join` changes only
the rule argument; the equation, the builder and the theorem are the same.
