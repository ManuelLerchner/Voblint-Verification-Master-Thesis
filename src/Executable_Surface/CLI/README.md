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

## What is here

| File | What |
| --- | --- |
| `Analyse_Dispatch.thy` | `analyse`, `analyse_config`, `analyse_config_ctx`, the `analyse_with_solver` comparison surface, and the public soundness corollaries restated over `analyse` |
| `State_Report_GraphViz.thy` | the render entry points: raw CFG DOT, per-node state labels, context-expanded graphs |

The corollaries in `Analyse_Dispatch.thy` are the one kind of soundness statement
that belongs here and nowhere else: a theorem about `analyse` cannot live above the
theory that defines `analyse`, and `analyse` is the constant `export_code` exports.
Each is a `by (rule ...)` restatement of a domain theorem one `analyse.simps`
equation away, so it carries no proof of its own -- only the instantiation that
connects a runtime verdict to the theorem about it.

## Worked example

`--domain interval --context entry-state` reaches `analyse_config_ctx`, which asks
`resolve_analysis_config` for a plan, gets `Plan_Interval_EntryState Solver_Warrow`, and
calls `analyse_interval_entry_state`. The same flags through `analyse_config` return
`None` on purpose — there is no honest flat report for a context-sensitive run. Drop
`--context` and both answer, `analyse_config` with the flat report the CLI prints.
