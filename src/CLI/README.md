# CLI

`Voblint_CLI` is where the domains meet again. Every analysis session below is
deliberately blind to its siblings; the dispatcher cannot be, so this session is
parented on `Voblint_Analysis_Int` and lists the other domain sessions.

That is the whole reason it is a session boundary rather than a folder: anything
importing it sees every domain, so what lives here should be only what genuinely
needs all of them.

## Vocabulary

| Term | Meaning |
| --- | --- |
| entry point | a domain's runtime API paired with its production soundness theorems, over an arbitrary `imp_prog` (`Entry/<Domain>_Entry.thy`) |
| plan | what `resolve_analysis_config` turns a config into: a legal (domain, solver, context) triple, or `None` |
| flat report | `check_report_entry list` — one verdict per check, no contexts |
| contextual report | one verdict per (check, context). Needed because a check can be `Dead` in one context and decided in another, which a flat verdict cannot express. |

## What is here

| File | What |
| --- | --- |
| `Entry/Sign_Entry.thy` | `analyse_sign_report`'s soundness: `run_source_sound`/`collect_sound` applied at Sign, plus worked demo programs |
| `Entry/Interval_Entry.thy` | the Interval counterpart. Production dispatches to the *warrowing* report, which carries its own soundness theorems. |
| `Entry/Parity_Entry.thy` | the Parity counterpart |
| `Entry/Int_Entry.thy` | the `int_dom` counterpart, fixed at `Refine_Fixpoint` |
| `Analyse_Dispatch.thy` | `analyse`, `analyse_config`, `analyse_config_ctx`, the `analyse_with_solver` comparison surface, and the `code_identifier` module map |
| `State_Report_GraphViz.thy` | the render entry points: raw CFG DOT, per-node state labels, context-expanded graphs |

The computation each entry point names lives one session down, in that domain's own
`_Exec_Sound` or `_Checks`. This session adds the theorems, not the definitions.

## The `code_identifier` block is here

`Analyse_Dispatch.thy` carries the map that folds nearly every contributing theory into
one OCaml module, `Core`. **A new theory whose constants are reachable from the export
root must be added to that list**, or `export_code` fails with a module dependency cycle
naming two constants and no theory. `pixi run codegen-modules` turns that into an
immediate, named failure instead. See the repository `AGENTS.md` for the full rule.

## Worked example

`--domain interval --context entry-state` reaches `analyse_config_ctx`, which asks
`resolve_analysis_config` for a plan, gets `Plan_Interval_EntryState Solver_Warrow`, and
calls `analyse_interval_entry_state`. The same flags through `analyse_config` return
`None` on purpose — there is no honest flat report for a context-sensitive run. Drop
`--context` and both answer, `analyse_config` with the flat report the CLI prints.
