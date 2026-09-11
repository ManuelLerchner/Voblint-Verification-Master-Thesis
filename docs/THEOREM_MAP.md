# Theorem map

This page maps the main pipeline claims to their checked Isabelle statements.
The theory and theorem names were verified against the theory sources on
2026-09-10. Definitions remain authoritative in the linked theories.

Two axes run through the table and are easy to conflate. The *domain* axis is
covered uniformly: every claim below that names a domain holds for all five.
The *context* axis is not, and the closing note says where it stops.

| Claim | Checked statement | Role |
| --- | --- | --- |
| Accepted source programs satisfy the procedural source contract | [`Voblint_VIMP.VIMP_Proc:wf_source_programD`](../src/Program_Model/VIMP/VIMP_Proc.thy) | Exposes the reserved return variable, declared argument-free `main`, well-formed procedure bodies, return discipline, and source-language restrictions. |
| Executable compiler inputs satisfy that source contract and enumerate procedures correctly | [`Voblint_Compile.Compile_Invariants:wf_compile_inputD`](../src/Program_Model/Compile/Compile_Invariants.thy) | Adds distinct, complete procedure enumeration to `wf_source_program`. |
| Source execution is simulated by the compiled CFG | [`Voblint_Compile.Simulation_Preservation:csim_step`](../src/Program_Model/Compile/Simulation/Simulation_Preservation.thy), [`Voblint_Compile.Simulation_Preservation:csim_star`](../src/Program_Model/Compile/Simulation/Simulation_Preservation.thy) | Preserves the located source/CFG relation for one step and for a complete finite run. |
| Every accepted source run has a valid activation-local trace | [`Voblint_Compile.Source_To_Trace:source_run_has_ltr`](../src/Program_Model/Compile/Source_To_Trace.thy) | Connects a source run, its simulated CFG location, and a `valid_ltr` witness. |
| `ltr_collect` contains exactly stores witnessed by valid local traces | [`Voblint_CFG.LTR_Collect:ltr_collect_I`](../src/Program_Model/CFG/Collecting/LTR_Collect.thy), [`Voblint_CFG.LTR_Collect:ltr_collect_E`](../src/Program_Model/CFG/Collecting/LTR_Collect.thy) | Introduction and elimination rules for the context-insensitive collector. |
| A semantic post-fixpoint covers the activation-local collecting semantics | [`Voblint_CFG.LTR_Abstract:ltr_collect_semantic_postfix`](../src/Program_Model/CFG/Collecting/LTR_Abstract.thy) | Turns the entry, edge, call and combine closure of a node map into an `ltr_collect` bound. |
| Context-indexed D/G post-solutions cover every admitted activation | [`Voblint_Framework.Routed_Context:routed_context_base_hetero.activation_collect_dg_sound`](../src/Abstract_Interpreter/Framework/Context/Routed_Context.thy) | Discharges the five activation obligations from one routed D/G `part_post_solution`. |
| Successful verified TD solving yields the post-solution consumed by the framework | [`Voblint_Solver.TD_Solver_Bridge:TD_side_upd_rule.part_post_solution_of_solve_c`](../src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy) | Bridges executable `solve_c` success to the vendored solver's `part_post_solution`. |
| A terminating routed solve bounds every activation at a functional route | [`Voblint_Result.Routed_Live_Keys:routed_dg_analysis.fun_route_activation_collect_sound_of_terminates`](../src/Analyses/Shared/Result/Routed_Live_Keys.thy) | Combines solver correctness, executable readback, and routed D/G soundness without exposing transport details to clients; coverage is derived from termination, not assumed. |
| The computed analysis result bounds every modeled source run | [`Voblint_Result.Unit_DG_Analysis:unit_dg_analysis.result_node_sound_of_terminates`](../src/Analyses/Shared/Result/Unit_DG_Analysis.thy), [`Voblint_Result.Unit_DG_Analysis:unit_dg_analysis.source_sound`](../src/Analyses/Shared/Result/Unit_DG_Analysis.thy) | The context-insensitive endpoints, stated once over the published `state_at`; every domain's unit route is an instance. |
| A routed solve bounds every activation its context policy admits | [`Voblint_Result.Routed_DG_Analysis:routed_dg_analysis.entry_state_activation_collect_sound`](../src/Analyses/Shared/Result/Routed_DG_Analysis.thy), [`Voblint_Result.Routed_DG_Analysis:routed_dg_analysis.fun_route_activation_collect_sound`](../src/Analyses/Shared/Result/Routed_DG_Analysis.thy) | The entry-state and call-string endpoints every domain re-exports. Each bounds `activation_collect` at one context, against the solved reader; neither mentions `ltr_collect` or a source run. |
| Every valid trace carries a context the policy admits | [`Voblint_Result.Routed_DG_Analysis:routed_dg_analysis.entry_state_has_context`](../src/Analyses/Shared/Result/Routed_DG_Analysis.thy) | Supplies the witness a caller needs before a per-context bound says anything about a given run. |
| The solved reader and the published result table describe the same stores | [`Voblint_Result.Routed_DG_Analysis:routed_dg_analysis.gamma_reader_eq_lookup`](../src/Analyses/Shared/Result/Routed_DG_Analysis.thy) | Rewrites a reader-shaped bound into `lookup_context` of the table a caller reads, with no coverage premise. |
| The context buckets exhaust the context-insensitive collector | [`Voblint_CFG.LTR_Collect:ltr_collect_eq_Union_activation_of_has_context`](../src/Program_Model/CFG/Collecting/LTR_Collect.thy), [`Voblint_CFG.LTR_Collect:ltr_collect_eq_Union_activation_of_fun`](../src/Program_Model/CFG/Collecting/LTR_Collect.thy), [`Voblint_CFG.LTR_Abstract:ltr_coverage.ltr_collect_eq_Union_activation_collect`](../src/Program_Model/CFG/Collecting/LTR_Abstract.thy) | Unconditional for a functional route such as call strings; earned from context totality for a relational one. |
| A per-context bound extends to arbitrary source executions | [`Voblint_Result.Source_Activation_Sound:source_sound_from_collecting_cap`](../src/Analyses/Shared/Result/Source_Activation_Sound.thy) | Domain-free and policy-free: it consumes an `activation_collect` bound and a context witness. `source_activation_sound` in the same theory instantiates it generically, and [`Voblint_Examples_Interval.Example_Interval_Source_Ctx:twice_source_ctx_run_sound`](../src/Examples/Interval/Ctx/Example_Interval_Source_Ctx.thy) for one fixed program. |
| The runtime dispatcher preserves each domain's proved and refuted verdicts | [`Voblint_CLI.Analyse_Dispatch:analyse_proved_sound`](../src/Executable_Surface/CLI/Analyse_Dispatch.thy), [`Voblint_CLI.Analyse_Dispatch:analyse_refuted_sound`](../src/Executable_Surface/CLI/Analyse_Dispatch.thy) | Covers all five selectable domains through the exported `analyse` function, which takes a domain and a program and no context. |
| A certified dispatcher result is sound along arbitrary source executions | [`Voblint_CLI.Analyse_Dispatch:analyse_source_sound`](../src/Executable_Surface/CLI/Analyse_Dispatch.thy) | The verdict-list layer beneath the entry point, at the unit context `analyse_certified` names a solve for. |
| A certified run of the exported entry point over-approximates the concrete run | [`Voblint_CLI.Analysis_Certified:run_voblint_source_sound`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | Endpoint over `run_voblint`, the one operation code generation exports, at `Ctx_None` and the default discipline: the abstract state at the reached node contains the concrete store, no rendered check row there is a dead marker, and every decided one holds. |
| The same, at a context-sensitive configuration | [`Voblint_CLI.Analysis_Run_Sound:sound_table_of_activation`](../src/Executable_Surface/CLI/Analysis_Run_Sound.thy), [`Voblint_CLI.Analysis_Run_Sound:sound_table.source_sound`](../src/Executable_Surface/CLI/Analysis_Run_Sound.thy) | Stated once over an arbitrary context policy: the first turns a routed bound on every `activation_collect` bucket into a `sound_table`, the second places a source run in it; each domain and policy instantiates the pair in one `*_table` lemma. The store sits in the table entry filed under at least one context its own call history is admitted at -- exactly one for a call string, possibly several under entry-state routing -- and quantifying over every solved context would be false. |
| Any accepted configuration's answer over-approximates the concrete run | [`Voblint_CLI.Analysis_Certified:run_voblint_certified_source_sound`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | The headline: the domain, solver discipline and context policy are arguments. Legality and well-formedness are not premises, since an unsupported pairing answers `Unsupported_Configuration` and a malformed program `Malformed_Program`. |
| A run about to execute a check finds a sound printed row for it | [`Voblint_CLI.Analysis_Certified:run_voblint_check_sound`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | The reader-facing form of the headline, with no `csim` in the statement. The row is existential and sits at a node the store reaches; it cannot be unique, since a source state does not determine its node. |
| The report has one row per compiled check | [`Voblint_CLI.Analysis_Certified:run_voblint_check_sites`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | At every configuration, the rows' `(row_point, row_exp)` pairs are the `EA_Check` edges of the compiled graph, in graph order. Pairing rows with source positions is done by `cli/main.ml` and is not proved. |
| A printed row is correct at the node it was printed for | [`Voblint_CLI.Analysis_Run_Sound:ctx_rows_sound_at`](../src/Executable_Surface/CLI/Analysis_Run_Sound.thy) | The endpoint's row claim without the source run, so the node is the caller's rather than the simulation's. What a caller supplies instead is a store the collecting semantics admits there. |
| That headline is non-vacuous | [`Voblint_Examples.Example_End_To_End_Certificate:certificate_demo_source_certified`](../src/Examples/Capstone/Example_End_To_End_Certificate.thy) | One program at `Int` + `Ctx_CallString 1` + explicit `Solver_Join`. `certificate_demo_full_certificate` names every witness the generic theorem leaves existential: the returned answer, its single `PROVED` row, the completed source run, the collecting-semantics membership at `Statement 4`, `analysis_result_covers` and `checks_sound_at` there, and the check's own truth. Well-formedness, termination, coverage and the answer are discharged by evaluation. |

The `analyse` and `run_voblint` rows prove partial correctness. Solver termination and
required key coverage remain explicit per-program premises; parsing, code
generation, the OCaml compiler, and the handwritten CLI are outside the proved
chain.

The two axes now run equally far. Context-free is complete for all five domains
in each `<Domain>_Entry` theory: `analyse_<domain>_report_sound_proved`/`_refuted`
conclude over `ltr_collect`, and
`analyse_<domain>_source_sound`/`_completed_run_sound` place a source run's store
in the published table at `lookup_context ... v ()`. Under `Ctx_EntryState` and
`Ctx_CallString` the same reaches a source run through
`sound_table_of_activation` and `sound_table.source_sound`, which together close
the three gaps the per-context bound left: it names a context the run's own call history is admitted at rather than
an arbitrary one, reads the published table rather than the solved reader, and
starts from a source execution. What each policy owes is a termination fact; the
coverage the proof reads follows from it.

The asymmetry that remains is precision of statement, not coverage. A contextual
endpoint is existential in the context: the store sits in at least one bucket its
call history is admitted at -- exactly one for a call string, possibly several for
the relational entry-state routing -- while a statement over every context the
node was solved at would be false.

## Configuration coverage of the source-level endpoint

`run_voblint` takes a domain, an optional solver and a context policy. Not every
combination is a candidate for the source-level theorem, and the reason differs
per cell. A program that fails the well-formedness check answers
`Malformed_Program` before any configuration is consulted; beyond that, two
outcomes exist.

**Row-producing** -- the answer is built by `flat_output_of`,
`entry_state_output_of` or `cs_output_of`, so `out_checks` is
`check_rows_of ... (classify_checks_verdicts ...)` and the endpoint's row
argument applies. 32 configurations:

| Context | Sign | Parity | Congruence | Interval | Int |
| --- | --- | --- | --- | --- | --- |
| `Ctx_None` | Join*, PerOrigin+ | Join*, PerOrigin+ | Join*, PerOrigin+ | Warrow*, Join+, PerOrigin+, WPO+ | Warrow*, Join+, PerOrigin+, WPO+ |
| `Ctx_EntryState` | Join* | Join* | Join* | Warrow*, Join+, PerOrigin+, WPO+ | Warrow*, Join+ |
| `Ctx_CallString k` | Join* | Join* | Join* | Warrow*, Join+, PerOrigin+, WPO+ | Warrow*, Join+ |

`*` marks the discipline `None` selects; `+` marks a cell reached only by naming
a solver. Every one of the 32 carries the source-level theorem. Each cell is one
`*_table` lemma instantiating `sound_table`: the unit cells through
`sound_table_of_unit`, whose per-node bound each alternate discipline supplies
from its own `unit_dg_analysis` registration, the contextual ones through
`sound_table_of_activation`.

The contextual cells at a named discipline live in
[`Voblint_CLI.Analysis_Run_Solver_Sound`](../src/Executable_Surface/CLI/Analysis_Run_Solver_Sound.thy),
those at each policy's default in
[`Voblint_CLI.Analysis_Run_Ctx_Sound`](../src/Executable_Surface/CLI/Analysis_Run_Ctx_Sound.thy).
The split is by discipline, not by argument: the two files prove the same thing
and the first imports the second.

Six of them reach the endpoint by a different presentation. Interval at `Join`,
`PerOrigin` and `WarrowPerOrigin` under either context policy routes to
`verdict_report_answer`, which looks like a different output path but is not: its
argument is a `(pp * exp * contextual_verdict) list`, and each of the six is
`routed_dg_pipeline.verdict_report`, which is *defined* as
`classify_checks_verdicts (prog_cfg p) (result gs p) classify`. Point, check
expression and verdict all survive, so the rows are exactly what the contextual
endpoint reads; `out_checks_of_verdict_report_answer` is the one-line bridge that
says so.

**Rejected** -- every remaining combination answers
`Unsupported_Configuration`, and there is nothing to prove.

Nothing row-producing remains. Closing the last six was registry and generator
work -- widen Interval's contextual solver lists, name the per-discipline
re-exports, regenerate -- followed by six ordinary instantiations.

## Dead rows

| Claim | Theorem | Note |
| --- | --- | --- |
| A dead row means nothing reaches that point | [`Voblint_CLI.Analysis_Certified:run_voblint_dead_row_unreached`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | Over `config_terminates`, so at every configuration. Per-node and universal over stores, so it does not follow from the endpoint by contraposition -- that one is existential in its CFG witness. |
| Contextual coverage is decidable | [`Voblint_Framework.CFG_Enumeration:ctx_vars_cover_of_exec`](../src/Abstract_Interpreter/Framework/Constraints/CFG_Enumeration.thy) | Walks the solved keys against the two edge enumerations; sufficient, not equivalent, like its unit counterpart. |
| A terminating solve is closed along live dependencies | [`Voblint_Result.Routed_Live_Keys:routed_dg_analysis.live_keys_cover`](../src/Analyses/Shared/Result/Routed_Live_Keys.thy) | Needs well-formedness and termination only. States `ctx_vars_cover_live` over `live_keys`, the solved keys whose node reaches a solved procedure result; code after a `return` is solved but never read, so the unrestricted key set is not closed. |
