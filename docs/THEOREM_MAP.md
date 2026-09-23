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
| A returning executable solve yields a post-solution | [`Voblint_Solver.TD_Solver_Bridge:TD_side_upd_rule.solve_dom_of_solve_c`](../src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy), [`TD.TD_side_upd_rule:TD_side_upd_rule.partial_post_solution`](../vendor/td-verification/TD_side_upd_rule.thy) | `solve_dom_of_solve_c` turns `solve_c x ≠ None` into `solve_dom x`; the vendored `partial_post_solution` turns `solve_dom x` into `part_post_solution` for `solve x`. Every domain registration discharges the two solver assumptions of `routed_dg_analysis` with exactly these facts (`TD_side_rule_Interp.*`), and `run_voblint`'s termination premise is `solve_dom`. The composite `TD_side_upd_rule.part_post_solution_of_solve_c` is cited only by two Sign examples. |
| A terminating routed solve bounds every activation at a functional route | [`Voblint_Result.Routed_Live_Keys:routed_dg_analysis.fun_route_activation_collect_sound_of_terminates`](../src/Analyses/Shared/Result/Routed_Live_Keys.thy) | Combines solver correctness, executable readback, and routed D/G soundness without exposing transport details to clients; coverage is derived from termination, not assumed. |
| The computed analysis result bounds every modeled source run | [`Voblint_Result.Unit_DG_Analysis:unit_dg_analysis.result_node_sound_of_terminates`](../src/Analyses/Shared/Result/Unit_DG_Analysis.thy), [`Voblint_Result.Unit_DG_Analysis:unit_dg_analysis.source_sound`](../src/Analyses/Shared/Result/Unit_DG_Analysis.thy) | The context-insensitive endpoints, stated once over the published `state_at`; every domain's unit route is an instance. |
| A routed solve bounds every activation its context policy admits | [`Voblint_Result.Routed_DG_Analysis:routed_dg_analysis.entry_state_activation_collect_sound`](../src/Analyses/Shared/Result/Routed_DG_Analysis.thy), [`Voblint_Result.Routed_DG_Analysis:routed_dg_analysis.fun_route_activation_collect_sound`](../src/Analyses/Shared/Result/Routed_DG_Analysis.thy) | The entry-state and call-string endpoints every domain re-exports. Each bounds `activation_collect` at one context, against the solved reader; neither mentions `ltr_collect` or a source run. |
| Every valid trace carries a context the policy admits | [`Voblint_Result.Routed_DG_Analysis:routed_dg_analysis.entry_state_has_context`](../src/Analyses/Shared/Result/Routed_DG_Analysis.thy) | Supplies the witness a caller needs before a per-context bound says anything about a given run. |
| The solved reader and the published result table describe the same stores | [`Voblint_Result.Routed_DG_Analysis:routed_dg_analysis.gamma_reader_eq_lookup`](../src/Analyses/Shared/Result/Routed_DG_Analysis.thy) | Rewrites a reader-shaped bound into `lookup_context` of the table a caller reads, with no coverage premise. |
| The context buckets exhaust the context-insensitive collector | [`Voblint_CFG.LTR_Collect:ltr_collect_eq_Union_activation_of_has_context`](../src/Program_Model/CFG/Collecting/LTR_Collect.thy), [`Voblint_CFG.LTR_Collect:ltr_collect_eq_Union_activation_of_fun`](../src/Program_Model/CFG/Collecting/LTR_Collect.thy), [`Voblint_CFG.LTR_Abstract:ltr_coverage.ltr_collect_eq_Union_activation_collect`](../src/Program_Model/CFG/Collecting/LTR_Abstract.thy) | Unconditional for a functional route such as call strings; earned from context totality for a relational one. |
| A per-context bound extends to arbitrary source executions | [`Voblint_Result.Source_Activation_Sound:source_sound_from_collecting_cap`](../src/Analyses/Shared/Result/Source_Activation_Sound.thy) | Domain-free and policy-free: it consumes an `activation_collect` bound and a context witness. `source_activation_sound` in the same theory instantiates it generically, and [`Voblint_Examples_Interval.Example_Interval_Source_Ctx:twice_source_ctx_run_sound`](../src/Examples/Interval/Ctx/Example_Interval_Source_Ctx.thy) for one fixed program. |
| Every configuration's result is sound at every collected store | [`Voblint_CLI.Analysis_Certified:analysis_result_sound`](../src/Executable_Surface/CLI/Analysis_Certified.thy), [`Voblint_CLI.Analysis_Certified:run_voblint_sound_at`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | Over `config_terminates D rule ctx p`, so for every domain, global update rule and context policy: at a store `ltr_collect` admits at a point, the table covers it (`analysis_result_covers`), no check listed there is dead, every decided one holds, and a point without a diagnostic divides by no zero. The first states it over the typed `analysis_result`, the second over `run_voblint`, the one operation code generation exports. |
| The same, at a context-sensitive configuration | [`Voblint_CLI.Analysis_Run_Sound:sound_table_of_activation`](../src/Executable_Surface/CLI/Analysis_Run_Sound.thy), [`Voblint_CLI.Analysis_Run_Sound:sound_table.source_sound`](../src/Executable_Surface/CLI/Analysis_Run_Sound.thy) | Stated once over an arbitrary context policy: the first turns a routed bound on every `activation_collect` bucket into a `sound_table`, the second places a source run in it; each domain and policy instantiates the pair in one `*_table` lemma. The store sits in the table entry filed under at least one context its own call history is admitted at -- exactly one for a call string, possibly several under entry-state routing -- and quantifying over every solved context would be false. |
| Any accepted configuration's answer over-approximates the concrete run | [`Voblint_CLI.Analysis_Certified:run_voblint_certified_source_sound`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | The headline: the domain, global update rule and context policy are arguments, and every combination is answered. Well-formedness is not a premise, since a malformed program answers `Malformed_Program`; termination is, as `config_terminates`. |
| A run about to execute a check finds a sound listed check for it | [`Voblint_CLI.Analysis_Certified:run_voblint_check_sound`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | The reader-facing form of the headline, with no `csim` in the statement. The check is existential and sits at a node the store reaches; it cannot be unique, since a source state does not determine its node. |
| The result lists one check per compiled check | [`Voblint_CLI.Analysis_Certified:run_voblint_check_sites`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | At every configuration, the checks' `(check_point, check_exp)` pairs are the `EA_Check` edges of the compiled graph, in graph order. Pairing checks with source positions is done by `cli/render/render_text.ml` and is not proved. |
| A listed check is correct at the node it was listed for | [`Voblint_CLI.Analysis_Run_Sound:ctx_checks_sound_at`](../src/Executable_Surface/CLI/Analysis_Run_Sound.thy) | The endpoint's check claim without the source run, so the node is the caller's rather than the simulation's. What a caller supplies instead is a store the collecting semantics admits there. |
| That headline is non-vacuous | [`Voblint_Examples.Example_End_To_End_Certificate:certificate_demo_source_certified`](../src/Examples/Capstone/Example_End_To_End_Certificate.thy) | One program at `Int` + `Ctx_CallString 1` + `Globals_Join`. `certificate_demo_full_certificate` names every witness the generic theorem leaves existential: the returned answer, its single `PROVED` check, the completed source run, the collecting-semantics membership at `Statement 4`, `analysis_result_covers` and `checks_sound_at` there, and the check's own truth. Well-formedness, termination, coverage and the answer are discharged by evaluation. |

The `run_voblint` rows prove partial correctness. Solver termination remains an
explicit per-program premise; parsing, code
generation, the OCaml compiler, and the handwritten CLI are outside the proved
chain.

The two axes run equally far. Context-free is complete for all five domains at
every global update rule, through each domain's generated `<d>_rule`
registration of `unit_dg_analysis`: `report_proved_sound`/`report_refuted_sound`
conclude over `ltr_collect`, and `source_sound`/`completed_run_sound` place a
source run's store in the published state `state_at gs p v`, the table's entry
at `lookup_context ... v ()`. Under `Ctx_EntryState` and
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

`run_voblint` takes a domain, a global update rule and a context policy. A
program that fails the well-formedness check answers `Malformed_Program` before
any configuration is consulted; every other combination is check-producing.
`analysis_result` hands the table of the domain's rule-parametric registration to
`unit_run_result`, `entry_state_run_result` or `call_string_run_result`, so
`res_checks` is `result_checks_of (classify_checks_verdicts ...)` and the
endpoint's check argument applies: 5 domains x 4 rules x 3 context policies, the
call string at every bound `k`, `k = 0` included.

Every combination carries the source-level theorem. Each (domain, context policy)
pair is one `*_table` lemma over an arbitrary rule `r`, instantiating
`sound_table`: the unit ones (`sign_rule_table`, ...) in
[`Voblint_CLI.Analysis_Run_Sound`](../src/Executable_Surface/CLI/Analysis_Run_Sound.thy)
through `sound_table_of_unit`, whose per-node bound each `<d>_rule` registration
supplies as a `unit_dg_analysis` instance; the contextual ones
(`sign_es_rule_table`, `sign_cs_rule_table`, ...) in
[`Voblint_CLI.Analysis_Run_Ctx_Sound`](../src/Executable_Surface/CLI/Analysis_Run_Ctx_Sound.thy)
through `sound_table_of_activation`. `entry_state_run_result_sound` and
`call_string_run_result_sound` then cover every contextual combination without
a separate bridge.

## Dead checks

| Claim | Theorem | Note |
| --- | --- | --- |
| A dead check means nothing reaches that point | [`Voblint_CLI.Analysis_Certified:run_voblint_dead_check_unreached`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | Over `config_terminates`, so at every configuration. Per-node and universal over stores, so it does not follow from the endpoint by contraposition -- that one is existential in its CFG witness. |
| Contextual coverage is decidable | [`Voblint_Framework.CFG_Enumeration:ctx_vars_cover_of_exec`](../src/Abstract_Interpreter/Framework/Constraints/CFG_Enumeration.thy) | Walks the solved keys against the two edge enumerations; sufficient, not equivalent, like its unit counterpart. |
| A terminating solve is closed along live dependencies | [`Voblint_Result.Routed_Live_Keys:routed_dg_analysis.live_keys_cover`](../src/Analyses/Shared/Result/Routed_Live_Keys.thy) | Needs well-formedness and termination only. States `ctx_vars_cover_live` over `live_keys`, the solved keys whose node reaches a solved procedure result; code after a `return` is solved but never read, so the unrestricted key set is not closed. |
