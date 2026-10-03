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
| Every accepted source run has a valid activation trace | [`Voblint_Compile.Source_To_Trace:source_run_has_activation_trace`](../src/Program_Model/Compile/Source_To_Trace.thy) | Connects a source run, its simulated CFG location, and a `valid_activation_trace` witness. |
| `node_collect` contains exactly stores witnessed by valid activation traces | [`Voblint_CFG.Activation_Trace_Collect:node_collect_I`](../src/Program_Model/CFG/Collecting/Activation_Trace_Collect.thy), [`Voblint_CFG.Activation_Trace_Collect:node_collect_E`](../src/Program_Model/CFG/Collecting/Activation_Trace_Collect.thy) | Introduction and elimination rules for the context-insensitive collector. |
| A semantic post-fixpoint covers the activation-trace collecting semantics | [`Voblint_CFG.Activation_Trace_Abstract:node_collect_semantic_postfix`](../src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy) | Turns the entry, edge, call and combine closure of a node map into an `node_collect` bound. |
| Context-indexed D/G post-solutions cover every admitted activation | [`Voblint_Framework.Routed_Context:routed_context.activation_collect_dg_sound`](../src/Abstract_Interpreter/Framework/Context/Routed_Context.thy) | Discharges the five activation obligations from one routed D/G `part_post_solution`. |
| A returning executable solve yields a post-solution | [`Voblint_Solver.TD_Solver_Bridge:TD_side_upd_rule.solve_dom_of_solve_c`](../src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy), [`TD.TD_side_upd_rule:TD_side_upd_rule.partial_post_solution`](../vendor/td-verification/TD_side_upd_rule.thy), [`Voblint_Solver.Globals_Rule:td_certified_solver`](../src/Abstract_Interpreter/Solver/Globals_Rule.thy) | `solve_dom_of_solve_c` turns `solve_c x ≠ None` into `solve_dom x`; the vendored `partial_post_solution` turns `solve_dom x` into `part_post_solution` for `solve x`. With `finite_stabl_solve` they make the solver a `certified_solver`, the solver contract `dg_analysis` extends; `td_certified_solver` proves it once for every `globals_rule`, every registration, per domain and combined, cites that one fact, and `run_voblint`'s termination premise is `solve_dom`. The composite `TD_side_upd_rule.part_post_solution_of_solve_c` is cited only by two Sign examples. |
| A terminating routed solve bounds every activation at a functional route | [`Voblint_Result.DG_Live_Unknowns:dg_analysis.fun_route_activation_collect_sound_of_terminates`](../src/Analyses/Shared/Result/DG_Live_Unknowns.thy) | Combines solver correctness, the executable carrier's represented functions, and routed D/G soundness without exposing transport details to clients; coverage is derived from termination, not assumed. |
| The computed analysis result bounds every modeled source run | [`Voblint_Result.DG_Live_Unknowns:dg_analysis.fun_route_result_node_sound`](../src/Analyses/Shared/Result/DG_Live_Unknowns.thy), [`Voblint_Result.DG_Live_Unknowns:dg_analysis.fun_route_source_sound`](../src/Analyses/Shared/Result/DG_Live_Unknowns.thy) | The endpoints for a route that is a function of the call site, stated once over the published `state_at` at a context; every domain's unit registration is an instance, at the one context `()`. |
| A routed solve bounds every activation its context policy admits | [`Voblint_Result.DG_Analysis:dg_analysis.entry_state_activation_collect_sound`](../src/Analyses/Shared/Result/DG_Analysis.thy), [`Voblint_Result.DG_Analysis:dg_analysis.fun_route_activation_collect_sound`](../src/Analyses/Shared/Result/DG_Analysis.thy) | The entry-state and call-string endpoints every domain re-exports. Each bounds `activation_collect` at one context, against the solved reader; neither mentions `node_collect` or a source run. |
| Every valid activation trace carries a context the policy admits | [`Voblint_Result.DG_Analysis:dg_analysis.entry_state_has_context`](../src/Analyses/Shared/Result/DG_Analysis.thy) | Supplies the witness a caller needs before a per-context bound says anything about a given run. |
| The solved reader and the published result table describe the same stores | [`Voblint_Result.DG_Analysis:dg_analysis.gamma_reader_eq_lookup`](../src/Analyses/Shared/Result/DG_Analysis.thy) | Rewrites a reader-shaped bound into `lookup_table` of the table a caller reads, with no coverage premise. |
| The context buckets exhaust the context-insensitive collector | [`Voblint_CFG.Activation_Trace_Collect:node_collect_eq_Union_activation_of_has_context`](../src/Program_Model/CFG/Collecting/Activation_Trace_Collect.thy), [`Voblint_CFG.Activation_Trace_Collect:node_collect_eq_Union_activation_of_fun`](../src/Program_Model/CFG/Collecting/Activation_Trace_Collect.thy), [`Voblint_CFG.Activation_Trace_Abstract:activation_coverage.node_collect_eq_Union_activation_collect`](../src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy) | Unconditional for a functional route such as call strings; earned from context totality for a relational one. |
| A per-context bound extends to arbitrary source executions | [`Voblint_Result.Source_Activation_Sound:source_sound_from_collecting_cap`](../src/Analyses/Shared/Result/Source_Activation_Sound.thy) | Domain-free and policy-free: it consumes an `activation_collect` bound and a context witness. `source_activation_sound` in the same theory instantiates it generically, and [`Voblint_Examples_Interval.Example_Interval_Source_Ctx:twice_source_ctx_run_sound`](../src/Examples/Interval/Ctx/Example_Interval_Source_Ctx.thy) for one fixed program. |
| Every report run_voblint returns is sound | [`Voblint_CLI.Analysis_Report:analysis_report_of_sound`](../src/Executable_Surface/CLI/Analysis_Report.thy), [`Voblint_CLI.Analysis_Certified:run_voblint_covers`](../src/Executable_Surface/CLI/Analysis_Certified.thy), [`Voblint_CLI.Analysis_Certified:run_voblint_collect_sound`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | For every activation list, global update rule and context policy, with no termination premise: the report is consistent, `𝒞 v ⊆ ⟦res⟧⇘v⇙ ⊆ 𝒱⇘res⇙ v`, and a point without a diagnostic divides by no zero. The first is the one proof that splits on the context policy. |
| An analysed report's contract in one statement | [`Voblint_CLI.Analysis_Certified:run_voblint_report_contract`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | `valid_config config`, `wf_program_compile_input_exec p`, `report_config res = config`, `report_cfg res = prog_cfg p`, `well_formed_report res` and `sound_report p res` for every `Analysed res`. |
| The semantic spine, once for every policy | [`Voblint_CLI.Analysis_Certified:run_voblint_spine`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | Given that every valid activation trace carries a context and the buckets are the collecting semantics: a source run's trace `t` and its context `c` with `s ∈ 𝒜(v, c)`, `⋃c'. 𝒜(v, c') = 𝒞 v ⊆ ⟦res⟧⇘v⇙ ⊆ 𝒱⇘res⇙ v`. The three policy chains instantiate it. |
| A consistent report's verdicts hold in its own semantics | [`Voblint_CLI.Analysis_Report:analysis_report_verdicts_sound`](../src/Executable_Surface/CLI/Analysis_Report.thy), [`Voblint_CLI.Analysis_Report:analysis_report_dead`](../src/Executable_Surface/CLI/Analysis_Report.thy) | `⟦res⟧⇘v⇙ ⊆ 𝒱⇘res⇙ v`, and `DEAD res v ⟹ ⟦res⟧⇘v⇙ = ∅`, from the report alone. The converse of the second does not hold: the product's emptiness test is sound and incomplete. |
| Which emptiness tests are exact and which only sound | [`Voblint_Domain.Abstract_Domain:exact_emptiness_is_empty`](../src/Abstract_Interpreter/Domain/Lattice/Abstract_Domain.thy), [`Voblint_Exec.Default_St_Reachability:exact_emptiness_default_st_is_bot_for`](../src/Abstract_Interpreter/Exec/State/Default_St_Reachability.thy), [`Voblint_CLI.MCP_Analyses:mcp_empty_v_not_exact`](../src/Executable_Surface/CLI/MCP_Analyses.thy), [`Voblint_CLI.Analysis_Report:sound_emptiness_DEAD`](../src/Executable_Surface/CLI/Analysis_Report.thy), [`Voblint_CLI.Analysis_Report:DEAD_not_exact`](../src/Executable_Surface/CLI/Analysis_Report.thy) | A domain's, a state's and the executable carrier's tests are exact (`e x ⟷ γ x = {}`). The combined state's test is only sound, with a witness: Interval says `x = 2`, Parity that `x` is odd. So `DEAD` is a sound emptiness test on report points and not an exact one: a report whose only state at a point is that contradiction describes no store there and is not `DEAD`. |
| Every analysed report is well-formed | [`Voblint_CLI.Analysis_Certified:run_voblint_well_formed`](../src/Executable_Surface/CLI/Analysis_Certified.thy), [`Voblint_CLI.Analysis_Report:well_formed_check_verdict`](../src/Executable_Surface/CLI/Analysis_Report.thy) | Context indices in range, one row per `(point, context)`, each row's check and obligation columns exactly the checks and arithmetic obligations at its point, with verdicts computed from its own state; with consistency, a check's verdict aggregates the rows' verdicts. Not needed for soundness. |
| The same, at a context-sensitive configuration | [`Voblint_CLI.Analysis_Run_Sound:covered_table_of_activation`](../src/Executable_Surface/CLI/Analysis_Run_Sound.thy), [`Voblint_CLI.Analysis_Report:report_of_sound`](../src/Executable_Surface/CLI/Analysis_Report.thy) | Stated once over an arbitrary context policy: the first turns a routed bound on every `activation_collect` bucket into a `covered_table`, the second turns a covered table and the sound classifier into a sound report; each policy instantiates the first in one `*_table` lemma. The store sits in the table entry filed under at least one context its own call history is admitted at -- exactly one for a call string, possibly several under entry-state routing -- and quantifying over every solved context would be false. |
| Any accepted configuration's answer over-approximates the concrete run | [`Voblint_CLI.Analysis_Certified:run_voblint_source_sound`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | The headline: the configuration is an argument, and every combination is answered. Neither well-formedness nor termination is a premise: a malformed program answers `Malformed_Program`, an invalid list `Invalid_Activation`, and an analysed answer exists only where the executable solve returned. |
| A run about to execute a check finds a sound listed check for it | [`Voblint_CLI.Analysis_Certified:run_voblint_check_sound`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | The reader-facing form of the headline, with no `csim` in the statement. The check is existential and sits at a node the store reaches; it cannot be unique, since a source state does not determine its node. |
| The result lists one check per compiled check | [`Voblint_CLI.Analysis_Certified:run_voblint_check_sites`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | At every configuration, the checks' `(check_point, check_exp)` pairs are the `EA_Check` edges of the compiled graph, in graph order. Pairing checks with source positions is done by `cli/render/render_text.ml` and is not proved. |
| A definite verdict holds at every collected store | [`Voblint_CLI.Analysis_Certified:run_voblint_proved`](../src/Executable_Surface/CLI/Analysis_Certified.thy), [`Voblint_CLI.Analysis_Certified:run_voblint_refuted`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | The check claim without the source run, so the node is the caller's rather than the simulation's. |
| That headline is non-vacuous | [`Voblint_Examples.Example_End_To_End_Certificate:certificate_demo_source_certified`](../src/Examples/Capstone/Example_End_To_End_Certificate.thy) | One program at `Int` + `Ctx_CallString 1` + `Globals_Join`. `certificate_demo_full_certificate` names every witness the generic theorem leaves existential: the returned answer, its single `PROVED` check, the completed source run, the collecting-semantics membership at `Statement 4`, membership in `⟦res⟧⇘v⇙` and `𝒱⇘res⇙ v` there, and the check's own truth. Well-formedness and the answer are discharged by evaluation. |

The `run_voblint` rows prove partial correctness. Solver termination is not
proved; an answer exists only where the solve returned; parsing, code
generation, the OCaml compiler, and the handwritten CLI are outside the proved
chain.

The two axes run equally far. Context-free is complete for all five domains at
every global update rule, through each domain's generated `<d>_rule`
registration of `dg_analysis_exec` at the unit route:
`fun_route_report_proved_sound`/`fun_route_report_refuted_sound` conclude over
the activation-indexed collector, which `activation_collect_unit_eq_node_collect`
identifies with `node_collect` at `()`, and `fun_route_source_sound` places a
source run's store in the published state `state_at gs p () v`, the table's entry
at `lookup_table ... v ()`. Under `Ctx_EntryState` and
`Ctx_CallString` the same reaches a source run through
`covered_table_of_activation` and `report_of_sound`, which together close
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

`run_voblint` takes an activation list, a global update rule, a context
policy and a placement of program globals. An activation list that is empty or repeats an analysis answers
`Invalid_Activation`; a program that fails the well-formedness check answers
`Malformed_Program`. Every other combination is check-producing.
`solved_table` hands the table of the combined state's rule-parametric
registration for the chosen policy and placement (`mcp_rule`, `mcp_es_rule`,
`mcp_cs_rule`, or their flow-insensitive counterparts `mcp_split_rule`,
`mcp_split_es_rule`, `mcp_split_cs_rule`)
to `run_result_of`, so `res_checks` is `result_checks_of (classify_checks_verdicts ...)`
and the endpoint's check argument applies: every distinct nonempty list over the
6 analyses x 5 rules x 3 context policies x 2 placements, the call string at every bound `k`,
`k = 0` included.

Every combination carries the source-level theorem. Each context policy is one
`*_table` lemma over an arbitrary activation list `as` and rule `r`,
instantiating `covered_table` through `covered_table_of_activation`: `mcp_rule_table`
in
[`Voblint_CLI.Analysis_Run_Sound`](../src/Executable_Surface/CLI/Analysis_Run_Sound.thy),
`mcp_es_rule_table` and `mcp_cs_rule_table` in
[`Voblint_CLI.Analysis_Run_Ctx_Sound`](../src/Executable_Surface/CLI/Analysis_Run_Ctx_Sound.thy).
Checks are classified by `mcp_classify`, which is `answer_check` applied to the
met answer of the active analyses to the check's `EvalInt` query; its soundness,
`mcp_sound_classifier`, does not depend on the table and is proved once.

## Dead checks

| Claim | Theorem | Note |
| --- | --- | --- |
| A dead check means nothing reaches that point | [`Voblint_CLI.Analysis_Certified:run_voblint_dead_check_unreached`](../src/Executable_Surface/CLI/Analysis_Certified.thy) | At every configuration, with no termination premise. Per-node and universal over stores, so it does not follow from the endpoint by contraposition -- that one is existential in its CFG witness. |
| Contextual coverage is decidable | [`Voblint_Framework.CFG_Enumeration:ctx_vars_cover_of_exec`](../src/Abstract_Interpreter/Framework/Constraints/CFG_Enumeration.thy) | Walks the solved keys against the two edge enumerations; sufficient, not equivalent, like its unit counterpart. |
| A terminating solve is closed along live dependencies | [`Voblint_Result.DG_Live_Unknowns:dg_analysis.live_unknowns_cover`](../src/Analyses/Shared/Result/DG_Live_Unknowns.thy) | Needs well-formedness and termination only. States `ctx_vars_cover_live` over `live_unknowns`, the solved keys whose node reaches a solved procedure result; code after a `return` is solved but never read, so the unrestricted key set is not closed. |
