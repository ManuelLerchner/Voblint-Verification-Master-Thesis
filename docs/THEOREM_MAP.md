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
| A semantic post-fixpoint covers the activation-local collecting semantics | [`Voblint_CFG.LTR_Abstract:ltr_collect_semantic_postfix`](../src/Program_Model/CFG/Collecting/LTR_Abstract.thy) | Converts the entry, edge, call, return, and finiteness obligations into an `ltr_collect` bound. |
| Context-indexed D/G post-solutions cover every admitted activation | [`Voblint_Framework.Routed_Context:activation_collect_dg_sound`](../src/Abstract_Interpreter/Framework/Context/Routed_Context.thy) | Discharges the five activation obligations from one routed D/G `part_post_solution`. |
| Successful verified TD solving yields the post-solution consumed by the framework | [`Voblint_Solver.TD_Solver_Bridge:TD_side_upd_rule.part_post_solution_of_solve_c`](../src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy) | Bridges executable `solve_c` success to the vendored solver's `part_post_solution`. |
| A solved executable D/G system supplies the unit-context soundness interface | [`Voblint_Soundness.Run_Analysis_Sound:ownership_split_dg_exec_analysis.unit_routed_context_of_solve`](../src/Soundness/Run_Analysis_Sound.thy) | Combines solver correctness, executable readback, and routed D/G soundness without exposing transport details to clients. |
| The computed analysis result bounds every modeled source run | [`Voblint_Soundness.Run_Analysis_Sound:ownership_split_dg_exec_analysis.run_source_sound`](../src/Soundness/Run_Analysis_Sound.thy), [`Voblint_Soundness.Run_Analysis_Sound:local_state_dg_exec_analysis.run_source_sound`](../src/Soundness/Run_Analysis_Sound.thy) | Source-facing endpoints for the ownership-split and local-state executable carriers. |
| A routed solve bounds every activation its context policy admits | [`Voblint_Result.Routed_DG_Analysis:routed_dg_analysis.entry_state_activation_collect_sound`](../src/Analyses/Shared/Result/Routed_DG_Analysis.thy), [`Voblint_Result.Routed_DG_Analysis:routed_dg_analysis.fun_route_activation_collect_sound`](../src/Analyses/Shared/Result/Routed_DG_Analysis.thy) | The entry-state and call-string endpoints every domain re-exports. Each bounds `activation_collect` at one context, against the solved reader; neither mentions `ltr_collect` or a source run. |
| Every valid trace carries a context the policy admits | [`Voblint_Result.Routed_DG_Analysis:routed_dg_analysis.entry_state_has_context`](../src/Analyses/Shared/Result/Routed_DG_Analysis.thy) | Supplies the witness a caller needs before a per-context bound says anything about a given run. |
| The solved reader and the published result table describe the same stores | [`Voblint_Result.Routed_DG_Analysis:routed_dg_analysis.gamma_reader_eq_lookup`](../src/Analyses/Shared/Result/Routed_DG_Analysis.thy) | Rewrites a reader-shaped bound into `lookup_context` of the table a caller reads, with no coverage premise. |
| The context buckets exhaust the context-insensitive collector | [`Voblint_CFG.LTR_Collect:ltr_collect_eq_Union_activation_of_has_context`](../src/Program_Model/CFG/Collecting/LTR_Collect.thy), [`Voblint_CFG.LTR_Collect:ltr_collect_eq_Union_activation_of_fun`](../src/Program_Model/CFG/Collecting/LTR_Collect.thy), [`Voblint_CFG.LTR_Abstract:ltr_coverage.ltr_collect_eq_Union_activation_collect`](../src/Program_Model/CFG/Collecting/LTR_Abstract.thy) | Unconditional for a functional route such as call strings; earned from context totality for a relational one. |
| A per-context bound extends to arbitrary source executions | [`Voblint_Soundness.Source_Activation_Sound:source_sound_from_collecting_cap`](../src/Soundness/Source_Activation_Sound.thy) | Domain-free and policy-free: it consumes an `activation_collect` bound and a context witness. Its only instance is one fixed program, [`Voblint_Examples_Interval.Example_Interval_Source_Ctx:twice_source_ctx_run_sound`](../src/Examples/Interval/Ctx/Example_Interval_Source_Ctx.thy). |
| The runtime dispatcher preserves each domain's proved and refuted verdicts | [`Voblint_CLI.Analyse_Dispatch:analyse_proved_sound`](../src/Executable_Surface/CLI/Analyse_Dispatch.thy), [`Voblint_CLI.Analyse_Dispatch:analyse_refuted_sound`](../src/Executable_Surface/CLI/Analyse_Dispatch.thy) | Covers all five selectable domains through the exported `analyse` function, which takes a domain and a program and no context. |
| A certified dispatcher result is sound along arbitrary source executions | [`Voblint_CLI.Analyse_Dispatch:analyse_source_sound`](../src/Executable_Surface/CLI/Analyse_Dispatch.thy) | The verdict-list layer beneath the entry point, at the unit context `analyse_certified` names a solve for. |
| A certified run of the exported entry point over-approximates the concrete run | [`Voblint_CLI.Analysis_Run_Sound:run_voblint_source_sound`](../src/Executable_Surface/CLI/Analysis_Run_Sound.thy) | Endpoint over `run_voblint`, the one operation code generation exports: the abstract state at the reached node contains the concrete store, and every rendered check row there is either a verdict that holds or not a dead marker. |

The `analyse` and `run_voblint` rows prove partial correctness. Solver termination and
required key coverage remain explicit per-program premises; parsing, code
generation, the OCaml compiler, and the handwritten CLI are outside the proved
chain.

The context axis stops earlier than the domain axis. Context-free is complete
for all five domains, in each `<Domain>_Entry` theory:
`analyse_<domain>_report_sound_proved`/`_refuted` conclude over `ltr_collect`,
and `analyse_<domain>_source_sound`/`_completed_run_sound` place a source run's
store in the published table at `lookup_context ... v ()`. The dispatcher rows
above collect all five into one statement over `analyse`. Under
`Ctx_EntryState` and `Ctx_CallString` what stands instead is the weaker
per-context bound: one context's
bucket of `activation_collect`, inside the concretization of the slot that
solve published for it. It falls short in three separate ways. It bounds one
bucket rather than everything reaching the node; it is stated against the
solved reader rather than against the published table; and it never reaches a
source execution. The contextual verdict report has no soundness statement in
any shape, and `analyse_config_ctx`, the dispatcher the CLI reaches both
policies through, has none either.

Each of those three gaps has its closing lemma already proved and generic — the
reader/table equation, the union over buckets, the source bridge, the last with
one worked program behind it. What is missing at either policy is the
instantiation, not the theory.

## Configuration coverage of the source-level endpoint

`run_voblint` takes a domain, an optional solver and a context policy. Not every
combination is a candidate for the source-level theorem, and the reason differs
per cell. Three outcomes exist in the dispatcher.

**Row-producing** -- the answer is built by `flat_output_of`,
`entry_state_output_of` or `cs_output_of`, so `out_checks` is
`check_rows_of ... (classify_checks_verdicts ...)` and the endpoint's row
argument applies. 26 configurations:

| Context | Sign | Parity | Congruence | Interval | Int |
| --- | --- | --- | --- | --- | --- |
| `Ctx_None` | Join*, PerOrigin | Join*, PerOrigin | Join*, PerOrigin | Warrow*, Join, PerOrigin, WPO | Warrow*, Join, PerOrigin, WPO |
| `Ctx_EntryState` | Join* | Join* | Join* | Warrow* | Warrow*, Join+ |
| `Ctx_CallString k` | Join* | Join* | Join* | Warrow* | Warrow*, Join |

`*` marks the discipline `None` selects; `+` marks a cell reached only by naming
a solver that nonetheless carries the source-level theorem. So 16 of the 26 are
covered. The remaining 10 are reachable in principle: the alternate unit disciplines are `global_interpretation`s of
`unit_dg_analysis`, which publishes `source_sound_closure` and
`result_node_sound_closure` alongside its own `terminates`/`sol_vars`/`result`;
and Int's two `Join` contextual cells already have
`analyse_int_entry_state_sound_of_cover` and
`analyse_int_call_string_sound_of_cover` published without the `_warrow` suffix.

**Report-only** -- Interval at `Join`, `PerOrigin` and `WarrowPerOrigin` under
either context policy routes to `verdict_report_answer`, which builds the answer
from a verdict report rather than from `classify_checks_verdicts` over a result
table. `out_checks_of_entry_state_output` and `out_checks_of_cs_output` do not
apply, so these 6 need a different bridge, not a re-instantiation of the same
one.

**Rejected** -- every remaining combination answers
`Unsupported_Configuration`, and there is nothing to prove.

The distinction that matters for planning: the remaining 10 are instantiation
work, the 6 are a new bridge.

## Dead rows

| Claim | Theorem | Note |
| --- | --- | --- |
| A dead row means nothing reaches that point | [`Voblint_CLI.Analysis_Run_Sound:dead_row_unreached`](../src/Executable_Surface/CLI/Analysis_Run_Sound.thy) | Per-node and universal over stores, so it does not follow from the endpoint by contraposition -- that one is existential in its CFG witness. |
| Contextual coverage is decidable | [`Voblint_Framework.CFG_Enumeration:ctx_vars_cover_of_exec`](../src/Abstract_Interpreter/Framework/Constraints/CFG_Enumeration.thy) | Walks the solved keys against the two edge enumerations; sufficient, not equivalent, like its unit counterpart. |

