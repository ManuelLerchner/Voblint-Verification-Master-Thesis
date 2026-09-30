theory Interval_Analyses
  imports
    Interval_Sound
    Interval_Classify
    Interval_Transfer
    Interval_Exec
    "Voblint_Result.DG_Live_Unknowns"
    "Voblint_Framework.Call_String_Context"
    "Voblint_Framework.Routed_Context"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Solver.Globals_Rule"
    "Voblint_VIMP.VIMP_Program"
begin

section \<open>Registering Interval at every context and update rule\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Interval runs through the shared D/G pipeline at the unit context, keyed by the
  abstract values a callee's formals hold on entry, and keyed by a bounded call
  string. The CLI runs it as a field of the combined state of
  \<open>MCP_Analyses\<close>, whose component and soundness the unit registration
  supplies. Each registration leaves the rule that merges a value side-effected into a
  global as a parameter \<open>r\<close>, and the call-string one also its bound
  \<open>k\<close>. The equation system, the solve, the result table and every
  soundness endpoint come from the interpreted locale; this theory only names the
  domain's own implementation and facts.
\<close>

subsection \<open>At the unit context\<close>

global_interpretation interval_rule: dg_analysis_exec
    ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
    "Analysis_Global ()" Activation_Seed "\<lambda>_. route_unit" "()"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, unit) global_unknown)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) r"
    bot interval_classify_check
    skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
    enter_ivl_ci_for event_ivl "\<lambda>_. route_unit"
    "TD_side_rule_Interp_solve_c r"
  for r
proof (rule ivl_tf.dg_analysis_execI
    [folded ivl_tf_st_for_def ivl_enter_st_for_def], goal_cases)
  case (1 \<G> u ctx d ca) show ?case by simp
next
  case (2 v ctx) show ?case by simp
next
  case 3 show ?case by (rule td_certified_solver)
next
  case (4 \<G>) show ?case by (rule interval_cinit_gamma)
qed

subsection \<open>At the entry-state context\<close>

global_interpretation interval_es_rule: dg_analysis_exec
    ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
    "Analysis_Global ()" Activation_Seed exec_formals_route "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, ivl list) global_unknown)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) r"
    bot interval_classify_check
    skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
    enter_ivl_ci_for event_ivl "\<lambda>_. formals_route_lifted_gen"
    "TD_side_rule_Interp_solve_c r"
  for r
proof (rule ivl_tf.dg_analysis_execI
    [folded ivl_tf_st_for_def ivl_enter_st_for_def], goal_cases)
  case (1 \<G> u ctx d ca) show ?case
    by (rule exec_formals_route_commute[symmetric])
next
  case (2 v ctx) show ?case by simp
next
  case 3 show ?case by (rule td_certified_solver)
next
  case (4 \<G>) show ?case by (rule interval_cinit_gamma)
qed

subsection \<open>At the call-string context\<close>

global_interpretation interval_cs_rule: dg_analysis_exec
    ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
    Call_String_Context.Global Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE(call_string_gk)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) r"
    bot interval_classify_check
    skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
    enter_ivl_ci_for event_ivl "\<lambda>_. cs_route k"
    "TD_side_rule_Interp_solve_c r"
  for k r
proof (rule ivl_tf.dg_analysis_execI
    [folded ivl_tf_st_for_def ivl_enter_st_for_def], goal_cases)
  case (1 \<G> u ctx d ca) show ?case by (rule cs_route_indep_of_data)
next
  case (2 v ctx) show ?case by simp
next
  case 3 show ?case by (rule td_certified_solver)
next
  case (4 \<G>) show ?case by (rule interval_cinit_gamma)
qed

end
