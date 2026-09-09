theory Interval_Contextual_Assembly
  imports
    Interval_Sound
    Interval_Assembly
    Interval_Classify
    Interval_Exec_Sound
    "Voblint_Result.Routed_DG_Analysis"
    "Voblint_Framework.Call_String_Context"
    "Voblint_Framework.Routed_Context"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_VIMP.VIMP_Program"
    "TD.TD_side_upd_rule"
begin

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>assembly/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.
\<close>

section \<open>Interval at the entry-state context\<close>

global_interpretation interval_es: routed_dg_analysis
    ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
    "Analysis_Global ()" Activation_Seed exec_formals_route "[]"
    TD_side_warrowing_apinis_Interp_solve
    "TD_side_warrowing_apinis_Interp.solve_dom TYPE((unit, ivl list) routed_gk)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)"
    bot interval_classify_check
    skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
    enter_ivl_ci_for event_ivl "\<lambda>_. formals_route_lifted_gen"
    TD_side_warrowing_apinis_Interp_solve_c
  defines
    interval_entry_state_spec = interval_es.analysis_spec
    and interval_entry_state_root_query = interval_es.root_query
    and entry_state_eqs_prog = interval_es.equations
    and entry_state_sol_prog = interval_es.solution
    and entry_state_terminates_prog = interval_es.terminates
    and entry_state_vars_prog = interval_es.sol_vars
    and entry_state_env_prog = interval_es.sol_env
    and entry_state_sg_st_prog = interval_es.reader
    and entry_state_context_rel = interval_es.admitted_contexts
    and analyse_interval_entry_state_result_for = interval_es.result
    and analyse_interval_entry_state_report_for = interval_es.verdict_report
    and analyse_interval_entry_state_projection_for = interval_es.check_projection
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule ivl_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule ivl_tf_st_for_commute[unfolded ivl_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule ivl_enter_st_for_commute)
next
  case (4 gs u ctx d ca) show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule exec_formals_route_commute[symmetric])
next
  case (5 v ctx) show ?case by simp
next
  case (6 eqs x) then show ?case
    by (rule TD_side_warrowing_apinis_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (7 eqs x) then show ?case
    by (rule TD_side_warrowing_apinis_Interp.finite_stabl_solve)
next
  case (8 c d s) then show ?case by (rule interval_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule interval_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule interval_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c)
qed

declare interval_entry_state_spec_def [code_unfold]

section \<open>Interval at the call-string context\<close>

context
  fixes k :: nat
begin

interpretation interval_cs: routed_dg_analysis
    ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
    Call_String_Context.Global Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    TD_side_warrowing_apinis_Interp_solve
    "TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)"
    bot interval_classify_check
    skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
    enter_ivl_ci_for event_ivl "\<lambda>_. cs_route k"
    TD_side_warrowing_apinis_Interp_solve_c
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule ivl_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule ivl_tf_st_for_commute[unfolded ivl_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule ivl_enter_st_for_commute)
next
  case (4 gs u ctx d ca) show ?case by (rule cs_route_indep_of_data)
next
  case (5 v ctx) show ?case by simp
next
  case (6 eqs x) then show ?case
    by (rule TD_side_warrowing_apinis_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (7 eqs x) then show ?case
    by (rule TD_side_warrowing_apinis_Interp.finite_stabl_solve)
next
  case (8 c d s) then show ?case by (rule interval_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule interval_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule interval_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c)
qed

lemmas analyse_interval_call_string_sound =
  interval_cs.fun_route_activation_collect_sound[OF cs_route_context_agree]

lemmas cs_call_string_terminates_via_solve_c =
  interval_cs.terminates_of_solve_c

end

end
