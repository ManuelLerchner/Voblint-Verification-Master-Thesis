theory Congruence_Analyses
  imports
    Congruence_Sound
    Congruence_Classify
    Congruence_Transfer
    Congruence_Exec
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

section \<open>Congruence at the entry-state context\<close>

global_interpretation congruence_es: routed_dg_analysis
    congruence_tf_st_for congruence_enter_st_for cinit_congruence_st
    "Analysis_Global ()" Activation_Seed exec_formals_route "[]"
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE((unit, congruence list) routed_gk)
       TYPE((congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)"
    bot congruence_classify_check
    skip_congruence assign_congruence special_congruence branch_congruence body_congruence
    return_congruence enter_congruence_ci_for event_congruence
    "\<lambda>_. formals_route_lifted_gen" TD_side_always_join_Interp_solve_c
  defines
    congruence_entry_state_spec = congruence_es.analysis_spec
    and congruence_entry_state_root_query = congruence_es.root_query
    and congruence_entry_state_equations = congruence_es.equations
    and congruence_entry_state_solution = congruence_es.solution
    and congruence_entry_state_terminates_for = congruence_es.terminates
    and congruence_entry_state_vars = congruence_es.sol_vars
    and congruence_entry_state_env = congruence_es.sol_env
    and analyse_congruence_entry_state_result_for = congruence_es.result
    and analyse_congruence_entry_state_report_for = congruence_es.verdict_report
    and analyse_congruence_entry_state_projection_for = congruence_es.check_projection
    and congruence_entry_state_context_rel = congruence_es.admitted_contexts
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule congruence_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule congruence_tf_st_for_commute[unfolded congruence_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule congruence_enter_st_for_commute)
next
  case (4 gs u ctx d ca) show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule exec_formals_route_commute[symmetric])
next
  case (5 v ctx) show ?case by simp
next
  case (6 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (7 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.finite_stabl_solve)
next
  case (8 c d s) then show ?case by (rule congruence_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule congruence_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule congruence_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.solve_dom_of_solve_c)
qed

declare congruence_entry_state_spec_def [code_unfold]

subsection \<open>The published entry-state constants\<close>

definition analyse_congruence_entry_state_result ::
    "imp_prog \<Rightarrow> (congruence list, congruence abs_state) analysis_result" where
  "analyse_congruence_entry_state_result p =
     analyse_congruence_entry_state_result_for (declared_global p) p"

definition analyse_congruence_entry_state_report ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_congruence_entry_state_report p =
     analyse_congruence_entry_state_report_for (declared_global p) p"

definition analyse_congruence_entry_state_terminates :: "imp_prog \<Rightarrow> bool" where
  "analyse_congruence_entry_state_terminates p =
     congruence_entry_state_terminates_for (declared_global p) p"

lemmas analyse_congruence_entry_state_sound =
  congruence_es.entry_state_activation_collect_sound

section \<open>Congruence at the call-string context\<close>

context
  fixes k :: nat
begin

interpretation congruence_cs: routed_dg_analysis
    congruence_tf_st_for congruence_enter_st_for cinit_congruence_st
    Call_String_Context.Global Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
       TYPE((congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)"
    bot congruence_classify_check
    skip_congruence assign_congruence special_congruence branch_congruence body_congruence
    return_congruence enter_congruence_ci_for event_congruence "\<lambda>_. cs_route k"
    TD_side_always_join_Interp_solve_c
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule congruence_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule congruence_tf_st_for_commute[unfolded congruence_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule congruence_enter_st_for_commute)
next
  case (4 gs u ctx d ca) show ?case by (rule cs_route_indep_of_data)
next
  case (5 v ctx) show ?case by simp
next
  case (6 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (7 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.finite_stabl_solve)
next
  case (8 c d s) then show ?case by (rule congruence_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule congruence_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule congruence_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.solve_dom_of_solve_c)
qed

lemmas analyse_congruence_call_string_sound =
  congruence_cs.fun_route_activation_collect_sound[OF cs_route_context_agree]

lemmas analyse_congruence_call_string_terminates_of_solve_c =
  congruence_cs.terminates_of_solve_c

end

subsection \<open>The published call-string constants\<close>

definition analyse_congruence_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, congruence abs_state) analysis_result" where
  "analyse_congruence_call_string_result k p =
     routed_dg_pipeline.result
    congruence_tf_st_for congruence_enter_st_for cinit_congruence_st
      Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve (declared_global p) p"

definition analyse_congruence_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_congruence_call_string_report k p =
     routed_dg_pipeline.verdict_report
    congruence_tf_st_for congruence_enter_st_for cinit_congruence_st
      Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve congruence_classify_check (declared_global p) p"

definition analyse_congruence_call_string_terminates ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "analyse_congruence_call_string_terminates k p =
     routed_dg_pipeline.terminates
    congruence_tf_st_for congruence_enter_st_for cinit_congruence_st
      Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
          TYPE((congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state))
       (declared_global p) p"

end
