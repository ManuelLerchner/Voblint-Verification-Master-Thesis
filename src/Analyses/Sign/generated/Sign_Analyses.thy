theory Sign_Analyses
  imports
    Sign_Sound
    Sign_Assembly
    Sign_Classify
    Sign_Transfer
    Sign_Exec
    "Voblint_Result.Routed_Live_Keys"
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

section \<open>Sign at the entry-state context\<close>

global_interpretation sign_es: routed_dg_analysis
    sign_tf_st_for sign_enter_st_for cinit_sign_st
    "Analysis_Global ()" Activation_Seed exec_formals_route "[]"
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE((unit, sign list) routed_gk)
       TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)"
    bot sign_classify_check
    skip_sign assign_sign special_sign branch_sign body_sign return_sign
    enter_sign_ci_for event_sign "\<lambda>_. formals_route_lifted_gen"
    TD_side_always_join_Interp_solve_c
  defines
    sign_entry_state_spec = sign_es.analysis_spec
    and sign_entry_state_root_query = sign_es.root_query
    and sign_entry_state_equations = sign_es.equations
    and sign_entry_state_solution = sign_es.solution
    and sign_entry_state_terminates_for = sign_es.terminates
    and sign_entry_state_vars = sign_es.sol_vars
    and sign_entry_state_env = sign_es.sol_env
    and analyse_sign_entry_state_result_for = sign_es.result
    and analyse_sign_entry_state_report_for = sign_es.verdict_report
    and analyse_sign_entry_state_projection_for = sign_es.check_projection
    and sign_entry_state_context_rel = sign_es.admitted_contexts
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule sign_tf.is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule sign_tf_st_for_commute[unfolded sign_tf.tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule sign_enter_st_for_commute)
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
  case (8 c d s) then show ?case by (rule sign_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule sign_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule sign_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.solve_dom_of_solve_c)
qed

declare sign_entry_state_spec_def [code_unfold]

subsection \<open>The published entry-state constants\<close>

definition analyse_sign_entry_state_result ::
    "imp_prog \<Rightarrow> (sign list, sign abs_state) analysis_result" where
  "analyse_sign_entry_state_result p =
     analyse_sign_entry_state_result_for (declared_global p) p"

definition analyse_sign_entry_state_report ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_sign_entry_state_report p =
     analyse_sign_entry_state_report_for (declared_global p) p"

definition analyse_sign_entry_state_terminates :: "imp_prog \<Rightarrow> bool" where
  "analyse_sign_entry_state_terminates p =
     sign_entry_state_terminates_for (declared_global p) p"

lemmas analyse_sign_entry_state_sound =
  sign_es.entry_state_activation_collect_sound

lemmas analyse_sign_entry_state_has_context =
  sign_es.entry_state_has_context

lemmas analyse_sign_entry_state_ltr_collect_eq_Union =
  sign_es.entry_state_ltr_collect_eq_Union

lemmas analyse_sign_entry_state_sound_of_cover =
  sign_es.entry_state_activation_collect_sound_of_cover

lemmas analyse_sign_entry_state_ltr_collect_eq_Union_of_cover =
  sign_es.entry_state_ltr_collect_eq_Union_of_cover

lemmas analyse_sign_entry_state_sound_of_terminates =
  sign_es.entry_state_activation_collect_sound_of_terminates

lemmas analyse_sign_entry_state_ltr_collect_eq_Union_of_terminates =
  sign_es.entry_state_ltr_collect_eq_Union_of_terminates

lemmas analyse_sign_entry_state_gamma_reader_eq_lookup =
  sign_es.gamma_reader_eq_lookup

lemmas analyse_sign_entry_state_vars_finite =
  sign_es.vars_finite_of_terminates

section \<open>Sign at the call-string context\<close>

context
  fixes k :: nat
begin

interpretation sign_cs: routed_dg_analysis
    sign_tf_st_for sign_enter_st_for cinit_sign_st
    Call_String_Context.Global Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
       TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)"
    bot sign_classify_check
    skip_sign assign_sign special_sign branch_sign body_sign return_sign
    enter_sign_ci_for event_sign "\<lambda>_. cs_route k"
    TD_side_always_join_Interp_solve_c
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule sign_tf.is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule sign_tf_st_for_commute[unfolded sign_tf.tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule sign_enter_st_for_commute)
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
  case (8 c d s) then show ?case by (rule sign_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule sign_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule sign_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.solve_dom_of_solve_c)
qed

lemmas analyse_sign_call_string_sound =
  sign_cs.fun_route_activation_collect_sound[OF cs_route_context_agree]

lemmas analyse_sign_call_string_sound_of_cover =
  sign_cs.fun_route_activation_collect_sound_of_cover[OF cs_route_context_agree]

lemmas analyse_sign_call_string_ltr_collect_eq_Union =
  sign_cs.fun_route_ltr_collect_eq_Union

lemmas analyse_sign_call_string_sound_of_terminates =
  sign_cs.fun_route_activation_collect_sound_of_terminates[OF cs_route_context_agree]

lemmas analyse_sign_call_string_gamma_reader_eq_lookup =
  sign_cs.gamma_reader_eq_lookup

lemmas analyse_sign_call_string_vars_finite =
  sign_cs.vars_finite_of_terminates

lemmas analyse_sign_call_string_terminates_of_solve_c =
  sign_cs.terminates_of_solve_c

end

subsection \<open>The published call-string constants\<close>

definition analyse_sign_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, sign abs_state) analysis_result" where
  "analyse_sign_call_string_result k p =
     routed_dg_pipeline.result
    sign_tf_st_for sign_enter_st_for cinit_sign_st
      Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve (declared_global p) p"

definition analyse_sign_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_sign_call_string_report k p =
     routed_dg_pipeline.verdict_report
    sign_tf_st_for sign_enter_st_for cinit_sign_st
      Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve sign_classify_check (declared_global p) p"

definition analyse_sign_call_string_terminates ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "analyse_sign_call_string_terminates k p =
     routed_dg_pipeline.terminates
    sign_tf_st_for sign_enter_st_for cinit_sign_st
      Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
          TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state))
       (declared_global p) p"

end
