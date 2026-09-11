theory Parity_Analyses
  imports
    Parity_Sound
    Parity_Classify
    Parity_Transfer
    Parity_Exec
    "Voblint_Result.Routed_Live_Keys"
    "Voblint_Framework.Call_String_Context"
    "Voblint_Framework.Routed_Context"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_VIMP.VIMP_Program"
    "TD.TD_side_upd_rule"
begin

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.
\<close>

section \<open>Parity at the entry-state context\<close>

global_interpretation parity_es: routed_dg_analysis
    parity_tf_st_for parity_enter_st_for cinit_parity_st
    "Analysis_Global ()" Activation_Seed exec_formals_route "[]"
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE((unit, parity list) routed_gk)
       TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)"
    bot parity_classify_check
    skip_parity assign_parity special_parity branch_parity body_parity return_parity
    enter_parity_ci_for event_parity "\<lambda>_. formals_route_lifted_gen"
    TD_side_always_join_Interp_solve_c
  defines
    parity_entry_state_spec = parity_es.analysis_spec
    and parity_entry_state_root_query = parity_es.root_query
    and parity_entry_state_equations = parity_es.equations
    and parity_entry_state_solution = parity_es.solution
    and parity_entry_state_terminates_for = parity_es.terminates
    and parity_entry_state_vars = parity_es.sol_vars
    and parity_entry_state_env = parity_es.sol_env
    and analyse_parity_entry_state_result_for = parity_es.result
    and analyse_parity_entry_state_report_for = parity_es.verdict_report
    and analyse_parity_entry_state_projection_for = parity_es.check_projection
    and parity_entry_state_context_rel = parity_es.admitted_contexts
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule parity_tf.is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule parity_tf_st_for_commute_if_live[unfolded parity_tf.tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule parity_enter_st_for_commute)
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
  case (8 c d s) then show ?case by (rule parity_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule parity_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule parity_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.solve_dom_of_solve_c)
qed

declare parity_entry_state_spec_def [code_unfold]

subsection \<open>The published entry-state constants\<close>

definition analyse_parity_entry_state_result ::
    "imp_prog \<Rightarrow> (parity list, parity abs_state) analysis_result" where
  "analyse_parity_entry_state_result p =
     analyse_parity_entry_state_result_for (declared_global p) p"

definition analyse_parity_entry_state_report ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_parity_entry_state_report p =
     analyse_parity_entry_state_report_for (declared_global p) p"

definition analyse_parity_entry_state_terminates :: "imp_prog \<Rightarrow> bool" where
  "analyse_parity_entry_state_terminates p =
     parity_entry_state_terminates_for (declared_global p) p"

lemmas analyse_parity_entry_state_sound =
  parity_es.entry_state_activation_collect_sound

lemmas analyse_parity_entry_state_has_context =
  parity_es.entry_state_has_context

lemmas analyse_parity_entry_state_ltr_collect_eq_Union =
  parity_es.entry_state_ltr_collect_eq_Union

lemmas analyse_parity_entry_state_sound_of_cover =
  parity_es.entry_state_activation_collect_sound_of_cover

lemmas analyse_parity_entry_state_ltr_collect_eq_Union_of_cover =
  parity_es.entry_state_ltr_collect_eq_Union_of_cover

lemmas analyse_parity_entry_state_sound_of_terminates =
  parity_es.entry_state_activation_collect_sound_of_terminates

lemmas analyse_parity_entry_state_ltr_collect_eq_Union_of_terminates =
  parity_es.entry_state_ltr_collect_eq_Union_of_terminates

lemmas analyse_parity_entry_state_gamma_reader_eq_lookup =
  parity_es.gamma_reader_eq_lookup

lemmas analyse_parity_entry_state_vars_finite =
  parity_es.vars_finite_of_terminates

section \<open>Parity at the call-string context\<close>

context
  fixes k :: nat
begin

interpretation parity_cs: routed_dg_analysis
    parity_tf_st_for parity_enter_st_for cinit_parity_st
    Call_String_Context.Global Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
       TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)"
    bot parity_classify_check
    skip_parity assign_parity special_parity branch_parity body_parity return_parity
    enter_parity_ci_for event_parity "\<lambda>_. cs_route k"
    TD_side_always_join_Interp_solve_c
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule parity_tf.is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule parity_tf_st_for_commute_if_live[unfolded parity_tf.tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule parity_enter_st_for_commute)
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
  case (8 c d s) then show ?case by (rule parity_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule parity_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule parity_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.solve_dom_of_solve_c)
qed

lemmas analyse_parity_call_string_sound =
  parity_cs.fun_route_activation_collect_sound[OF cs_route_context_agree]

lemmas analyse_parity_call_string_sound_of_cover =
  parity_cs.fun_route_activation_collect_sound_of_cover[OF cs_route_context_agree]

lemmas analyse_parity_call_string_ltr_collect_eq_Union =
  parity_cs.fun_route_ltr_collect_eq_Union

lemmas analyse_parity_call_string_sound_of_terminates =
  parity_cs.fun_route_activation_collect_sound_of_terminates[OF cs_route_context_agree]

lemmas analyse_parity_call_string_gamma_reader_eq_lookup =
  parity_cs.gamma_reader_eq_lookup

lemmas analyse_parity_call_string_vars_finite =
  parity_cs.vars_finite_of_terminates

lemmas analyse_parity_call_string_terminates_of_solve_c =
  parity_cs.terminates_of_solve_c

end

subsection \<open>The published call-string constants\<close>

definition analyse_parity_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, parity abs_state) analysis_result" where
  "analyse_parity_call_string_result k p =
     routed_dg_pipeline.result
    parity_tf_st_for parity_enter_st_for cinit_parity_st
      Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve (declared_global p) p"

definition analyse_parity_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_parity_call_string_report k p =
     routed_dg_pipeline.verdict_report
    parity_tf_st_for parity_enter_st_for cinit_parity_st
      Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve parity_classify_check (declared_global p) p"

definition analyse_parity_call_string_terminates ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "analyse_parity_call_string_terminates k p =
     routed_dg_pipeline.terminates
    parity_tf_st_for parity_enter_st_for cinit_parity_st
      Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
          TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state))
       (declared_global p) p"

end
