theory Int_Analyses
  imports
    Int_Sound
    Int_Classify
    Int_Exec
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

section \<open>Int at the entry-state context\<close>

context
  fixes mode :: refine_mode
begin

interpretation int_es: routed_dg_analysis
    "int_tf_st_for mode" "int_dom_enter_st_for mode" cinit_int_dom_st
    "Analysis_Global ()" Activation_Seed exec_formals_route "[]"
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE((unit, int_dom list) routed_gk)
       TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
    bot int_classify_check
    skip_int_dom "assign_int_dom mode" "special_int_dom mode" "branch_int_dom_for mode"
    body_int_dom "return_int_dom mode" "enter_int_dom_ci_for mode" event_int_dom
    "\<lambda>_. formals_route_lifted_gen" TD_side_always_join_Interp_solve_c
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule int_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule int_tf_st_for_commute[unfolded int_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule int_dom_enter_st_for_commute)
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
  case (8 c d s) then show ?case by (rule int_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule int_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule int_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.solve_dom_of_solve_c)
qed

lemmas analyse_int_entry_state_sound =
  int_es.entry_state_activation_collect_sound

lemmas analyse_int_entry_state_has_context =
  int_es.entry_state_has_context

lemmas analyse_int_entry_state_ltr_collect_eq_Union =
  int_es.entry_state_ltr_collect_eq_Union

lemmas analyse_int_entry_state_sound_of_cover =
  int_es.entry_state_activation_collect_sound_of_cover

lemmas analyse_int_entry_state_ltr_collect_eq_Union_of_cover =
  int_es.entry_state_ltr_collect_eq_Union_of_cover

lemmas analyse_int_entry_state_gamma_reader_eq_lookup =
  int_es.gamma_reader_eq_lookup

lemmas analyse_int_entry_state_vars_finite =
  int_es.vars_finite_of_terminates

interpretation int_es_warrow: routed_dg_analysis
    "int_tf_st_for mode" "int_dom_enter_st_for mode" cinit_int_dom_st
    "Analysis_Global ()" Activation_Seed exec_formals_route "[]"
    TD_side_warrowing_apinis_Interp_solve
    "TD_side_warrowing_apinis_Interp.solve_dom TYPE((unit, int_dom list) routed_gk)
       TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
    bot int_classify_check
    skip_int_dom "assign_int_dom mode" "special_int_dom mode" "branch_int_dom_for mode"
    body_int_dom "return_int_dom mode" "enter_int_dom_ci_for mode" event_int_dom
    "\<lambda>_. formals_route_lifted_gen" TD_side_warrowing_apinis_Interp_solve_c
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule int_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule int_tf_st_for_commute[unfolded int_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule int_dom_enter_st_for_commute)
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
  case (8 c d s) then show ?case by (rule int_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule int_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule int_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c)
qed

lemmas analyse_int_entry_state_sound_warrow =
  int_es_warrow.entry_state_activation_collect_sound

lemmas analyse_int_entry_state_has_context_warrow =
  int_es_warrow.entry_state_has_context

lemmas analyse_int_entry_state_ltr_collect_eq_Union_warrow =
  int_es_warrow.entry_state_ltr_collect_eq_Union

lemmas analyse_int_entry_state_sound_of_cover_warrow =
  int_es_warrow.entry_state_activation_collect_sound_of_cover

lemmas analyse_int_entry_state_ltr_collect_eq_Union_of_cover_warrow =
  int_es_warrow.entry_state_ltr_collect_eq_Union_of_cover

lemmas analyse_int_entry_state_gamma_reader_eq_lookup_warrow =
  int_es_warrow.gamma_reader_eq_lookup

lemmas analyse_int_entry_state_vars_finite_warrow =
  int_es_warrow.vars_finite_of_terminates

end

subsection \<open>The published entry-state constants\<close>

definition analyse_int_entry_state_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_for gs p =
     routed_dg_pipeline.result
    (int_tf_st_for Refine_Fixpoint) (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
      (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_always_join_Interp_solve gs p"

definition analyse_int_entry_state_result ::
    "imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result p =
     analyse_int_entry_state_result_for (declared_global p) p"

definition analyse_int_entry_state_report ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_entry_state_report p =
     routed_dg_pipeline.verdict_report
    (int_tf_st_for Refine_Fixpoint) (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
      (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_always_join_Interp_solve int_classify_check (declared_global p) p"

section \<open>Int at the call-string context\<close>

context
  fixes mode :: refine_mode and k :: nat
begin

interpretation int_cs: routed_dg_analysis
    "int_tf_st_for mode" "int_dom_enter_st_for mode" cinit_int_dom_st
    Call_String_Context.Global Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
       TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
    bot int_classify_check
    skip_int_dom "assign_int_dom mode" "special_int_dom mode" "branch_int_dom_for mode"
    body_int_dom "return_int_dom mode" "enter_int_dom_ci_for mode" event_int_dom
    "\<lambda>_. cs_route k" TD_side_always_join_Interp_solve_c
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule int_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule int_tf_st_for_commute[unfolded int_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule int_dom_enter_st_for_commute)
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
  case (8 c d s) then show ?case by (rule int_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule int_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule int_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.solve_dom_of_solve_c)
qed

lemmas analyse_int_call_string_sound =
  int_cs.fun_route_activation_collect_sound[OF cs_route_context_agree]

lemmas analyse_int_call_string_sound_of_cover =
  int_cs.fun_route_activation_collect_sound_of_cover[OF cs_route_context_agree]

lemmas analyse_int_call_string_ltr_collect_eq_Union =
  int_cs.fun_route_ltr_collect_eq_Union

lemmas analyse_int_call_string_gamma_reader_eq_lookup =
  int_cs.gamma_reader_eq_lookup

lemmas analyse_int_call_string_vars_finite =
  int_cs.vars_finite_of_terminates

interpretation int_cs_warrow: routed_dg_analysis
    "int_tf_st_for mode" "int_dom_enter_st_for mode" cinit_int_dom_st
    Call_String_Context.Global Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    TD_side_warrowing_apinis_Interp_solve
    "TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk)
       TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
    bot int_classify_check
    skip_int_dom "assign_int_dom mode" "special_int_dom mode" "branch_int_dom_for mode"
    body_int_dom "return_int_dom mode" "enter_int_dom_ci_for mode" event_int_dom
    "\<lambda>_. cs_route k" TD_side_warrowing_apinis_Interp_solve_c
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule int_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule int_tf_st_for_commute[unfolded int_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule int_dom_enter_st_for_commute)
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
  case (8 c d s) then show ?case by (rule int_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule int_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule int_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c)
qed

lemmas analyse_int_call_string_sound_warrow =
  int_cs_warrow.fun_route_activation_collect_sound[OF cs_route_context_agree]

lemmas analyse_int_call_string_sound_of_cover_warrow =
  int_cs_warrow.fun_route_activation_collect_sound_of_cover[OF cs_route_context_agree]

lemmas analyse_int_call_string_ltr_collect_eq_Union_warrow =
  int_cs_warrow.fun_route_ltr_collect_eq_Union

lemmas analyse_int_call_string_gamma_reader_eq_lookup_warrow =
  int_cs_warrow.gamma_reader_eq_lookup

lemmas analyse_int_call_string_vars_finite_warrow =
  int_cs_warrow.vars_finite_of_terminates

end

subsection \<open>The published call-string constants\<close>

definition analyse_int_call_string_result_for ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result_for k gs p =
     routed_dg_pipeline.result
    (int_tf_st_for Refine_Fixpoint) (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
      Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve gs p"

definition analyse_int_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result k p =
     analyse_int_call_string_result_for k (declared_global p) p"

definition analyse_int_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_call_string_report k p =
     routed_dg_pipeline.verdict_report
    (int_tf_st_for Refine_Fixpoint) (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
      Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve int_classify_check (declared_global p) p"

end
