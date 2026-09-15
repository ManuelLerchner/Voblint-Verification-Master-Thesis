theory Interval_Analyses
  imports
    Interval_Sound
    Interval_Classify
    Interval_Transfer
    Interval_Exec
    "Voblint_Result.Unit_DG_Analysis"
    "Voblint_Result.Routed_Live_Keys"
    "Voblint_Framework.Call_String_Context"
    "Voblint_Framework.Routed_Context"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Solver.Globals_Rule"
    "Voblint_VIMP.VIMP_Program"
    "TD.TD_side_upd_rule"
begin

section \<open>Registering Interval at every context and update rule\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Interval runs through the shared D/G pipeline three times: at the unit context,
  keyed by the abstract values a callee's formals hold on entry, and keyed by a
  bounded call string. Each registration leaves the rule that merges a value
  side-effected into a global as a parameter \<open>r\<close>, and the call-string
  one also its bound \<open>k\<close>, so one registration serves every discipline and
  every bound. The equation system, the solve, the result table and every soundness
  endpoint come from the interpreted locale; this theory only names the domain's
  own implementation and facts.
\<close>

subsection \<open>At the unit context\<close>

global_interpretation interval_rule: unit_dg_analysis
    ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) r"
    bot interval_classify_check
    skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
    enter_ivl_ci_for event_ivl "TD_side_rule_Interp_solve_c r"
  for r
proof (rule unit_dg_analysis.intro, rule routed_dg_analysis.intro,
       goal_cases)
  case (1 gs) show ?case by (rule ivl_tf.is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule ivl_tf_st_for_commute[unfolded ivl_tf.tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule ivl_enter_st_for_commute)
next
  case (4 gs u ctx d ca) show ?case by simp
next
  case (5 v ctx) show ?case by simp
next
  case (6 eqs x) then show ?case
    by (rule TD_side_rule_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (7 eqs x) then show ?case
    by (rule TD_side_rule_Interp.finite_stabl_solve)
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
    by (rule TD_side_rule_Interp.solve_dom_of_solve_c)
qed

subsection \<open>At the entry-state context\<close>

global_interpretation interval_es_rule: routed_dg_analysis
    ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
    "Analysis_Global ()" Activation_Seed exec_formals_route "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, ivl list) routed_gk)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) r"
    bot interval_classify_check
    skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
    enter_ivl_ci_for event_ivl "\<lambda>_. formals_route_lifted_gen"
    "TD_side_rule_Interp_solve_c r"
  for r
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule ivl_tf.is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule ivl_tf_st_for_commute[unfolded ivl_tf.tf_abs_def])
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
    by (rule TD_side_rule_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (7 eqs x) then show ?case
    by (rule TD_side_rule_Interp.finite_stabl_solve)
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
    by (rule TD_side_rule_Interp.solve_dom_of_solve_c)
qed

subsection \<open>At the call-string context\<close>

global_interpretation interval_cs_rule: routed_dg_analysis
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
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule ivl_tf.is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule ivl_tf_st_for_commute[unfolded ivl_tf.tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule ivl_enter_st_for_commute)
next
  case (4 gs u ctx d ca) show ?case by (rule cs_route_indep_of_data)
next
  case (5 v ctx) show ?case by simp
next
  case (6 eqs x) then show ?case
    by (rule TD_side_rule_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (7 eqs x) then show ?case
    by (rule TD_side_rule_Interp.finite_stabl_solve)
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
    by (rule TD_side_rule_Interp.solve_dom_of_solve_c)
qed

end
