theory Sign_Analyses
  imports
    Sign_Sound
    Sign_Classify
    Sign_Transfer
    Sign_Exec
    "Voblint_Result.DG_Live_Unknowns"
    "Voblint_Framework.Call_String_Context"
    "Voblint_Framework.Routed_Context"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Solver.Globals_Rule"
    "Voblint_VIMP.VIMP_Program"
begin

section \<open>Registering Sign at every context and update rule\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Sign runs through the shared D/G pipeline at the unit context. The CLI runs it as a
  field of the combined state of \<open>MCP_Analyses\<close>, whose component and
  soundness the unit registration supplies. Each registration leaves the rule that
  merges a value side-effected into a global as a parameter \<open>r\<close>. The
  equation system, the solve, the result table and every soundness endpoint come from
  the interpreted locale; this theory only names the domain's own implementation and
  facts.
\<close>

subsection \<open>At the unit context\<close>

global_interpretation sign_rule: dg_analysis_exec
    sign_tf_st_for sign_enter_st_for cinit_sign_st
    "Analysis_Global ()" Activation_Seed "\<lambda>_. route_unit" "()"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, unit) global_unknown)
       TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) r"
    bot sign_classify_check
    skip_sign assign_sign special_sign branch_sign body_sign return_sign
    enter_sign_ci_for event_sign "\<lambda>_. route_unit"
    "TD_side_rule_Interp_solve_c r"
  for r
proof (rule sign_tf.dg_analysis_execI
    [folded sign_tf_st_for_def sign_enter_st_for_def], goal_cases)
  case (1 \<G> u ctx d ca) show ?case by simp
next
  case (2 v ctx) show ?case by simp
next
  case 3 show ?case by (rule td_certified_solver)
next
  case (4 \<G>) show ?case by (rule sign_cinit_gamma)
qed

end
