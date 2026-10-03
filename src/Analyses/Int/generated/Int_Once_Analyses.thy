theory Int_Once_Analyses
  imports
    Int_Sound
    Int_Classify
    Int_Transfer
    Int_Exec
    "Voblint_Result.DG_Live_Unknowns"
    "Voblint_Framework.Call_String_Context"
    "Voblint_Framework.Routed_Context"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Solver.Globals_Rule"
    "Voblint_VIMP.VIMP_Program"
begin

section \<open>Registering \<open>Int_Once\<close> at every context and update rule\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  \<open>Int_Once\<close> runs through the shared D/G pipeline at the unit context.
  The CLI runs it as a field of the combined state of \<open>MCP_Analyses\<close>,
  whose component and soundness the unit registration supplies. Each registration
  leaves the rule that merges a value side-effected into a global as a parameter
  \<open>r\<close>. The equation system, the solve, the result table and every
  soundness endpoint come from the interpreted locale; this theory only names the
  domain's own implementation and facts.
\<close>

subsection \<open>At the unit context\<close>

global_interpretation int_once_rule: dg_analysis_exec
    "generic_tf_st_for (int_dom_ops Refine_Once)"
    "generic_enter_st_for (int_dom_ops Refine_Once)" cinit_int_dom_st
    "Analysis_Global ()" Analysis_Global Activation_Seed "\<lambda>_. route_unit" "()"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, unit) global_unknown)
       TYPE((int_dom default_st lifted, int_dom default_st lifted) dg_state) r"
    bot "int_classify_check Refine_Once"
    skip_int_dom "assign_int_dom Refine_Once" "special_int_dom Refine_Once"
    "branch_int_dom_for Refine_Once" body_int_dom "return_int_dom Refine_Once"
    "enter_int_dom_ci_for Refine_Once" event_int_dom "\<lambda>_. route_unit"
    "TD_side_rule_Interp_solve_c r"
  for r
proof (rule int_tf.dg_analysis_execI, goal_cases)
  case (1 \<G> u ctx d ca) show ?case by simp
next
  case (2 v ctx) show ?case by simp
next
  case 3 show ?case by (rule td_certified_solver)
next
  case (4 \<G>) show ?case by (rule int_cinit_gamma)
next
  case (5 n) show ?case by simp
qed

end
