theory Parity_Analyses
  imports
    Parity_Sound
    Parity_Classify
    Parity_Transfer
    Parity_Exec
    "Voblint_Result.DG_Live_Unknowns"
    "Voblint_Framework.Call_String_Context"
    "Voblint_Framework.Routed_Context"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Solver.Globals_Rule"
    "Voblint_VIMP.VIMP_Program"
begin

section \<open>Registering Parity at every context and update rule\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Parity runs through the shared D/G pipeline at the unit context. The CLI runs it as
  a field of the combined state of \<open>MCP_Analyses\<close>, whose component and
  soundness the unit registration supplies. Each registration leaves the rule that
  merges a value side-effected into a global as a parameter \<open>r\<close>. The
  equation system, the solve, the result table and every soundness endpoint come from
  the interpreted locale; this theory only names the domain's own implementation and
  facts.
\<close>

subsection \<open>At the unit context\<close>

global_interpretation parity_rule: dg_analysis_exec
    parity_tf_st_for parity_enter_st_for cinit_parity_st
    "Analysis_Global ()" Activation_Seed "\<lambda>_. route_unit" "()"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, unit) global_unknown)
       TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) r"
    bot parity_classify_check
    skip_parity assign_parity special_parity branch_parity body_parity return_parity
    enter_parity_ci_for event_parity "\<lambda>_. route_unit"
    "TD_side_rule_Interp_solve_c r"
  for r
proof (rule parity_tf.dg_analysis_execI
    [folded parity_tf_st_for_def parity_enter_st_for_def], goal_cases)
  case (1 \<G> u ctx d ca) show ?case by simp
next
  case (2 v ctx) show ?case by simp
next
  case 3 show ?case by (rule td_certified_solver)
next
  case (4 \<G>) show ?case by (rule parity_cinit_gamma)
qed

end
