theory Sign_Assembly
  imports
    Sign_Classify
    Sign_Transfer
    Sign_Sound
    "Voblint_Result.Unit_DG_Analysis"
    "Voblint_Solver.TD_Solver_Bridge"
    "TD.TD_side_upd_rule"
    "Voblint_VIMP.VIMP_Notation"
begin

hide_const phase.N

section \<open>Sign through the shared unit-context assembly\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>assembly/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Sign at the context-insensitive route: 2 instances of \<^locale>\<open>unit_dg_analysis\<close>, one per
  published solver discipline (\<open>always_join\<close>, \<open>per_origin\<close>), the first being the
  production default. The equation system, the solve, the reader, the result table, the
  report and every soundness endpoint come from that locale; this theory only names
  Sign's own implementation and facts and chooses the disciplines.

  Every obligation is discharged by citing a handwritten fact: Sign's own, or, for the
  three solver contracts, a \<^locale>\<open>TD_side_upd_rule\<close> instance. Only those three mention the
  update rule, which is why a second discipline costs a change of solver name and
  nothing else. Why Sign publishes these disciplines and not others is recorded in its
  README, not here.
\<close>

subsection \<open>Always join\<close>

global_interpretation sign_join: unit_dg_analysis
    sign_tf_st_for sign_enter_st_for cinit_sign_st
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)"
    bot sign_classify_check
    skip_sign assign_sign special_sign branch_sign body_sign return_sign
    enter_sign_ci_for event_sign TD_side_always_join_Interp_solve_c
  defines
    sign_unit_spec = sign_join.analysis_spec
    and sign_unit_root_query = sign_join.root_query
    and sign_unit_equations = sign_join.equations
    and sign_unit_solution = sign_join.solution
    and sign_unit_terminates = sign_join.terminates
    and sign_unit_vars = sign_join.sol_vars
    and sign_unit_env = sign_join.sol_env
    and sign_unit_result = sign_join.result
    and sign_unit_globals = sign_join.globals
    and sign_unit_solved = sign_join.solved
    and sign_unit_state_at = sign_join.state_at
    and sign_unit_report = sign_join.report
    and sign_unit_report_with_state = sign_join.report_with_state
proof (rule unit_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule sign_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule sign_tf_st_for_commute[unfolded sign_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule sign_enter_st_for_commute)
next
  case (4 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (5 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.finite_stabl_solve)
next
  case (6 c d s) then show ?case by (rule sign_classify_check_proved)
next
  case (7 c d s) then show ?case by (rule sign_classify_check_refuted)
next
  case 8 show ?case by (rule refl)
next
  case (9 gs) show ?case by (rule sign_cinit_gamma)
next
  case (10 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.solve_dom_of_solve_c)
qed

text \<open>
  A named \<^type>\<open>dg_spec\<close> that code generation can reach declares its own
  unfolding, next to the definition, so a specification never has to be given a
  most general ML type.
\<close>

declare sign_unit_spec_def [code_unfold]

subsection \<open>Per origin\<close>

global_interpretation sign_po_asm: unit_dg_analysis
    sign_tf_st_for sign_enter_st_for cinit_sign_st
    TD_side_per_origin_Interp_solve
    "TD_side_per_origin_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)"
    bot sign_classify_check
    skip_sign assign_sign special_sign branch_sign body_sign return_sign
    enter_sign_ci_for event_sign TD_side_per_origin_Interp_solve_c
  defines
    sign_po_solution = sign_po_asm.solution
    and sign_po_terminates = sign_po_asm.terminates
    and sign_po_vars = sign_po_asm.sol_vars
    and sign_po_result = sign_po_asm.result
    and sign_po_state_at = sign_po_asm.state_at
    and sign_po_report = sign_po_asm.report
proof (rule unit_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule sign_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule sign_tf_st_for_commute[unfolded sign_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule sign_enter_st_for_commute)
next
  case (4 eqs x) then show ?case
    by (rule TD_side_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (5 eqs x) then show ?case
    by (rule TD_side_per_origin_Interp.finite_stabl_solve)
next
  case (6 c d s) then show ?case by (rule sign_classify_check_proved)
next
  case (7 c d s) then show ?case by (rule sign_classify_check_refuted)
next
  case 8 show ?case by (rule refl)
next
  case (9 gs) show ?case by (rule sign_cinit_gamma)
next
  case (10 eqs x) then show ?case
    by (rule TD_side_per_origin_Interp.solve_dom_of_solve_c)
qed

subsection \<open>One equation system, 2 disciplines\<close>

text \<open>
  The pipeline builds its equations from the transfer parameters alone and the
  solver parameter never reaches them, so every discipline above solves the
  identical system. Stated, not asserted.
\<close>

lemma sign_po_equations_eq: "sign_po_asm.equations = sign_unit_equations"
  by (rule ext)+
     (simp add: sign_po_asm.equations_def sign_join.equations_def
        sign_po_asm.analysis_spec_def sign_join.analysis_spec_def)

end
