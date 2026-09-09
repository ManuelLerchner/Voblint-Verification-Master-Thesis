theory Congruence_Assembly
  imports
    Congruence_Classify
    Congruence_Transfer
    Congruence_Sound
    "Voblint_Result.Unit_DG_Analysis"
    "Voblint_Solver.TD_Solver_Bridge"
    "TD.TD_side_upd_rule"
begin

hide_const phase.N

section \<open>Congruence through the shared unit-context assembly\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>assembly/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Congruence at the context-insensitive route: 2 instances of \<^locale>\<open>unit_dg_analysis\<close>, one
  per published solver discipline (\<open>always_join\<close>, \<open>per_origin\<close>), the first being the
  production default. The equation system, the solve, the reader, the result table, the
  report and every soundness endpoint come from that locale; this theory only names
  Congruence's own implementation and facts and chooses the disciplines.

  Every obligation is discharged by citing a handwritten fact: Congruence's own, or,
  for the three solver contracts, a \<^locale>\<open>TD_side_upd_rule\<close> instance. Only those three
  mention the update rule, which is why a second discipline costs a change of solver
  name and nothing else. Why Congruence publishes these disciplines and not others is
  recorded in its README, not here.
\<close>

subsection \<open>Always join\<close>

global_interpretation congruence_join: unit_dg_analysis
    congruence_tf_st_for congruence_enter_st_for cinit_congruence_st
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)"
    bot congruence_classify_check
    skip_congruence assign_congruence special_congruence branch_congruence body_congruence
    return_congruence enter_congruence_ci_for event_congruence TD_side_always_join_Interp_solve_c
  defines
    congruence_unit_spec = congruence_join.analysis_spec
    and congruence_unit_root_query = congruence_join.root_query
    and congruence_unit_equations = congruence_join.equations
    and congruence_unit_solution = congruence_join.solution
    and congruence_unit_terminates = congruence_join.terminates
    and congruence_unit_vars = congruence_join.sol_vars
    and congruence_unit_env = congruence_join.sol_env
    and congruence_unit_result = congruence_join.result
    and congruence_unit_globals = congruence_join.globals
    and congruence_unit_solved = congruence_join.solved
    and congruence_unit_state_at = congruence_join.state_at
    and congruence_unit_report = congruence_join.report
    and congruence_unit_report_with_state = congruence_join.report_with_state
proof (rule unit_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule congruence_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule congruence_tf_st_for_commute[unfolded congruence_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule congruence_enter_st_for_commute)
next
  case (4 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (5 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.finite_stabl_solve)
next
  case (6 c d s) then show ?case by (rule congruence_classify_check_proved)
next
  case (7 c d s) then show ?case by (rule congruence_classify_check_refuted)
next
  case 8 show ?case by (rule refl)
next
  case (9 gs) show ?case by (rule congruence_cinit_gamma)
next
  case (10 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.solve_dom_of_solve_c)
qed

text \<open>
  A named \<^type>\<open>dg_spec\<close> that code generation can reach declares its own
  unfolding, next to the definition, so a specification never has to be given a
  most general ML type.
\<close>

declare congruence_unit_spec_def [code_unfold]

subsection \<open>Per origin\<close>

global_interpretation congruence_po_asm: unit_dg_analysis
    congruence_tf_st_for congruence_enter_st_for cinit_congruence_st
    TD_side_per_origin_Interp_solve
    "TD_side_per_origin_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)"
    bot congruence_classify_check
    skip_congruence assign_congruence special_congruence branch_congruence body_congruence
    return_congruence enter_congruence_ci_for event_congruence TD_side_per_origin_Interp_solve_c
  defines
    congruence_po_solution = congruence_po_asm.solution
    and congruence_po_terminates = congruence_po_asm.terminates
    and congruence_po_vars = congruence_po_asm.sol_vars
    and congruence_po_result = congruence_po_asm.result
    and congruence_po_state_at = congruence_po_asm.state_at
    and congruence_po_report = congruence_po_asm.report
proof (rule unit_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule congruence_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule congruence_tf_st_for_commute[unfolded congruence_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule congruence_enter_st_for_commute)
next
  case (4 eqs x) then show ?case
    by (rule TD_side_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (5 eqs x) then show ?case
    by (rule TD_side_per_origin_Interp.finite_stabl_solve)
next
  case (6 c d s) then show ?case by (rule congruence_classify_check_proved)
next
  case (7 c d s) then show ?case by (rule congruence_classify_check_refuted)
next
  case 8 show ?case by (rule refl)
next
  case (9 gs) show ?case by (rule congruence_cinit_gamma)
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

lemma congruence_po_equations_eq: "congruence_po_asm.equations = congruence_unit_equations"
  by (rule ext)+
     (simp add: congruence_po_asm.equations_def congruence_join.equations_def
        congruence_po_asm.analysis_spec_def congruence_join.analysis_spec_def)

end
