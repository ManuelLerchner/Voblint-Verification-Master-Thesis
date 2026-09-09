theory Parity_Assembly
  imports
    Parity_Classify
    Parity_Transfer
    Parity_Sound
    "Voblint_Result.Unit_DG_Analysis"
    "Voblint_Solver.TD_Solver_Bridge"
    "TD.TD_side_upd_rule"
begin

section \<open>Parity through the shared unit-context assembly\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>assembly/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Parity at the context-insensitive route: 2 instances of \<^locale>\<open>unit_dg_analysis\<close>, one per
  published solver discipline (\<open>always_join\<close>, \<open>per_origin\<close>), the first being the
  production default. The equation system, the solve, the reader, the result table, the
  report and every soundness endpoint come from that locale; this theory only names
  Parity's own implementation and facts and chooses the disciplines.

  Every obligation is discharged by citing a handwritten fact: Parity's own, or, for
  the three solver contracts, a \<^locale>\<open>TD_side_upd_rule\<close> instance. Only those three mention
  the update rule, which is why a second discipline costs a change of solver name and
  nothing else. Why Parity publishes these disciplines and not others is recorded in
  its README, not here.
\<close>

subsection \<open>Always join\<close>

global_interpretation parity_join: unit_dg_analysis
    parity_tf_st_for parity_enter_st_for cinit_parity_st
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)"
    bot parity_classify_check
    skip_parity assign_parity special_parity branch_parity body_parity return_parity
    enter_parity_ci_for event_parity TD_side_always_join_Interp_solve_c
  defines
    parity_unit_spec = parity_join.analysis_spec
    and parity_unit_root_query = parity_join.root_query
    and parity_unit_equations = parity_join.equations
    and parity_unit_solution = parity_join.solution
    and parity_unit_terminates = parity_join.terminates
    and parity_unit_vars = parity_join.sol_vars
    and parity_unit_env = parity_join.sol_env
    and parity_unit_result = parity_join.result
    and parity_unit_globals = parity_join.globals
    and parity_unit_solved = parity_join.solved
    and parity_unit_state_at = parity_join.state_at
    and parity_unit_report = parity_join.report
    and parity_unit_report_with_state = parity_join.report_with_state
proof (rule unit_dg_analysis.intro, rule routed_dg_analysis.intro,
       goal_cases)
  case (1 gs) show ?case by (rule parity_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule parity_tf_st_for_commute_if_live[unfolded parity_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule parity_enter_st_for_commute)
next
  case (4 gs u ctx d ca) show ?case by simp
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

text \<open>
  A named \<^type>\<open>dg_spec\<close> that code generation can reach declares its own
  unfolding, next to the definition, so a specification never has to be given a
  most general ML type.
\<close>

declare parity_unit_spec_def [code_unfold]

subsection \<open>Per origin\<close>

global_interpretation parity_po_asm: unit_dg_analysis
    parity_tf_st_for parity_enter_st_for cinit_parity_st
    TD_side_per_origin_Interp_solve
    "TD_side_per_origin_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)"
    bot parity_classify_check
    skip_parity assign_parity special_parity branch_parity body_parity return_parity
    enter_parity_ci_for event_parity TD_side_per_origin_Interp_solve_c
  defines
    parity_po_root_query = parity_po_asm.root_query
    and parity_po_solution = parity_po_asm.solution
    and parity_po_terminates = parity_po_asm.terminates
    and parity_po_vars = parity_po_asm.sol_vars
    and parity_po_result = parity_po_asm.result
    and parity_po_state_at = parity_po_asm.state_at
    and parity_po_report = parity_po_asm.report
proof (rule unit_dg_analysis.intro, rule routed_dg_analysis.intro,
       goal_cases)
  case (1 gs) show ?case by (rule parity_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule parity_tf_st_for_commute_if_live[unfolded parity_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule parity_enter_st_for_commute)
next
  case (4 gs u ctx d ca) show ?case by simp
next
  case (5 v ctx) show ?case by simp
next
  case (6 eqs x) then show ?case
    by (rule TD_side_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (7 eqs x) then show ?case
    by (rule TD_side_per_origin_Interp.finite_stabl_solve)
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
    by (rule TD_side_per_origin_Interp.solve_dom_of_solve_c)
qed

subsection \<open>One equation system, 2 disciplines\<close>

text \<open>
  The pipeline builds its equations from the transfer parameters alone and the
  solver parameter never reaches them, so every discipline above solves the
  identical system. Stated, not asserted.
\<close>

lemma parity_po_equations_eq: "parity_po_asm.equations = parity_unit_equations"
  by (rule ext)+
     (simp add: parity_po_asm.equations_def parity_join.equations_def
        parity_po_asm.analysis_spec_def parity_join.analysis_spec_def)

end
