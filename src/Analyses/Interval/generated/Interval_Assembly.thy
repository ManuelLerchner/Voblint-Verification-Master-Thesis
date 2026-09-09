theory Interval_Assembly
  imports
    Interval_Classify
    Interval_Transfer
    Interval_Sound
    "Voblint_Result.Unit_DG_Analysis"
    "Voblint_Solver.TD_Solver_Bridge"
    "TD.TD_side_upd_rule"
begin

section \<open>Interval through the shared unit-context assembly\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>assembly/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Interval at the context-insensitive route: 4 instances of \<^locale>\<open>unit_dg_analysis\<close>, one
  per published solver discipline (\<open>warrowing_apinis\<close>, \<open>always_join\<close>, \<open>per_origin\<close>,
  \<open>warrowing_per_origin\<close>), the first being the production default. The equation system,
  the solve, the reader, the result table, the report and every soundness endpoint come
  from that locale; this theory only names Interval's own implementation and facts and
  chooses the disciplines.

  Every obligation is discharged by citing a handwritten fact: Interval's own, or, for
  the three solver contracts, a \<^locale>\<open>TD_side_upd_rule\<close> instance. Only those three mention
  the update rule, which is why a second discipline costs a change of solver name and
  nothing else. Why Interval publishes these disciplines and not others is recorded in
  its README, not here.
\<close>

subsection \<open>Apinis warrowing\<close>

global_interpretation interval_warrow_asm: unit_dg_analysis
    ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
    TD_side_warrowing_apinis_Interp_solve
    "TD_side_warrowing_apinis_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)"
    bot interval_classify_check
    skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
    enter_ivl_ci_for event_ivl TD_side_warrowing_apinis_Interp_solve_c
  defines
    interval_td_spec = interval_warrow_asm.analysis_spec
    and interval_td_root_query = interval_warrow_asm.root_query
    and interval_td_equations = interval_warrow_asm.equations
    and interval_td_solution = interval_warrow_asm.solution
    and interval_td_terminates = interval_warrow_asm.terminates
    and interval_td_vars = interval_warrow_asm.sol_vars
    and interval_td_env = interval_warrow_asm.sol_env
    and interval_td_result = interval_warrow_asm.result
    and interval_td_globals = interval_warrow_asm.globals
    and interval_td_solved = interval_warrow_asm.solved
    and interval_td_state_at = interval_warrow_asm.state_at
    and interval_td_report = interval_warrow_asm.report
    and interval_td_report_with_state = interval_warrow_asm.report_with_state
proof (rule unit_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule ivl_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule ivl_tf_st_for_commute[unfolded ivl_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule ivl_enter_st_for_commute)
next
  case (4 eqs x) then show ?case
    by (rule TD_side_warrowing_apinis_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (5 eqs x) then show ?case
    by (rule TD_side_warrowing_apinis_Interp.finite_stabl_solve)
next
  case (6 c d s) then show ?case by (rule interval_classify_check_proved)
next
  case (7 c d s) then show ?case by (rule interval_classify_check_refuted)
next
  case 8 show ?case by (rule refl)
next
  case (9 gs) show ?case by (rule interval_cinit_gamma)
next
  case (10 eqs x) then show ?case
    by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c)
qed

text \<open>
  A named \<^type>\<open>dg_spec\<close> that code generation can reach declares its own
  unfolding, next to the definition, so a specification never has to be given a
  most general ML type.
\<close>

declare interval_td_spec_def [code_unfold]

subsection \<open>Always join\<close>

global_interpretation interval_join_asm: unit_dg_analysis
    ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)"
    bot interval_classify_check
    skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
    enter_ivl_ci_for event_ivl TD_side_always_join_Interp_solve_c
  defines
    interval_join_solution = interval_join_asm.solution
    and interval_join_terminates = interval_join_asm.terminates
    and interval_join_vars = interval_join_asm.sol_vars
    and interval_join_result = interval_join_asm.result
    and interval_join_state_at = interval_join_asm.state_at
    and interval_join_report = interval_join_asm.report
proof (rule unit_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule ivl_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule ivl_tf_st_for_commute[unfolded ivl_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule ivl_enter_st_for_commute)
next
  case (4 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (5 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.finite_stabl_solve)
next
  case (6 c d s) then show ?case by (rule interval_classify_check_proved)
next
  case (7 c d s) then show ?case by (rule interval_classify_check_refuted)
next
  case 8 show ?case by (rule refl)
next
  case (9 gs) show ?case by (rule interval_cinit_gamma)
next
  case (10 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.solve_dom_of_solve_c)
qed

subsection \<open>Per origin\<close>

global_interpretation interval_po_asm: unit_dg_analysis
    ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
    TD_side_per_origin_Interp_solve
    "TD_side_per_origin_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)"
    bot interval_classify_check
    skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
    enter_ivl_ci_for event_ivl TD_side_per_origin_Interp_solve_c
  defines
    interval_po_solution = interval_po_asm.solution
    and interval_po_terminates = interval_po_asm.terminates
    and interval_po_vars = interval_po_asm.sol_vars
    and interval_po_result = interval_po_asm.result
    and interval_po_state_at = interval_po_asm.state_at
    and interval_po_report = interval_po_asm.report
proof (rule unit_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule ivl_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule ivl_tf_st_for_commute[unfolded ivl_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule ivl_enter_st_for_commute)
next
  case (4 eqs x) then show ?case
    by (rule TD_side_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (5 eqs x) then show ?case
    by (rule TD_side_per_origin_Interp.finite_stabl_solve)
next
  case (6 c d s) then show ?case by (rule interval_classify_check_proved)
next
  case (7 c d s) then show ?case by (rule interval_classify_check_refuted)
next
  case 8 show ?case by (rule refl)
next
  case (9 gs) show ?case by (rule interval_cinit_gamma)
next
  case (10 eqs x) then show ?case
    by (rule TD_side_per_origin_Interp.solve_dom_of_solve_c)
qed

subsection \<open>Warrowing per origin\<close>

global_interpretation interval_wpo_asm: unit_dg_analysis
    ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
    TD_side_warrowing_per_origin_Interp_solve
    "TD_side_warrowing_per_origin_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)"
    bot interval_classify_check
    skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
    enter_ivl_ci_for event_ivl TD_side_warrowing_per_origin_Interp_solve_c
  defines
    interval_wpo_solution = interval_wpo_asm.solution
    and interval_wpo_terminates = interval_wpo_asm.terminates
    and interval_wpo_vars = interval_wpo_asm.sol_vars
    and interval_wpo_result = interval_wpo_asm.result
    and interval_wpo_state_at = interval_wpo_asm.state_at
    and interval_wpo_report = interval_wpo_asm.report
proof (rule unit_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule ivl_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule ivl_tf_st_for_commute[unfolded ivl_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule ivl_enter_st_for_commute)
next
  case (4 eqs x) then show ?case
    by (rule TD_side_warrowing_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (5 eqs x) then show ?case
    by (rule TD_side_warrowing_per_origin_Interp.finite_stabl_solve)
next
  case (6 c d s) then show ?case by (rule interval_classify_check_proved)
next
  case (7 c d s) then show ?case by (rule interval_classify_check_refuted)
next
  case 8 show ?case by (rule refl)
next
  case (9 gs) show ?case by (rule interval_cinit_gamma)
next
  case (10 eqs x) then show ?case
    by (rule TD_side_warrowing_per_origin_Interp.solve_dom_of_solve_c)
qed

subsection \<open>One equation system, 4 disciplines\<close>

text \<open>
  The pipeline builds its equations from the transfer parameters alone and the
  solver parameter never reaches them, so every discipline above solves the
  identical system. Stated, not asserted.
\<close>

lemma interval_join_equations_eq: "interval_join_asm.equations = interval_td_equations"
  by (rule ext)+
     (simp add: interval_join_asm.equations_def interval_warrow_asm.equations_def
        interval_join_asm.analysis_spec_def interval_warrow_asm.analysis_spec_def)

lemma interval_po_equations_eq: "interval_po_asm.equations = interval_td_equations"
  by (rule ext)+
     (simp add: interval_po_asm.equations_def interval_warrow_asm.equations_def
        interval_po_asm.analysis_spec_def interval_warrow_asm.analysis_spec_def)

lemma interval_wpo_equations_eq: "interval_wpo_asm.equations = interval_td_equations"
  by (rule ext)+
     (simp add: interval_wpo_asm.equations_def interval_warrow_asm.equations_def
        interval_wpo_asm.analysis_spec_def interval_warrow_asm.analysis_spec_def)

end
