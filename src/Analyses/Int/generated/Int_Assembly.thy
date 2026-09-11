theory Int_Assembly
  imports
    Int_Classify
    Int_Transfer
    Int_Sound
    "Voblint_Result.Unit_DG_Analysis"
    "Voblint_Solver.TD_Solver_Bridge"
    "TD.TD_side_upd_rule"
begin

section \<open>Int through the shared unit-context assembly\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Int at the context-insensitive route: 4 instances of \<^locale>\<open>unit_dg_analysis\<close>, one per
  published solver discipline (\<open>warrowing_apinis\<close>, \<open>always_join\<close>, \<open>per_origin\<close>,
  \<open>warrowing_per_origin\<close>), the first being the production default. The equation system,
  the solve, the reader, the result table, the report and every soundness endpoint come
  from that locale; this theory only names Int's own implementation and facts and
  chooses the disciplines.

  Every obligation is discharged by citing a handwritten fact: Int's own, or, for the
  three solver contracts, a \<^locale>\<open>TD_side_upd_rule\<close> instance. Only those three mention the
  update rule, which is why a second discipline costs a change of solver name and
  nothing else. Why Int publishes these disciplines and not others is recorded in its
  README, not here.
\<close>

subsection \<open>Apinis warrowing\<close>

global_interpretation int_warrow_asm: unit_dg_analysis
    "int_tf_st_for Refine_Fixpoint" "int_dom_enter_st_for Refine_Fixpoint" cinit_int_dom_st
    TD_side_warrowing_apinis_Interp_solve
    "TD_side_warrowing_apinis_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
    bot int_classify_check
    skip_int_dom "assign_int_dom Refine_Fixpoint" "special_int_dom Refine_Fixpoint"
    "branch_int_dom_for Refine_Fixpoint" body_int_dom "return_int_dom Refine_Fixpoint"
    "enter_int_dom_ci_for Refine_Fixpoint" event_int_dom TD_side_warrowing_apinis_Interp_solve_c
  defines
    int_unit_spec = int_warrow_asm.analysis_spec
    and int_unit_root_query = int_warrow_asm.root_query
    and int_unit_equations = int_warrow_asm.equations
    and int_unit_solution = int_warrow_asm.solution
    and int_unit_terminates = int_warrow_asm.terminates
    and int_unit_vars = int_warrow_asm.sol_vars
    and int_unit_env = int_warrow_asm.sol_env
    and int_unit_result = int_warrow_asm.result
    and int_unit_globals = int_warrow_asm.globals
    and int_unit_solved = int_warrow_asm.solved
    and int_unit_state_at = int_warrow_asm.state_at
    and int_unit_report = int_warrow_asm.report
    and int_unit_report_with_state = int_warrow_asm.report_with_state
proof (rule unit_dg_analysis.intro, rule routed_dg_analysis.intro,
       goal_cases)
  case (1 gs) show ?case by (rule int_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule int_tf_st_for_commute[unfolded int_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule int_dom_enter_st_for_commute)
next
  case (4 gs u ctx d ca) show ?case by simp
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

text \<open>
  A named \<^type>\<open>dg_spec\<close> that code generation can reach declares its own
  unfolding, next to the definition, so a specification never has to be given a
  most general ML type.
\<close>

declare int_unit_spec_def [code_unfold]

subsection \<open>Always join\<close>

global_interpretation int_join_asm: unit_dg_analysis
    "int_tf_st_for Refine_Fixpoint" "int_dom_enter_st_for Refine_Fixpoint" cinit_int_dom_st
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
    bot int_classify_check
    skip_int_dom "assign_int_dom Refine_Fixpoint" "special_int_dom Refine_Fixpoint"
    "branch_int_dom_for Refine_Fixpoint" body_int_dom "return_int_dom Refine_Fixpoint"
    "enter_int_dom_ci_for Refine_Fixpoint" event_int_dom TD_side_always_join_Interp_solve_c
  defines
    int_join_root_query = int_join_asm.root_query
    and int_join_solution = int_join_asm.solution
    and int_join_terminates = int_join_asm.terminates
    and int_join_vars = int_join_asm.sol_vars
    and int_join_result = int_join_asm.result
    and int_join_state_at = int_join_asm.state_at
    and int_join_report = int_join_asm.report
proof (rule unit_dg_analysis.intro, rule routed_dg_analysis.intro,
       goal_cases)
  case (1 gs) show ?case by (rule int_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule int_tf_st_for_commute[unfolded int_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule int_dom_enter_st_for_commute)
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

subsection \<open>Per origin\<close>

global_interpretation int_po_asm: unit_dg_analysis
    "int_tf_st_for Refine_Fixpoint" "int_dom_enter_st_for Refine_Fixpoint" cinit_int_dom_st
    TD_side_per_origin_Interp_solve
    "TD_side_per_origin_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
    bot int_classify_check
    skip_int_dom "assign_int_dom Refine_Fixpoint" "special_int_dom Refine_Fixpoint"
    "branch_int_dom_for Refine_Fixpoint" body_int_dom "return_int_dom Refine_Fixpoint"
    "enter_int_dom_ci_for Refine_Fixpoint" event_int_dom TD_side_per_origin_Interp_solve_c
  defines
    int_po_root_query = int_po_asm.root_query
    and int_po_solution = int_po_asm.solution
    and int_po_terminates = int_po_asm.terminates
    and int_po_vars = int_po_asm.sol_vars
    and int_po_result = int_po_asm.result
    and int_po_state_at = int_po_asm.state_at
    and int_po_report = int_po_asm.report
proof (rule unit_dg_analysis.intro, rule routed_dg_analysis.intro,
       goal_cases)
  case (1 gs) show ?case by (rule int_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule int_tf_st_for_commute[unfolded int_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule int_dom_enter_st_for_commute)
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
  case (8 c d s) then show ?case by (rule int_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule int_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule int_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_per_origin_Interp.solve_dom_of_solve_c)
qed

subsection \<open>Warrowing per origin\<close>

global_interpretation int_wpo_asm: unit_dg_analysis
    "int_tf_st_for Refine_Fixpoint" "int_dom_enter_st_for Refine_Fixpoint" cinit_int_dom_st
    TD_side_warrowing_per_origin_Interp_solve
    "TD_side_warrowing_per_origin_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
    bot int_classify_check
    skip_int_dom "assign_int_dom Refine_Fixpoint" "special_int_dom Refine_Fixpoint"
    "branch_int_dom_for Refine_Fixpoint" body_int_dom "return_int_dom Refine_Fixpoint"
    "enter_int_dom_ci_for Refine_Fixpoint" event_int_dom TD_side_warrowing_per_origin_Interp_solve_c
  defines
    int_wpo_root_query = int_wpo_asm.root_query
    and int_wpo_solution = int_wpo_asm.solution
    and int_wpo_terminates = int_wpo_asm.terminates
    and int_wpo_vars = int_wpo_asm.sol_vars
    and int_wpo_result = int_wpo_asm.result
    and int_wpo_state_at = int_wpo_asm.state_at
    and int_wpo_report = int_wpo_asm.report
proof (rule unit_dg_analysis.intro, rule routed_dg_analysis.intro,
       goal_cases)
  case (1 gs) show ?case by (rule int_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule int_tf_st_for_commute[unfolded int_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule int_dom_enter_st_for_commute)
next
  case (4 gs u ctx d ca) show ?case by simp
next
  case (5 v ctx) show ?case by simp
next
  case (6 eqs x) then show ?case
    by (rule TD_side_warrowing_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (7 eqs x) then show ?case
    by (rule TD_side_warrowing_per_origin_Interp.finite_stabl_solve)
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
    by (rule TD_side_warrowing_per_origin_Interp.solve_dom_of_solve_c)
qed

subsection \<open>One equation system, 4 disciplines\<close>

text \<open>
  The pipeline builds its equations from the transfer parameters alone and the
  solver parameter never reaches them, so every discipline above solves the
  identical system. Stated, not asserted.
\<close>

lemma int_join_equations_eq: "int_join_asm.equations = int_unit_equations"
  by (rule ext)+
     (simp add: int_join_asm.equations_def int_warrow_asm.equations_def
        int_join_asm.analysis_spec_def int_warrow_asm.analysis_spec_def)

lemma int_po_equations_eq: "int_po_asm.equations = int_unit_equations"
  by (rule ext)+
     (simp add: int_po_asm.equations_def int_warrow_asm.equations_def
        int_po_asm.analysis_spec_def int_warrow_asm.analysis_spec_def)

lemma int_wpo_equations_eq: "int_wpo_asm.equations = int_unit_equations"
  by (rule ext)+
     (simp add: int_wpo_asm.equations_def int_warrow_asm.equations_def
        int_wpo_asm.analysis_spec_def int_warrow_asm.analysis_spec_def)

end
