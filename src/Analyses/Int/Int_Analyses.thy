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

chapter \<open>How the Int product is run under each supported context policy\<close>

text \<open>
  The Int product's analysis package -- specification, concretization and
  soundness -- lives in \<^theory>\<open>Voblint_Analysis_Int.Int_Sound\<close> and mentions no
  context. This theory supplies the two contextual configurations: a callee keyed
  on the string of call sites that reached it, and a callee keyed on the abstract
  values its formals hold on entry. Each is one interpretation of the shared
  routed assembly, which owns the equation system, the solve, the covered keys,
  the reader, the result table and the contextual report. The
  context-insensitive configuration is not here: it is \<open>Int_Assembly\<close>'s
  registration of the same assembly at the unit context.

  \<open>mode\<close> is Int's refinement axis and stays free. Every obligation the assembly
  asks for is one of Int's own mode-generic facts, so the registrations below
  hold at an arbitrary \<^typ>\<open>refine_mode\<close> and only the published constants pin
  \<^const>\<open>Refine_Fixpoint\<close>, where a caller needs one concrete choice.

  Solver discipline is a second, independent axis: each context is registered at
  always-join and at Apinis warrowing, which differ in no argument but the solve.

  Global keys are \<^type>\<open>routed_gk\<close> with \<^const>\<open>Analysis_Global\<close> at \<^typ>\<open>unit\<close>,
  since Int publishes no named global of its own; the call-string configuration
  uses the shared \<^typ>\<open>call_string_gk\<close>.
\<close>

section \<open>Int at the call-string context\<close>

text \<open>
  \<^const>\<open>Call_String_Context.cs_route\<close> ignores the value being entered, so the
  routing-agreement obligation is \<open>cs_route_indep_of_data\<close> and nothing about the
  construction varies with the bound \<open>k\<close>. Because \<open>k\<close> is runtime data no
  \<^theory_text>\<open>global_interpretation\<close> can fix it, so the registration is local to a
  context fixing \<open>k\<close> and the published constants below are applications of the
  assembly's own constants at \<^term>\<open>cs_route k\<close>.
\<close>


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
    skip_int_dom "assign_int_dom mode" "special_int_dom mode"
    "branch_int_dom_for mode" body_int_dom "return_int_dom mode"
    "enter_int_dom_ci_for mode" event_int_dom "\<lambda>_. cs_route k"
    TD_side_always_join_Interp_solve_c
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

text \<open>
  The same registration under Apinis warrowing, Int's production default. Only
  the solver moves: always-join has no termination guarantee on the interval
  component once a call string collapses a recursion's contexts.
\<close>

interpretation int_cs_warrow: routed_dg_analysis
    "int_tf_st_for mode" "int_dom_enter_st_for mode" cinit_int_dom_st
    Call_String_Context.Global Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    TD_side_warrowing_apinis_Interp_solve
    "TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk)
       TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
    bot int_classify_check
    skip_int_dom "assign_int_dom mode" "special_int_dom mode"
    "branch_int_dom_for mode" body_int_dom "return_int_dom mode"
    "enter_int_dom_ci_for mode" event_int_dom "\<lambda>_. cs_route k"
    TD_side_warrowing_apinis_Interp_solve_c
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
    by (rule TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF _ surjective_pairing])
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
  The published call-string endpoint. \<^const>\<open>cs_route\<close>'s independence of the
  entered value is the whole of what this policy owes the shared derivation, so
  the routing-function endpoint applies rather than the entry-state one.
\<close>

lemmas analyse_int_call_string_sound =
  int_cs.fun_route_activation_collect_sound[OF cs_route_context_agree]

lemmas analyse_int_call_string_sound_warrow =
  int_cs_warrow.fun_route_activation_collect_sound[OF cs_route_context_agree]

end

section \<open>Int at the entry-state context\<close>

text \<open>
  Keying a callee on the abstract values its formals hold on entry. The route
  reads the callee frame the routed generator has already entered, so obligation
  4 is discharged by \<open>exec_formals_route_commute\<close> from
  \<^theory>\<open>Voblint_Result.Routed_DG_Analysis\<close> rather than by an independence
  fact, and the abstract counterpart \<^const>\<open>formals_route_lifted_gen\<close> is a
  separate parameter from the executable \<^const>\<open>exec_formals_route\<close>.
\<close>

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
    skip_int_dom "assign_int_dom mode" "special_int_dom mode"
    "branch_int_dom_for mode" body_int_dom "return_int_dom mode"
    "enter_int_dom_ci_for mode" event_int_dom "\<lambda>_. formals_route_lifted_gen"
    TD_side_always_join_Interp_solve_c
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

interpretation int_es_warrow: routed_dg_analysis
    "int_tf_st_for mode" "int_dom_enter_st_for mode" cinit_int_dom_st
    "Analysis_Global ()" Activation_Seed exec_formals_route "[]"
    TD_side_warrowing_apinis_Interp_solve
    "TD_side_warrowing_apinis_Interp.solve_dom TYPE((unit, int_dom list) routed_gk)
       TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
    bot int_classify_check
    skip_int_dom "assign_int_dom mode" "special_int_dom mode"
    "branch_int_dom_for mode" body_int_dom "return_int_dom mode"
    "enter_int_dom_ci_for mode" event_int_dom "\<lambda>_. formals_route_lifted_gen"
    TD_side_warrowing_apinis_Interp_solve_c
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
    by (rule TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF _ surjective_pairing])
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
  The published entry-state endpoint: every activation the trace semantics
  admits at an entry context is described by the solved table's entry for that
  context. The admitted-context relation is the one the entry answer induces,
  not the graph of a function on stores, which is why this is the entry-state
  endpoint rather than the routing-function one.
\<close>

lemmas analyse_int_entry_state_sound =
  int_es.entry_state_activation_collect_sound

lemmas analyse_int_entry_state_sound_warrow =
  int_es_warrow.entry_state_activation_collect_sound

end

section \<open>The published call-string constants\<close>

text \<open>
  Fixed at \<^const>\<open>Refine_Fixpoint\<close> with \<open>k\<close> an explicit leading argument. Each
  constant is the corresponding assembly constant applied to Int's
  implementation, the call-string routing pair and the chosen solve; they are
  the assembly's own objects rather than copies, so no equation relates the two.
\<close>

subsection \<open>The call-string result table\<close>
section \<open>Solved-result table\<close>

text \<open>
  The solved call-string D/G system, read as a \<^typ>\<open>(call_string, int_dom abs_state)
  analysis_result\<close> -- the exact construction Sign's and Interval's own call-string
  result tables already use, at Int's own solve. The covered-key set is the
  solver's own, never an enumerated theoretical context space.
\<close>


definition analyse_int_call_string_result_for ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result_for k gs p =
     routed_dg_pipeline.result (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve gs p"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and \<^const>\<open>prog_main_name\<close>,
  matching Sign's own \<open>analyse_sign_call_string_result\<close>'s shape, with \<open>k\<close> as an
  explicit leading runtime argument.\<close>

definition analyse_int_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result k p =
     analyse_int_call_string_result_for k (declared_global p) p"

subsection \<open>The call-string check report\<close>

text \<open>
  Reuses \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> unchanged --
  both are generic in the context type already, so nothing call-string-specific
  is needed here beyond supplying the call-string result table and Int's own
  \<^const>\<open>int_classify_check\<close>, exactly mirroring Sign's own
  \<open>analyse_sign_call_string_report\<close>.
\<close>

definition analyse_int_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_call_string_report k p =
     routed_dg_pipeline.verdict_report (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve int_classify_check (declared_global p) p"

section \<open>The published entry-state constants\<close>

text \<open>
  Fixed at \<^const>\<open>Refine_Fixpoint\<close>, matching Int's production default: the
  registrations above hold at an arbitrary mode, and only this surface, which a
  config-driven caller reaches, needs one concrete choice. \<open>k\<close> has no
  counterpart here -- an entry context is determined by the callee's formals
  rather than by a bound the caller supplies.
\<close>


subsection \<open>The entry-state result table\<close>

text \<open>
  The solved entry-state D/G system, read as a \<^typ>\<open>(int_dom list, int_dom abs_state)
  analysis_result\<close> -- the exact construction Sign's and Interval's own entry-state
  result tables already use, at Int's own solve. The covered-key set is the solver's
  own, never an enumerated theoretical context space.
\<close>

definition analyse_int_entry_state_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_for gs p =
     routed_dg_pipeline.result (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_always_join_Interp_solve gs p"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and \<^const>\<open>prog_main_name\<close>,
  matching \<open>analyse_int_call_string_result\<close>'s shape.\<close>

definition analyse_int_entry_state_result :: "imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result p =
     analyse_int_entry_state_result_for (declared_global p) p"

subsection \<open>The entry-state check report\<close>

text \<open>
  Reuses \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> unchanged --
  both are generic in the context type already, so nothing entry-state-specific is
  needed here beyond supplying the entry-state result table and Int's own
  \<^const>\<open>int_classify_check\<close>.
\<close>

definition analyse_int_entry_state_report ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_entry_state_report p =
     routed_dg_pipeline.verdict_report (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_always_join_Interp_solve int_classify_check (declared_global p) p"

end
