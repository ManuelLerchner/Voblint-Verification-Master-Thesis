theory Parity_Analyses
  imports
    Parity_Sound
    Parity_Classify
    Parity_Transfer
    Parity_Exec
    "Voblint_Result.Routed_DG_Analysis"
    "Voblint_Framework.Call_String_Context"
    "Voblint_Framework.Routed_Context"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_VIMP.VIMP_Program"
    "TD.TD_side_upd_rule"
begin

chapter \<open>How Parity is run under each context-sensitive policy\<close>
text \<open>
  Parity's analysis package -- its specification, concretization and soundness --
  lives in \<^theory>\<open>Voblint_Analysis_Parity.Parity_Sound\<close> and mentions no context.
  This theory supplies the other half for the two policies that route a call to
  more than one context: the call-string run, which truncates the caller's string
  at a runtime bound, and the entry-state run, which keys a callee on the abstract
  values its formals hold on entry.

  Neither policy has a pipeline of its own here. Both are interpretations of
  \<^locale>\<open>routed_dg_analysis\<close>, the same one Sign and Interval interpret; the
  context-insensitive run is \<open>Parity_Assembly\<close>'s interpretation of the unit
  assembly. What this theory supplies is Parity's own implementation and facts,
  the routing functions, the solver, and the published names.

  Parity's transfer commutes with the readback unconditionally, which is stronger
  than the shared contract asks for. The registration cites the conditional
  corollary \<open>parity_tf_st_for_commute_if_live\<close>, discharged by
  \<^theory>\<open>Voblint_Analysis_Parity.Parity_Exec\<close>, rather than weakening the domain's
  own theorem, exactly as the unit registration does; nothing here is a
  Parity-specific derivation.
\<close>

section \<open>Parity at the call-string context\<close>

text \<open>
  A call string is the last \<open>k\<close> call sites on the stack, so a procedure entered
  from two places is analysed twice rather than once at the join.
  \<^const>\<open>cs_route\<close> never reads the state it is handed, which is what makes
  \<open>fun_route_activation_collect_sound\<close> --- the endpoint for a route that is a
  function of the call site and the caller's context alone --- the applicable one,
  at the trace-semantic counterpart \<^const>\<open>cs_context\<close>.

  \<open>k\<close> is runtime data, so the interpretation is local to a context fixing it and
  the published constants below are applications of the pipeline's own constants
  at \<^term>\<open>cs_route k\<close>.
\<close>

context
  fixes k :: nat
begin

interpretation parity_cs: routed_dg_analysis
    parity_tf_st_for parity_enter_st_for cinit_parity_st
    Call_String_Context.Global Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
       TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)"
    bot parity_classify_check
    skip_parity assign_parity special_parity branch_parity body_parity return_parity
    enter_parity_ci_for event_parity "\<lambda>_. cs_route k"
    TD_side_always_join_Interp_solve_c
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule parity_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule parity_tf_st_for_commute_if_live[unfolded parity_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule parity_enter_st_for_commute)
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

lemmas analyse_parity_call_string_sound =
  parity_cs.fun_route_activation_collect_sound[OF cs_route_context_agree]

lemmas analyse_parity_call_string_terminates_of_solve_c =
  parity_cs.terminates_of_solve_c

end

subsection \<open>The published call-string constants\<close>

definition analyse_parity_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, parity abs_state) analysis_result" where
  "analyse_parity_call_string_result k p =
     routed_dg_pipeline.result parity_tf_st_for parity_enter_st_for cinit_parity_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve (declared_global p) p"

definition analyse_parity_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_parity_call_string_report k p =
     routed_dg_pipeline.verdict_report parity_tf_st_for parity_enter_st_for
       cinit_parity_st Call_String_Context.Global Call_String_Context.Seed
       (\<lambda>_. cs_route k) [] TD_side_always_join_Interp_solve parity_classify_check
       (declared_global p) p"

definition analyse_parity_call_string_terminates ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "analyse_parity_call_string_terminates k p =
     routed_dg_pipeline.terminates parity_tf_st_for parity_enter_st_for cinit_parity_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
          TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state))
       (declared_global p) p"

section \<open>Parity at the entry-state context\<close>

text \<open>
  Keying a callee on the abstract values its formals hold on entry.
  \<^const>\<open>exec_formals_route\<close> genuinely reads the state it is handed --- the callee
  frame the routed generator has already entered --- so the applicable endpoint is
  \<open>entry_state_activation_collect_sound\<close>, whose admitted-context relation is the
  one the entry answer induces rather than the graph of a function on stores.
\<close>

global_interpretation parity_es: routed_dg_analysis
    parity_tf_st_for parity_enter_st_for cinit_parity_st
    "Analysis_Global ()" Activation_Seed exec_formals_route "[]"
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE((unit, parity list) routed_gk)
       TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)"
    bot parity_classify_check
    skip_parity assign_parity special_parity branch_parity body_parity return_parity
    enter_parity_ci_for event_parity "\<lambda>_. formals_route_lifted_gen"
    TD_side_always_join_Interp_solve_c
  defines
    parity_entry_state_spec = parity_es.analysis_spec
    and parity_entry_state_root_query = parity_es.root_query
    and parity_entry_state_equations = parity_es.equations
    and parity_entry_state_solution = parity_es.solution
    and parity_entry_state_terminates_for = parity_es.terminates
    and parity_entry_state_vars = parity_es.sol_vars
    and parity_entry_state_env = parity_es.sol_env
    and analyse_parity_entry_state_result_for = parity_es.result
    and analyse_parity_entry_state_report_for = parity_es.verdict_report
    and analyse_parity_entry_state_projection_for = parity_es.check_projection
    and parity_entry_state_context_rel = parity_es.admitted_contexts
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule parity_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule parity_tf_st_for_commute_if_live[unfolded parity_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule parity_enter_st_for_commute)
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

declare parity_entry_state_spec_def [code_unfold]

subsection \<open>The published entry-state constants\<close>

definition analyse_parity_entry_state_result ::
    "imp_prog \<Rightarrow> (parity list, parity abs_state) analysis_result" where
  "analyse_parity_entry_state_result p =
     analyse_parity_entry_state_result_for (declared_global p) p"

definition analyse_parity_entry_state_report ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_parity_entry_state_report p =
     analyse_parity_entry_state_report_for (declared_global p) p"

definition analyse_parity_entry_state_terminates :: "imp_prog \<Rightarrow> bool" where
  "analyse_parity_entry_state_terminates p =
     parity_entry_state_terminates_for (declared_global p) p"

lemmas analyse_parity_entry_state_sound =
  parity_es.entry_state_activation_collect_sound

end

