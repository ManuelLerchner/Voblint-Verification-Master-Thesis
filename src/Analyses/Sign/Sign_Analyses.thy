theory Sign_Analyses
  imports
    Sign_Sound
    Sign_Assembly
    Sign_Classify
    Sign_Transfer
    Sign_Exec
    "Voblint_Result.Routed_DG_Analysis"
    "Voblint_Framework.Call_String_Context"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_VIMP.VIMP_Program"
    "TD.TD_side_upd_rule"
begin

chapter \<open>How Sign is run under each context-sensitive policy\<close>

text \<open>
  Sign's analysis package -- its specification, concretization and soundness --
  lives in \<^theory>\<open>Voblint_Analysis_Sign.Sign_Sound\<close> and mentions no context. This
  theory supplies the other half for the two policies that route a call to more
  than one context: the call-string run, which truncates the caller's string at a
  runtime bound, and the entry-state run, which keys a callee on the abstract
  values its formals hold on entry.

  Neither policy has a pipeline of its own here. Both are interpretations of
  \<^locale>\<open>routed_dg_analysis\<close>, which owns the equation system, the solve, the
  covered keys, the reader, the result table, the contextual report and the
  activation-indexed soundness endpoint for every domain at every policy. What
  this theory supplies is Sign's own implementation and facts, the routing
  functions, the solver, and the published names.

  The context-insensitive run is not here either: it is \<open>Sign_Assembly\<close>'s
  \<^theory_text>\<open>global_interpretation\<close> of the shared unit-context assembly.

  Global keys differ per policy and are therefore parameters, not a fixed shape:
  the call-string run keys at \<^type>\<open>call_string_gk\<close>, shared with every other
  call-string-keyed instance, while the entry-state run keys at
  \<^type>\<open>routed_gk\<close> --- \<^const>\<open>Analysis_Global\<close> at \<^typ>\<open>unit\<close>, since Sign
  publishes no named global of its own, and \<^const>\<open>Activation_Seed\<close> carrying a
  callee entry point with its routed context.
\<close>

section \<open>Sign at the call-string context\<close>

text \<open>
  A call string is the last \<open>k\<close> call sites on the stack, so a procedure entered
  from two places is analysed twice rather than once at the join. \<^const>\<open>cs_route\<close>
  never reads the state it is handed, which is what makes
  \<open>fun_route_activation_collect_sound\<close> --- the endpoint for a route that is a
  function of the call site and the caller's context alone --- the applicable one,
  at the trace-semantic counterpart \<^const>\<open>cs_context\<close>.

  \<open>k\<close> is runtime data, so the interpretation is local to a context fixing it and
  the published constants below are applications of the pipeline's own constants
  at \<^term>\<open>cs_route k\<close>. Nothing about the construction changes with \<open>k\<close>.
\<close>

context
  fixes k :: nat
begin

interpretation sign_cs: routed_dg_analysis
    sign_tf_st_for sign_enter_st_for cinit_sign_st
    Call_String_Context.Global Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
       TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)"
    bot sign_classify_check
    skip_sign assign_sign special_sign branch_sign body_sign return_sign
    enter_sign_ci_for event_sign "\<lambda>_. cs_route k"
    TD_side_always_join_Interp_solve_c
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule sign_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule sign_tf_st_for_commute[unfolded sign_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule sign_enter_st_for_commute)
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
  case (8 c d s) then show ?case by (rule sign_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule sign_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule sign_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.solve_dom_of_solve_c)
qed

text \<open>
  The published call-string endpoint: every activation the trace semantics admits
  at a call string is described by the solved table's entry for that string.
  \<^const>\<open>cs_route\<close>'s independence of the entered value is the whole of what this
  policy owes the shared derivation.
\<close>

lemmas analyse_sign_call_string_sound =
  sign_cs.fun_route_activation_collect_sound[OF cs_route_context_agree]

lemmas analyse_sign_call_string_terminates_of_solve_c =
  sign_cs.terminates_of_solve_c

end

subsection \<open>The published call-string constants\<close>

text \<open>
  \<open>k\<close> is an explicit leading runtime argument, and each constant is the
  corresponding \<^locale>\<open>routed_dg_pipeline\<close> constant applied to Sign's
  implementation, the call-string routing pair and the always-join solver. They
  are the assembly's own objects, not copies of them, so no equation relates the
  two.
\<close>

definition analyse_sign_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, sign abs_state) analysis_result" where
  "analyse_sign_call_string_result k p =
     routed_dg_pipeline.result sign_tf_st_for sign_enter_st_for cinit_sign_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve (declared_global p) p"

definition analyse_sign_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_sign_call_string_report k p =
     routed_dg_pipeline.verdict_report sign_tf_st_for sign_enter_st_for cinit_sign_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve sign_classify_check (declared_global p) p"

definition analyse_sign_call_string_terminates ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "analyse_sign_call_string_terminates k p =
     routed_dg_pipeline.terminates sign_tf_st_for sign_enter_st_for cinit_sign_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
          TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state))
       (declared_global p) p"

section \<open>Sign at the entry-state context\<close>

text \<open>
  Keying a callee on the abstract values its formals hold on entry.
  \<^const>\<open>exec_formals_route\<close> genuinely reads the state it is handed --- the callee
  frame the routed generator has already entered --- so the applicable endpoint is
  \<open>entry_state_activation_collect_sound\<close>, whose admitted-context relation is the
  one the entry answer induces rather than the graph of a function on stores.

  Nothing here is Sign-specific beyond the domain package itself: the route, its
  agreement with \<^const>\<open>formals_route_lifted_gen\<close> on read-back states, and the
  entry coverage all come from the shared assembly.
\<close>

global_interpretation sign_es: routed_dg_analysis
    sign_tf_st_for sign_enter_st_for cinit_sign_st
    "Analysis_Global ()" Activation_Seed exec_formals_route "[]"
    TD_side_always_join_Interp_solve
    "TD_side_always_join_Interp.solve_dom TYPE((unit, sign list) routed_gk)
       TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)"
    bot sign_classify_check
    skip_sign assign_sign special_sign branch_sign body_sign return_sign
    enter_sign_ci_for event_sign "\<lambda>_. formals_route_lifted_gen"
    TD_side_always_join_Interp_solve_c
  defines
    sign_entry_state_spec = sign_es.analysis_spec
    and sign_entry_state_root_query = sign_es.root_query
    and sign_entry_state_equations = sign_es.equations
    and sign_entry_state_solution = sign_es.solution
    and sign_entry_state_terminates_for = sign_es.terminates
    and sign_entry_state_vars = sign_es.sol_vars
    and sign_entry_state_env = sign_es.sol_env
    and analyse_sign_entry_state_result_for = sign_es.result
    and analyse_sign_entry_state_report_for = sign_es.verdict_report
    and analyse_sign_entry_state_projection_for = sign_es.check_projection
    and sign_entry_state_context_rel = sign_es.admitted_contexts
proof (rule routed_dg_analysis.intro, goal_cases)
  case (1 gs) show ?case by (rule sign_is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule sign_tf_st_for_commute[unfolded sign_tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule sign_enter_st_for_commute)
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
  case (8 c d s) then show ?case by (rule sign_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule sign_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule sign_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_always_join_Interp.solve_dom_of_solve_c)
qed

text \<open>
  A named \<^type>\<open>dg_spec\<close> that code generation can reach declares its own
  unfolding, next to the definition, so a specification never has to be given a
  most general ML type.
\<close>

declare sign_entry_state_spec_def [code_unfold]

subsection \<open>The published entry-state constants\<close>

text \<open>Convenience instances at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching the
  call-string constants' shape.\<close>

definition analyse_sign_entry_state_result ::
    "imp_prog \<Rightarrow> (sign list, sign abs_state) analysis_result" where
  "analyse_sign_entry_state_result p =
     analyse_sign_entry_state_result_for (declared_global p) p"

definition analyse_sign_entry_state_report ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_sign_entry_state_report p =
     analyse_sign_entry_state_report_for (declared_global p) p"

definition analyse_sign_entry_state_terminates :: "imp_prog \<Rightarrow> bool" where
  "analyse_sign_entry_state_terminates p =
     sign_entry_state_terminates_for (declared_global p) p"

lemmas analyse_sign_entry_state_sound =
  sign_es.entry_state_activation_collect_sound

end

