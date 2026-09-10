theory Interval_Solver_Analyses
  imports Interval_Analyses
begin

chapter \<open>The contextual Interval configurations, at the alternative solver disciplines\<close>

text \<open>
  Which solver runs an equation system is independent of which context policy
  generated it. \<^theory>\<open>Voblint_Analysis_Interval.Interval_Analyses\<close> fixes the
  call-string and entry-state policies at Apinis warrowing, the shipped default;
  this theory re-runs those same equation systems under the always-join,
  per-origin and warrowing-per-origin disciplines and publishes the reports the
  configuration-driven entry point dispatches to.

  A discipline costs one definition here because the solver is a parameter of
  \<^locale>\<open>routed_dg_pipeline\<close>, not something the equation system fixed: every
  constant below is that pipeline's own \<open>verdict_report\<close> at Interval's
  implementation, the policy's routing pair, and one solver name. The equation
  system each of them solves is the same term the default discipline solves --
  visibly so, since the solver argument is the only difference between these
  definitions and \<^const>\<open>analyse_interval_call_string_report\<close>.

  The context-insensitive route is deliberately absent. That one is
  \<^theory>\<open>Voblint_Analysis_Interval.Interval_Assembly\<close>'s four interpretations of
  \<^locale>\<open>unit_dg_analysis\<close>.

  These routes publish reports; the coverage endpoints each of them needs come
  from its own registration in
  \<^theory>\<open>Voblint_Analysis_Interval.Interval_Contextual_Assembly\<close>, and the
  source-level soundness of an answer built from one is stated where the
  configuration that dispatches to it is, above the CLI.
\<close>

section \<open>Call-string, at the alternative disciplines\<close>

definition analyse_interval_call_string_report_join ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_call_string_report_join k p =
     routed_dg_pipeline.verdict_report ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve interval_classify_check (declared_global p) p"

definition analyse_interval_call_string_report_per_origin ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_call_string_report_per_origin k p =
     routed_dg_pipeline.verdict_report ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_per_origin_Interp_solve interval_classify_check (declared_global p) p"

definition analyse_interval_call_string_report_wpo ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_call_string_report_wpo k p =
     routed_dg_pipeline.verdict_report ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_per_origin_Interp_solve interval_classify_check
       (declared_global p) p"

section \<open>Entry state, at the alternative disciplines\<close>

definition analyse_interval_entry_state_join ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_join p =
     routed_dg_pipeline.verdict_report ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_always_join_Interp_solve interval_classify_check (declared_global p) p"

definition analyse_interval_entry_state_per_origin ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_per_origin p =
     routed_dg_pipeline.verdict_report ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_per_origin_Interp_solve interval_classify_check (declared_global p) p"

definition analyse_interval_entry_state_wpo ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_wpo p =
     routed_dg_pipeline.verdict_report ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_warrowing_per_origin_Interp_solve interval_classify_check
       (declared_global p) p"

end

