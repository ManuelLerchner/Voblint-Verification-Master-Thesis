theory Interval_Solver_Analyses
  imports Interval_Analyses
begin

chapter \<open>The contextual Interval configurations, at the alternative solver disciplines\<close>

text \<open>
  Which solver runs an equation system is independent of which context policy
  generated it. \<^theory>\<open>Voblint_Analysis_Interval.Interval_Analyses\<close> fixes the
  call-string and entry-state policies at the default always-join solver; this theory
  re-runs those same equation systems under the PerOrigin, Apinis-warrowing and
  warrowing-per-origin disciplines, and publishes the result and report tables the
  configuration-driven entry point dispatches to.

  The context-insensitive route is deliberately absent. That one is
  \<^theory>\<open>Voblint_Analysis_Interval.Interval_Assembly\<close>'s four interpretations of
  \<^locale>\<open>unit_dg_analysis\<close>, which take the solver as a locale parameter, so a
  discipline there costs one interpretation rather than a repeated block. The two
  policies below route calls to more than one context, which that assembly's fixed
  unit route cannot express, so they still name each solve explicitly.
\<close>


text \<open>
  \<^const>\<open>cs_call_string_eqs\<close> names no solve function -- only \<open>interval_spec\<close> and
  the routing policy -- so it is exactly as solver-independent as
  \<open>interval_conf_eqs_prog\<close> at \<open>Ctx_None\<close>, which the four
  \<^theory>\<open>Voblint_Analysis_Interval.Interval_Assembly\<close> interpretations all solve. The same routed system is solved under every discipline
  below, mirroring that pattern precisely; \<open>cs_call_string_sol_prog\<close> (Warrow,
  the shipped default) is untouched.
\<close>

definition cs_call_string_sol_prog_join ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "cs_call_string_sol_prog_join k gs p =
     TD_side_always_join_Interp_solve (cs_call_string_eqs_prog k gs p)
       (cfg_exit (prog_cfg p), [])"

definition cs_call_string_sol_prog_per_origin ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "cs_call_string_sol_prog_per_origin k gs p =
     TD_side_per_origin_Interp_solve (cs_call_string_eqs_prog k gs p)
       (cfg_exit (prog_cfg p), [])"

definition analyse_interval_call_string_result_for_join ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, ivl abs_state) analysis_result" where
  "analyse_interval_call_string_result_for_join k gs p =
     Analysis_Result
       (fst (cs_call_string_sol_prog_join k gs p))
       (\<lambda>v ctx. readback_result_value gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (cs_call_string_sol_prog_join k gs p) (Inl (v, ctx))))))"

declare analyse_interval_call_string_result_for_join_def [code del]

lemma analyse_interval_call_string_result_for_join_code [code]:
  "analyse_interval_call_string_result_for_join k gs p =
     (let sol = cs_call_string_sol_prog_join k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. readback_result_value gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_call_string_result_for_join_def Let_def by (rule refl)

definition analyse_interval_call_string_result_for_per_origin ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, ivl abs_state) analysis_result" where
  "analyse_interval_call_string_result_for_per_origin k gs p =
     Analysis_Result
       (fst (cs_call_string_sol_prog_per_origin k gs p))
       (\<lambda>v ctx. readback_result_value gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (cs_call_string_sol_prog_per_origin k gs p) (Inl (v, ctx))))))"

declare analyse_interval_call_string_result_for_per_origin_def [code del]

lemma analyse_interval_call_string_result_for_per_origin_code [code]:
  "analyse_interval_call_string_result_for_per_origin k gs p =
     (let sol = cs_call_string_sol_prog_per_origin k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. readback_result_value gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_call_string_result_for_per_origin_def Let_def by (rule refl)

definition cs_call_string_verdict_report_prog_join ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "cs_call_string_verdict_report_prog_join k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_call_string_result_for_join k (declared_global p) p)
       interval_classify_check"

definition cs_call_string_verdict_report_prog_per_origin ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "cs_call_string_verdict_report_prog_per_origin k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_call_string_result_for_per_origin k (declared_global p) p)
       interval_classify_check"

definition analyse_interval_call_string_report_join ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_call_string_report_join k p =
     cs_call_string_verdict_report_prog_join k p"

definition analyse_interval_call_string_report_per_origin ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_call_string_report_per_origin k p =
     cs_call_string_verdict_report_prog_per_origin k p"

definition cs_call_string_sol_prog_wpo ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "cs_call_string_sol_prog_wpo k gs p =
     TD_side_warrowing_per_origin_Interp_solve (cs_call_string_eqs_prog k gs p)
       (cfg_exit (prog_cfg p), [])"

definition analyse_interval_call_string_result_for_wpo ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, ivl abs_state) analysis_result" where
  "analyse_interval_call_string_result_for_wpo k gs p =
     Analysis_Result
       (fst (cs_call_string_sol_prog_wpo k gs p))
       (\<lambda>v ctx. readback_result_value gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (cs_call_string_sol_prog_wpo k gs p) (Inl (v, ctx))))))"

declare analyse_interval_call_string_result_for_wpo_def [code del]

lemma analyse_interval_call_string_result_for_wpo_code [code]:
  "analyse_interval_call_string_result_for_wpo k gs p =
     (let sol = cs_call_string_sol_prog_wpo k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. readback_result_value gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_call_string_result_for_wpo_def Let_def by (rule refl)

definition cs_call_string_verdict_report_prog_wpo ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "cs_call_string_verdict_report_prog_wpo k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_call_string_result_for_wpo k (declared_global p) p)
       interval_classify_check"

definition analyse_interval_call_string_report_wpo ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_call_string_report_wpo k p =
     cs_call_string_verdict_report_prog_wpo k p"


section \<open>Solver-choice generalization\<close>

text \<open>
  \<^const>\<open>entry_state_eqs\<close> names no solve function -- only \<open>interval_spec\<close> and
  the routing policy -- so it is exactly as solver-independent as
  \<open>interval_conf_eqs_prog\<close> at \<open>Ctx_None\<close>, which the four
  \<^theory>\<open>Voblint_Analysis_Interval.Interval_Assembly\<close> interpretations all solve, and exactly as its own
  the call-string configuration above sibling solves the routed call-string
  system under every discipline. \<^const>\<open>entry_state_sol_prog\<close> (Warrow,
  the shipped default) is untouched.
\<close>

definition entry_state_sol_prog_join ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + (unit, ivl list) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog_join gs p =
     TD_side_always_join_Interp_solve (entry_state_eqs_prog gs p)
       (cfg_exit (prog_cfg p), [])"

definition entry_state_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + (unit, ivl list) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog_per_origin gs p =
     TD_side_per_origin_Interp_solve (entry_state_eqs_prog gs p)
       (cfg_exit (prog_cfg p), [])"

definition analyse_interval_entry_state_result_for_join ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for_join gs p =
     Analysis_Result
       (fst (entry_state_sol_prog_join gs p))
       (\<lambda>v ctx. readback_result_value gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog_join gs p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_join_def [code del]

lemma analyse_interval_entry_state_result_for_join_code [code]:
  "analyse_interval_entry_state_result_for_join gs p =
     (let sol = entry_state_sol_prog_join gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. readback_result_value gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_join_def Let_def by (rule refl)

definition analyse_interval_entry_state_result_for_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for_per_origin gs p =
     Analysis_Result
       (fst (entry_state_sol_prog_per_origin gs p))
       (\<lambda>v ctx. readback_result_value gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog_per_origin gs p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_per_origin_def [code del]

lemma analyse_interval_entry_state_result_for_per_origin_code [code]:
  "analyse_interval_entry_state_result_for_per_origin gs p =
     (let sol = entry_state_sol_prog_per_origin gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. readback_result_value gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_per_origin_def Let_def by (rule refl)

definition entry_state_verdict_report_prog_join ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog_join p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_entry_state_result_for_join (declared_global p) p)
       interval_classify_check"

definition entry_state_verdict_report_prog_per_origin ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog_per_origin p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_entry_state_result_for_per_origin (declared_global p) p)
       interval_classify_check"

definition analyse_interval_entry_state_join ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_join p = entry_state_verdict_report_prog_join p"

definition analyse_interval_entry_state_per_origin ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_per_origin p =
     entry_state_verdict_report_prog_per_origin p"

definition entry_state_sol_prog_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + (unit, ivl list) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog_wpo gs p =
     TD_side_warrowing_per_origin_Interp_solve (entry_state_eqs_prog gs p)
       (cfg_exit (prog_cfg p), [])"

definition analyse_interval_entry_state_result_for_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for_wpo gs p =
     Analysis_Result
       (fst (entry_state_sol_prog_wpo gs p))
       (\<lambda>v ctx. readback_result_value gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog_wpo gs p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_wpo_def [code del]

lemma analyse_interval_entry_state_result_for_wpo_code [code]:
  "analyse_interval_entry_state_result_for_wpo gs p =
     (let sol = entry_state_sol_prog_wpo gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. readback_result_value gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_wpo_def Let_def by (rule refl)

definition entry_state_verdict_report_prog_wpo ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog_wpo p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_entry_state_result_for_wpo (declared_global p) p)
       interval_classify_check"

definition analyse_interval_entry_state_wpo ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_wpo p =
     entry_state_verdict_report_prog_wpo p"

end
