theory Interval_Ctx_Call_String_Sound
  imports
    Interval_Ctx_Entry_State_Sound
    "Voblint_Core.Call_String_Context"
begin

section \<open>Generic executable call-string context analysis for Interval\<close>

text \<open>
  The call-string sibling of \<open>Interval_Ctx_Entry_State_Sound\<close>'s entry-state pipeline:
  same \<open>ectx_spec\<close> D/G specification, same executable Warrow solve, routed at
  \<^const>\<open>Call_String_Context.cs_route\<close> with a runtime bound \<open>k\<close> instead of at the
  entered callee formals. Every commutation fact the entry-state pipeline
  proves against \<open>ectx_spec\<close> (\<open>ivl_Hstep_lifted_for\<close>, \<open>ivl_Henter_lifted_for\<close>,
  \<open>ivl_Hcomb_lifted_for\<close>, \<open>dg_reader_commute_gen_ivl_lifted\<close>) is already generic
  in the routing policy, so nothing here re-derives them.

  This covers only the executable/result/report path, mirroring exactly what
  \<open>Interval_Ctx_Entry_State_Sound\<close>'s own unconditional section
  (\<open>analyse_interval_entry_state_result_for\<close> onward) provides: no premise here
  needs \<open>call_fwd\<close>/\<open>comb_fwd\<close> (\<open>Call_String_Routed_Context\<close>),
  matching the entry-state pipeline's own current posture, where the shipped
  \<^const>\<open>analyse_interval_entry_state_result_for\<close> is likewise unconditional and
  the generic activation-collecting-soundness theorem is separate, open work.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

text \<open>
  \<^const>\<open>Call_String_Context.cs_route\<close>, applied to \<open>k\<close>, is already exactly the
  four-argument \<open>pp \<Rightarrow> call_string \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> call_string\<close> route
  \<open>side_cfg_T_eff_keyed_seed_dg_buffered\<close> wants -- unlike entry-state's own
  \<open>entry_state_route_gen\<close>, no wrapper is needed to reach that shape.
\<close>

definition cs_call_string_eqs ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> call_string, call_string_gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "cs_call_string_eqs k gs is_bot_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
       (cs_route k)
       (routed_cmb_g_contribution (ectx_spec gs is_bot_pred)
          Call_String_Context.Global Call_String_Context.Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
       (compile_prog Pi ps) (ectx_spec gs is_bot_pred) Bot (Lifted cinit_ivl_st) Bot"

definition cs_call_string_sol ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "cs_call_string_sol k gs is_bot_pred Pi ps =
     TD_side_warrowing_apinis_Interp_solve (cs_call_string_eqs k gs is_bot_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition cs_call_string_terminates ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "cs_call_string_terminates k gs is_bot_pred Pi ps =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (cs_call_string_eqs k gs is_bot_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma cs_call_string_terminates_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (cs_call_string_eqs k gs is_bot_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "cs_call_string_terminates k gs is_bot_pred Pi ps"
  unfolding cs_call_string_terminates_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Whole-program convenience layer\<close>

definition cs_call_string_eqs_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string, call_string_gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "cs_call_string_eqs_prog k gs p =
     cs_call_string_eqs k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition cs_call_string_sol_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "cs_call_string_sol_prog k gs p =
     cs_call_string_sol k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition cs_call_string_terminates_prog :: "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "cs_call_string_terminates_prog k gs p =
     cs_call_string_terminates k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma cs_call_string_terminates_prog_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (cs_call_string_eqs_prog k gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "cs_call_string_terminates_prog k gs p"
  using assms
  unfolding cs_call_string_terminates_prog_def cs_call_string_eqs_prog_def
  by (rule cs_call_string_terminates_via_solve_c)

section \<open>Solved-result table\<close>

text \<open>
  The solved call-string D/G system, read as a
  \<^typ>\<open>(call_string, ivl abs_state) analysis_result\<close> -- the exact construction
  \<^const>\<open>analyse_interval_entry_state_result_for\<close> already uses, at the
  call-string solve instead of the entry-state one. \<open>result_keys\<close> is the
  solver's own covered-key set, never an enumerated theoretical context space:
  call-string contexts are dynamic and discovered, not statically bounded, the
  same reason entry-state's own key set is solver-discovered rather than
  enumerated.
\<close>

definition analyse_interval_call_string_result_for ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, ivl abs_state) analysis_result" where
  "analyse_interval_call_string_result_for k gs p =
     Analysis_Result
       (fst (cs_call_string_sol_prog k gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (cs_call_string_sol_prog k gs p) (Inl (v, ctx))))))"

declare analyse_interval_call_string_result_for_def [code del]

lemma analyse_interval_call_string_result_for_code [code]:
  "analyse_interval_call_string_result_for k gs p =
     (let sol = cs_call_string_sol_prog k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_call_string_result_for_def Let_def by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and
  \<^const>\<open>prog_main_name\<close>, matching \<^const>\<open>analyse_interval_entry_state_result\<close>'s
  shape, with \<open>k\<close> as an explicit leading runtime argument.\<close>

definition analyse_interval_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, ivl abs_state) analysis_result" where
  "analyse_interval_call_string_result k p =
     analyse_interval_call_string_result_for k (declared_global p) p"

section \<open>Contextual check report\<close>

text \<open>
  Reuses \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> unchanged
  -- both are generic in the context type already, so nothing call-string-specific
  is needed here beyond supplying the call-string result table, exactly mirroring
  \<^const>\<open>entry_state_check_projection\<close>/\<^const>\<open>entry_state_verdict_report_prog\<close>.
\<close>

definition cs_call_string_check_projection ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> (call_string \<times> contextual_verdict) set) list" where
  "cs_call_string_check_projection k p =
     classify_checks_ctx (prog_cfg p)
       (analyse_interval_call_string_result_for k (declared_global p) p)
       interval_classify_check"

definition cs_call_string_verdict_report_prog ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "cs_call_string_verdict_report_prog k p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (cs_call_string_check_projection k p)"

lemma cs_call_string_verdict_report_prog_eq:
  "cs_call_string_verdict_report_prog k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_call_string_result_for k (declared_global p) p)
       interval_classify_check"
  unfolding cs_call_string_verdict_report_prog_def cs_call_string_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_interval_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_call_string_report k p = cs_call_string_verdict_report_prog k p"

section \<open>Solver-choice generalization\<close>

text \<open>
  \<^const>\<open>cs_call_string_eqs\<close> names no solve function -- only \<open>ectx_spec\<close> and
  the routing policy -- so it is exactly as solver-independent as
  \<open>ictx_eqs\<close> at \<open>Ctx_None\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>'s
  \<open>analyse_interval_dg_join_for\<close>/\<open>_per_origin_for\<close> alongside the Warrow
  default). The same routed system is solved under every discipline
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
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (cs_call_string_sol_prog_join k gs p) (Inl (v, ctx))))))"

declare analyse_interval_call_string_result_for_join_def [code del]

lemma analyse_interval_call_string_result_for_join_code [code]:
  "analyse_interval_call_string_result_for_join k gs p =
     (let sol = cs_call_string_sol_prog_join k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_call_string_result_for_join_def Let_def by (rule refl)

definition analyse_interval_call_string_result_for_per_origin ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, ivl abs_state) analysis_result" where
  "analyse_interval_call_string_result_for_per_origin k gs p =
     Analysis_Result
       (fst (cs_call_string_sol_prog_per_origin k gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (cs_call_string_sol_prog_per_origin k gs p) (Inl (v, ctx))))))"

declare analyse_interval_call_string_result_for_per_origin_def [code del]

lemma analyse_interval_call_string_result_for_per_origin_code [code]:
  "analyse_interval_call_string_result_for_per_origin k gs p =
     (let sol = cs_call_string_sol_prog_per_origin k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
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
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (cs_call_string_sol_prog_wpo k gs p) (Inl (v, ctx))))))"

declare analyse_interval_call_string_result_for_wpo_def [code del]

lemma analyse_interval_call_string_result_for_wpo_code [code]:
  "analyse_interval_call_string_result_for_wpo k gs p =
     (let sol = cs_call_string_sol_prog_wpo k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
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

end
