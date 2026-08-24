theory Sign_Ctx_Call_String_Sound
  imports
    "Voblint_Analysis.Sign_Ctx_None_Sound"
    "Voblint_Analysis.Sign_Checks"
    "Voblint_Core.Call_String_Context"
    "Voblint_Core.Call_String_Routed_Context"
begin

section \<open>Sign at the routed spine, instantiated at the call-string context\<close>

text \<open>
  The call-string sibling of \<^theory>\<open>Voblint_Analysis.Sign_Ctx_None_Sound\<close>'s own
  routed-unit-context instance: same \<^const>\<open>sctx_spec\<close>/\<^const>\<open>sctx_abs_spec\<close> D/G
  specification and the same domain-commute facts it already interprets
  (\<^locale>\<open>routed_dg_domain_exec\<close>, \<^theory>\<open>Voblint_Core.DG_Base_Exec\<close>) --
  nothing here re-derives them. Only the routing policy changes, from
  \<^const>\<open>route_unit\<close> to \<^const>\<open>Call_String_Context.cs_route\<close> at a runtime bound
  \<open>k\<close>, and the routed-context locale interpreted changes from
  \<^locale>\<open>unit_routed_context\<close> to \<^locale>\<open>call_string_routed_context\<close>
  (\<^theory>\<open>Voblint_Core.Call_String_Routed_Context\<close>), which is itself already
  generic in the domain and discharges four of its six routing obligations
  for any compiled program, leaving only \<open>call_fwd\<close>/\<open>comb_fwd\<close> as genuine
  per-instance premises -- exactly as Sign's own \<open>call_fwd_ok\<close>/\<open>comb_fwd_ok\<close>
  already are at the unit context.

  This is the architecture-milestone acceptance test: a second context for an
  existing domain, exposed from the existing generic routed-domain
  interpretation and the existing generic call-string context locale, with no
  new Sign-domain mathematics.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

definition scs_eqs ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> call_string, call_string_gk, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "scs_eqs k gs \<Gamma> is_bot_pred Pi ps mnm main =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
       (cs_route k)
       (routed_cmb_g_contribution (sctx_spec gs \<Gamma> is_bot_pred)
          Call_String_Context.Global Call_String_Context.Seed
          (static_resolve (compile_prog Pi ps mnm main)))
       (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
       (compile_prog Pi ps mnm main) (sctx_spec gs \<Gamma> is_bot_pred) Bot (Lifted cinit_sign_st) Bot"

definition scs_sol ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "scs_sol k gs \<Gamma> is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp_solve (scs_eqs k gs \<Gamma> is_bot_pred Pi ps mnm main)
       (cfg_exit (compile_prog Pi ps mnm main), [])"

definition scs_terminates ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "scs_terminates k gs \<Gamma> is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)
       (scs_eqs k gs \<Gamma> is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])"

lemma scs_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (scs_eqs k gs \<Gamma> is_bot_pred Pi ps mnm main)
             (cfg_exit (compile_prog Pi ps mnm main), []) \<noteq> None"
  shows "scs_terminates k gs \<Gamma> is_bot_pred Pi ps mnm main"
  unfolding scs_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Domain commute facts, at the call-string routed spec\<close>

text \<open>
  The same interpretation Sign's unit-context instance makes, at the call-string
  routing policy: \<^locale>\<open>routed_domain_exec\<close> takes the routing functions as
  parameters, so switching from \<^const>\<open>route_unit\<close> to \<^const>\<open>cs_route\<close> at a runtime
  bound \<open>k\<close> is a different instantiation of one derivation, not a second one.
  \<^const>\<open>cs_route\<close> reads only the call site and the incoming string, never the
  incoming abstract value, so the routing-agreement obligation is as free here as it
  is for \<^const>\<open>route_unit\<close>.
\<close>

lemma cs_route_commute: "cs_route k u c' d ca = cs_route k u c' (f d) ca"
  by (simp add: cs_route_def)

context
  fixes gs :: "vname \<Rightarrow> bool" and \<Gamma> :: tyenv and is_bot_pred :: "sign exec_dg_st \<Rightarrow> bool" and k :: nat
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation sign_cs: routed_domain_exec
  gs is_bot_pred "sign_tf_st_for gs \<Gamma>" "sign_enter_st_for \<Gamma> gs" "sign_tf_for gs \<Gamma>"
  Call_String_Context.Global Call_String_Context.Seed "cs_route k" "cs_route k"
  static_resolve static_resolve
  by unfold_locales
     (rule sign_tf_st_for_commute, rule sign_enter_st_for_commute, rule exact, simp,
      rule cs_route_commute, simp add: static_resolve_def)

lemmas sign_cs_pp_abs_gen = sign_cs.pp_abs

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and \<Gamma> :: tyenv and is_bot_pred :: "sign exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com and k :: nat
  assumes solves: "scs_terminates k gs \<Gamma> is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

lemma scs_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)
     (scs_eqs k gs \<Gamma> is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])"
  using solves[unfolded scs_terminates_def] .

lemma scs_pp_st:
  "part_post_solution (scs_eqs k gs \<Gamma> is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])
     (snd (scs_sol k gs \<Gamma> is_bot_pred Pi ps mnm main)) (fst (scs_sol k gs \<Gamma> is_bot_pred Pi ps mnm main))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF scs_solve_dom, of "fst (scs_sol k gs \<Gamma> is_bot_pred Pi ps mnm main)"
             "snd (scs_sol k gs \<Gamma> is_bot_pred Pi ps mnm main)"]
  unfolding scs_sol_def by simp

theorem scs_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global) (cs_route k)
        (routed_cmb_g (sctx_abs_spec gs \<Gamma>) Call_String_Context.Global Call_String_Context.Seed
           (static_resolve (compile_prog Pi ps mnm main)))
        (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
        (compile_prog Pi ps mnm main) (sctx_abs_spec gs \<Gamma>)
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st))
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)))
     (cfg_exit (compile_prog Pi ps mnm main), [])
     (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
        \<circ> snd (scs_sol k gs \<Gamma> is_bot_pred Pi ps mnm main))
     (fst (scs_sol k gs \<Gamma> is_bot_pred Pi ps mnm main))"
proof -
  have pp_buf: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list
          (\<lambda>_. Call_String_Context.Global) (cs_route k)
          (routed_cmb_g_contribution (sctx_spec gs \<Gamma> is_bot_pred)
             Call_String_Context.Global Call_String_Context.Seed
             (static_resolve (compile_prog Pi ps mnm main)))
          (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
          (compile_prog Pi ps mnm main) (sctx_spec gs \<Gamma> is_bot_pred) Bot (Lifted cinit_sign_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), [])
       (snd (scs_sol k gs \<Gamma> is_bot_pred Pi ps mnm main))
       (fst (scs_sol k gs \<Gamma> is_bot_pred Pi ps mnm main))"
    using scs_pp_st unfolding scs_eqs_def by simp
  show ?thesis
    unfolding sctx_abs_spec_def
    using pp_buf unfolding sctx_spec_def by (rule sign_cs_pp_abs_gen[OF exact])
qed

end

subsection \<open>Whole-program convenience layer\<close>

definition scs_eqs_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string, call_string_gk, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "scs_eqs_prog k gs \<Gamma> mnm p =
     scs_eqs k gs \<Gamma> (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition scs_sol_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "scs_sol_prog k gs \<Gamma> mnm p =
     scs_sol k gs \<Gamma> (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition scs_terminates_prog :: "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "scs_terminates_prog k gs \<Gamma> mnm p =
     scs_terminates k gs \<Gamma> (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma scs_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (scs_eqs_prog k gs \<Gamma> mnm p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p)), []) \<noteq> None"
  shows "scs_terminates_prog k gs \<Gamma> mnm p"
  using assms
  unfolding scs_terminates_prog_def scs_eqs_prog_def
  by (rule scs_terminates_via_solve_c)

section \<open>Solved-result table\<close>

text \<open>
  The solved call-string D/G system, read as a \<^typ>\<open>(call_string, sign abs_state)
  analysis_result\<close> -- the exact construction Interval's own call-string result table
  already uses, at Sign's own solve instead of Interval's. The covered-key set is
  the solver's own, never an enumerated theoretical context space, matching
  Interval's own posture.
\<close>

definition analyse_sign_call_string_result_for ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (call_string, sign abs_state) analysis_result" where
  "analyse_sign_call_string_result_for k gs \<Gamma> mnm p =
     Analysis_Result
       (fst (scs_sol_prog k gs \<Gamma> mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (scs_sol_prog k gs \<Gamma> mnm p) (Inl (v, ctx))))))"

declare analyse_sign_call_string_result_for_def [code del]

lemma analyse_sign_call_string_result_for_code [code]:
  "analyse_sign_call_string_result_for k gs \<Gamma> mnm p =
     (let sol = scs_sol_prog k gs \<Gamma> mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_sign_call_string_result_for_def Let_def by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and \<^const>\<open>prog_main_name\<close>,
  matching Interval's own \<open>analyse_interval_call_string_result\<close>'s shape, with \<open>k\<close> as an
  explicit leading runtime argument.\<close>

definition analyse_sign_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, sign abs_state) analysis_result" where
  "analyse_sign_call_string_result k p =
     analyse_sign_call_string_result_for k (declared_global p) (prog_tyenv p) prog_main_name p"

section \<open>Contextual check report\<close>

text \<open>
  Reuses \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> unchanged --
  both are generic in the context type already, so nothing call-string-specific is
  needed here beyond supplying the call-string result table and Sign's own
  \<open>sign_classify_check\<close>, exactly mirroring Interval's own
  \<open>cs_call_string_check_projection\<close>/\<open>cs_call_string_verdict_report_prog\<close>.
\<close>

definition scs_check_projection ::
    "nat \<Rightarrow> tyenv \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> (call_string \<times> contextual_verdict) set) list" where
  "scs_check_projection k \<Gamma> mnm p =
     classify_checks_ctx (prog_cfg mnm p)
       (analyse_sign_call_string_result_for k (declared_global p) \<Gamma> mnm p)
       sign_classify_check"

definition scs_verdict_report_prog ::
    "nat \<Rightarrow> tyenv \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "scs_verdict_report_prog k \<Gamma> mnm p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (scs_check_projection k \<Gamma> mnm p)"

lemma scs_verdict_report_prog_eq:
  "scs_verdict_report_prog k \<Gamma> mnm p =
     classify_checks_verdicts (prog_cfg mnm p)
       (analyse_sign_call_string_result_for k (declared_global p) \<Gamma> mnm p)
       sign_classify_check"
  unfolding scs_verdict_report_prog_def scs_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_sign_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_sign_call_string_report k p = scs_verdict_report_prog k (prog_tyenv p) prog_main_name p"

end
