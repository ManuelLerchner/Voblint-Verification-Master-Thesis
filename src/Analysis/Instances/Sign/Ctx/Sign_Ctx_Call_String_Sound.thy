theory Sign_Ctx_Call_String_Sound
  imports
    "Voblint_Analysis.Sign_Ctx_None_Sound"
    "Voblint_Analysis.Sign_Checks"
    "Voblint_Core.Call_String_Context"
    Call_String_Routed_Context
begin

section \<open>Sign at the routed spine, instantiated at the call-string context\<close>

text \<open>
  The call-string sibling of \<^theory>\<open>Voblint_Analysis.Sign_Ctx_None_Sound\<close>'s own
  routed-unit-context instance: same \<^const>\<open>sctx_spec\<close>/\<^const>\<open>sctx_abs_spec\<close> D/G
  specification and the same domain-commute facts it already interprets
  (\<^locale>\<open>routed_dg_domain_exec\<close>, \<^theory>\<open>Voblint_Exec.DG_Base_Exec\<close>) --
  nothing here re-derives them. Only the routing policy changes, from
  \<^const>\<open>route_unit\<close> to \<^const>\<open>Call_String_Context.cs_route\<close> at a runtime bound
  \<open>k\<close>, and the routed-context locale interpreted changes from
  \<^locale>\<open>unit_routed_context\<close> to \<^locale>\<open>call_string_routed_context\<close>
  (\<^theory>\<open>Voblint_Analysis.Call_String_Routed_Context\<close>), which is itself already
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
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> call_string, call_string_gk, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "scs_eqs k gs empty_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
       (cs_route k)
       (\<lambda>ctx' src a. dg_spec_edge_tree (sctx_spec gs empty_pred) a src
          Call_String_Context.Global)
       (routed_cmb_g (sctx_spec gs empty_pred)
          Call_String_Context.Global Call_String_Context.Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
       (compile_prog Pi ps) Bot (Lifted cinit_sign_st) Bot"

definition scs_sol ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "scs_sol k gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (scs_eqs k gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition scs_terminates ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "scs_terminates k gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)
       (scs_eqs k gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma scs_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (scs_eqs k gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "scs_terminates k gs empty_pred Pi ps"
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
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "sign exec_dg_st \<Rightarrow> bool" and k :: nat
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation sign_cs: routed_domain_exec
  gs empty_pred "sign_tf_st_for gs" "sign_enter_st_for gs" "sign_tf_for gs"
  Call_String_Context.Global Call_String_Context.Seed "cs_route k" "cs_route k"
  static_resolve static_resolve
  by unfold_locales
     (rule sign_tf_st_for_commute, rule sign_enter_st_for_commute, rule exact, simp,
      rule cs_route_commute, simp add: static_resolve_def)

lemmas sign_cs_pp_st_gen = sign_cs.pp_st

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "sign exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and k :: nat
  assumes solves: "scs_terminates k gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma scs_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)
     (scs_eqs k gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded scs_terminates_def] .

lemma scs_pp_st:
  "part_post_solution (scs_eqs k gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (scs_sol k gs empty_pred Pi ps)) (fst (scs_sol k gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF scs_solve_dom, of "fst (scs_sol k gs empty_pred Pi ps)"
             "snd (scs_sol k gs empty_pred Pi ps)"]
  unfolding scs_sol_def by simp

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec: the shape \<^locale>\<open>call_string_routed_context\<close> consumes directly.\<close>

theorem scs_pp_routed:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
        (cs_route k)
        (\<lambda>ctx' src a. dg_spec_edge_tree (sctx_spec gs empty_pred) a src
           Call_String_Context.Global)
        (routed_cmb_g (sctx_spec gs empty_pred) Call_String_Context.Global
           Call_String_Context.Seed (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
        (compile_prog Pi ps) Bot (Lifted cinit_sign_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (scs_sol k gs empty_pred Pi ps)) (fst (scs_sol k gs empty_pred Pi ps))"
  using scs_pp_st unfolding scs_eqs_def sctx_spec_def by (rule sign_cs_pp_st_gen[OF exact])
end

subsection \<open>The analysis-level result at the call-string context\<close>

text \<open>
  The call-string instance of \<^locale>\<open>routed_analysis_sound\<close>. Nothing below is
  call-string-specific beyond the routing pair \<^const>\<open>cs_route\<close>/\<^const>\<open>cs_context\<close>
  and the seed-key encoding: the solved-table reader, its two coverage
  obligations and the published result all come from the generic composition,
  which is why this context reaches the same activation-collect theorem the
  unit and entry-state instances reach.
\<close>

definition scs_sg_st ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> call_string + call_string_gk \<Rightarrow> sign exec_dg_st lifted" where
  "scs_sg_st k gs empty_pred Pi ps =
     solved_local_reader (fst (scs_sol k gs empty_pred Pi ps))
                         (snd (scs_sol k gs empty_pred Pi ps))"

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "sign exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and k :: nat
  assumes solves: "scs_terminates k gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov:
      "(cfg_entry (compile_prog Pi ps), []) \<in> fst (scs_sol k gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (scs_sol k gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (scs_sol k gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont d.
        (u, ctx) \<in> fst (scs_sol k gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p, cs_route k u ctx d (CallEdge dst pars args))
              \<in> fst (scs_sol k gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (scs_sol k gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (scs_sol k gs empty_pred Pi ps)"
begin

lemma scs_cinit_le_cinit_sign_st:
  "cinit_stores gs \<subseteq> sctx_gamma gs (Lifted cinit_sign_st) Bot"
  by (auto simp: sctx_gamma_def cinit_stores_def gamma_state_def
                 fun_of_resolved_st_q_for_def fun_of_st_cinit_sign_st_for)

interpretation scs_dg_base: sound_dg_spec "sctx_spec gs empty_pred" "sctx_gamma gs" gs
  by (rule sctx_sound_exec[OF exact])

interpretation scs_adapter: routed_analysis_sound
    "sctx_spec gs empty_pred" "sctx_gamma gs" gs
    "compile_prog Pi ps" Call_String_Context.Global "cs_route k"
    Bot "Lifted cinit_sign_st" Bot
    "snd (scs_sol k gs empty_pred Pi ps)" "fst (scs_sol k gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])"
    Call_String_Context.Seed "cs_context k"
    "map_lift (fun_of_resolved_st_q_for gs)" sign_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree GammaRd ClProved ClRefuted)
  case FinE show ?case using compile_prog_finite by auto
next
  case PP show ?case by (rule scs_pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: sctx_gamma_def)
next
  case (SgUncov v c)
  thus ?case by simp
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (simp add: compile_prog_finite)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff compile_prog_finite)
next
  case (RouteEnterc u ctx dst pars args p cont s)
  show ?case by (rule cs_route_context_agree)
next
  case (CallFwd u ctx dst pars args p cont)
  show ?case using call_fwd_ok[OF CallFwd(1,2)] by (simp add: cs_route_def)
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) by (rule comb_fwd_ok)
next
  case (EnterAgree cl s es dst pars args p cont)
  note ces = EnterAgree(1) and ce = EnterAgree(2)
  obtain dst' pars' args' p' cont' where
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
next
  case (GammaRd d g') show ?case by (simp add: sctx_gamma_def)
next
  case (ClProved c d s) thus ?case by (rule sign_classify_check_proved)
next
  case (ClRefuted c d s) thus ?case by (rule sign_classify_check_refuted)
qed

theorem scs_activation_collect_sound:
  "activation_collect gs (cs_context k) [] (compile_prog Pi ps) (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (scs_sg_st k gs empty_pred Pi ps (Inl (v, ctx))))"
  unfolding scs_sg_st_def
  by (rule scs_adapter.routed_activation_collect_sound
        [OF entry_cov scs_cinit_le_cinit_sign_st])

end

subsection \<open>Whole-program convenience layer\<close>

definition scs_eqs_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string, call_string_gk, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "scs_eqs_prog k gs p =
     scs_eqs k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition scs_sol_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "scs_sol_prog k gs p =
     scs_sol k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition scs_terminates_prog :: "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "scs_terminates_prog k gs p =
     scs_terminates k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma scs_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (scs_eqs_prog k gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "scs_terminates_prog k gs p"
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
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, sign abs_state) analysis_result" where
  "analyse_sign_call_string_result_for k gs p =
     Analysis_Result
       (fst (scs_sol_prog k gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (scs_sol_prog k gs p) (Inl (v, ctx))))))"

declare analyse_sign_call_string_result_for_def [code del]

lemma analyse_sign_call_string_result_for_code [code]:
  "analyse_sign_call_string_result_for k gs p =
     (let sol = scs_sol_prog k gs p; gl = declared_global_vars p
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
     analyse_sign_call_string_result_for k (declared_global p) p"

section \<open>Contextual check report\<close>

text \<open>
  Reuses \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> unchanged --
  both are generic in the context type already, so nothing call-string-specific is
  needed here beyond supplying the call-string result table and Sign's own
  \<open>sign_classify_check\<close>, exactly mirroring Interval's own
  \<open>cs_call_string_check_projection\<close>/\<open>cs_call_string_verdict_report_prog\<close>.
\<close>

definition scs_check_projection ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> (call_string \<times> contextual_verdict) set) list" where
  "scs_check_projection k p =
     classify_checks_ctx (prog_cfg p)
       (analyse_sign_call_string_result_for k (declared_global p) p)
       sign_classify_check"

definition scs_verdict_report_prog ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "scs_verdict_report_prog k p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (scs_check_projection k p)"

lemma scs_verdict_report_prog_eq:
  "scs_verdict_report_prog k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_sign_call_string_result_for k (declared_global p) p)
       sign_classify_check"
  unfolding scs_verdict_report_prog_def scs_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_sign_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_sign_call_string_report k p = scs_verdict_report_prog k p"

end
