theory Parity_Ctx_Call_String_Sound
  imports
    "Voblint_Analysis.Parity_Sound"
    "Voblint_Analysis.Parity_Checks"
    "Voblint_Core.Routed_Analysis_Sound"
    "Voblint_Core.Call_String_Context"
    Call_String_Routed_Context
begin

section \<open>Parity at the routed spine, instantiated at the call-string context\<close>

text \<open>
  The call-string run of the Parity analysis. Everything about Parity it needs --
  the specification \<^const>\<open>pctx_spec\<close>, its concretization \<^const>\<open>pctx_gamma\<close>, and the
  soundness of one against the other -- is taken from
  \<^theory>\<open>Voblint_Analysis.Parity_Sound\<close> and used as it stands; no fact about parity
  arithmetic, parity transfer or parity readback is restated or reproved here.

  What this theory supplies is the other half: a routing policy. \<^const>\<open>cs_route\<close>
  computes a callee's context by pushing the call site onto the caller's string and
  truncating to a runtime bound \<open>k\<close>, and \<^locale>\<open>call_string_routed_context\<close> already
  discharges four of the six routing obligations for any compiled program and any
  domain. What is left is the equation system this pairing generates, its solved
  table, and the two coverage premises the solver's own reachable set must satisfy.

  The global keys are \<^typ>\<open>call_string_gk\<close> from
  \<^theory>\<open>Voblint_Core.Call_String_Context\<close>, shared with every other call-string-keyed
  instance rather than declared again per domain.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

definition pcs_eqs ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> call_string, call_string_gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pcs_eqs k gs empty_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
       (cs_route k)
       (\<lambda>ctx' src a. dg_spec_edge_tree (pctx_spec gs empty_pred) a src
          (\<lambda>_. Call_String_Context.Global))
       (routed_cmb_g (pctx_spec gs empty_pred)
          Call_String_Context.Global Call_String_Context.Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
       (compile_prog Pi ps) Bot (Lifted cinit_parity_st) Bot"

definition pcs_sol ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pcs_sol k gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (pcs_eqs k gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition pcs_terminates ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "pcs_terminates k gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)
       (pcs_eqs k gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma pcs_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (pcs_eqs k gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "pcs_terminates k gs empty_pred Pi ps"
  unfolding pcs_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Domain commute facts, at the call-string routed spec\<close>

text \<open>
  \<^locale>\<open>routed_domain_exec\<close> takes the routing functions as parameters, so this is the
  same interpretation Parity's unit-context run makes, at a different instantiation.
  \<^const>\<open>cs_route\<close> reads only the call site and the incoming string, never the incoming
  abstract value, so the routing-agreement obligation is free.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool" and k :: nat
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation parity_cs: routed_domain_exec
  gs empty_pred "parity_tf_st_for gs" "parity_enter_st_for gs" "parity_tf_for gs"
  Call_String_Context.Global Call_String_Context.Seed "cs_route k" "cs_route k"
  static_resolve static_resolve
  by unfold_locales
     (rule parity_tf_st_for_commute, rule parity_enter_st_for_commute, rule exact, simp,
      rule cs_route_indep_of_data, simp add: static_resolve_def)

lemmas parity_cs_pp_st_gen = parity_cs.pp_st

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and k :: nat
  assumes solves: "pcs_terminates k gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma pcs_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)
     (pcs_eqs k gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded pcs_terminates_def] .

lemma pcs_pp_st:
  "part_post_solution (pcs_eqs k gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (pcs_sol k gs empty_pred Pi ps)) (fst (pcs_sol k gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF pcs_solve_dom, of "fst (pcs_sol k gs empty_pred Pi ps)"
             "snd (pcs_sol k gs empty_pred Pi ps)"]
  unfolding pcs_sol_def by simp

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec: the shape \<^locale>\<open>call_string_routed_context\<close> consumes directly.\<close>

theorem pcs_pp_routed:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
        (cs_route k)
        (\<lambda>ctx' src a. dg_spec_edge_tree (pctx_spec gs empty_pred) a src
           (\<lambda>_. Call_String_Context.Global))
        (routed_cmb_g (pctx_spec gs empty_pred) Call_String_Context.Global
           Call_String_Context.Seed (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
        (compile_prog Pi ps) Bot (Lifted cinit_parity_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (pcs_sol k gs empty_pred Pi ps)) (fst (pcs_sol k gs empty_pred Pi ps))"
  using pcs_pp_st unfolding pcs_eqs_def pctx_spec_def by (rule parity_cs_pp_st_gen[OF exact])
end

subsection \<open>The analysis-level result at the call-string context\<close>

text \<open>
  Nothing below is call-string-specific beyond the routing pair
  \<^const>\<open>cs_route\<close>/\<^const>\<open>cs_context\<close> and the seed-key encoding: the solved-table
  reader, its two coverage obligations and the published result all come from the
  generic composition, which is why this context reaches the same activation-collect
  theorem the unit context reaches.
\<close>

definition pcs_sg_st ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> call_string + call_string_gk \<Rightarrow> parity exec_dg_st lifted" where
  "pcs_sg_st k gs empty_pred Pi ps =
     solved_local_reader (fst (pcs_sol k gs empty_pred Pi ps))
                         (snd (pcs_sol k gs empty_pred Pi ps))"

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and k :: nat
  assumes solves: "pcs_terminates k gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov:
      "(cfg_entry (compile_prog Pi ps), []) \<in> fst (pcs_sol k gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (pcs_sol k gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (pcs_sol k gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont d.
        (u, ctx) \<in> fst (pcs_sol k gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p, cs_route k u ctx d (CallEdge dst pars args))
              \<in> fst (pcs_sol k gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (pcs_sol k gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (pcs_sol k gs empty_pred Pi ps)"
begin

lemma pcs_cinit_le_cinit_parity_st:
  "cinit_stores gs \<subseteq> pctx_gamma gs (Lifted cinit_parity_st) Bot"
  by (auto simp: pctx_gamma_def cinit_stores_def gamma_state_def
                 fun_of_resolved_st_q_for_def fun_of_st_cinit_parity_st_for)

interpretation pcs_dg_base: sound_dg_spec "pctx_spec gs empty_pred" "pctx_gamma gs" gs
  by (rule pctx_sound_exec[OF exact])

interpretation pcs_adapter: routed_analysis_sound
    "pctx_spec gs empty_pred" "pctx_gamma gs" gs
    "compile_prog Pi ps" Call_String_Context.Global "cs_route k"
    Bot "Lifted cinit_parity_st" Bot
    "snd (pcs_sol k gs empty_pred Pi ps)" "fst (pcs_sol k gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])"
    Call_String_Context.Seed "cs_context k"
    "map_lift (fun_of_resolved_st_q_for gs)" parity_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree GammaRd ClProved ClRefuted)
  case FinE show ?case using compile_prog_finite by auto
next
  case PP show ?case by (rule pcs_pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: pctx_gamma_def)
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
  case (GammaRd d g') show ?case by (simp add: pctx_gamma_def)
next
  case (ClProved c d s) thus ?case by (rule parity_classify_check_proved)
next
  case (ClRefuted c d s) thus ?case by (rule parity_classify_check_refuted)
qed

theorem pcs_activation_collect_sound:
  "activation_collect gs (cs_context k) [] (compile_prog Pi ps) (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (pcs_sg_st k gs empty_pred Pi ps (Inl (v, ctx))))"
  unfolding pcs_sg_st_def
  by (rule pcs_adapter.routed_activation_collect_sound
        [OF entry_cov pcs_cinit_le_cinit_parity_st])

end

subsection \<open>Whole-program convenience layer\<close>

definition pcs_eqs_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string, call_string_gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pcs_eqs_prog k gs p =
     pcs_eqs k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition pcs_sol_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pcs_sol_prog k gs p =
     pcs_sol k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition pcs_terminates_prog :: "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "pcs_terminates_prog k gs p =
     pcs_terminates k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma pcs_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (pcs_eqs_prog k gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "pcs_terminates_prog k gs p"
  using assms
  unfolding pcs_terminates_prog_def pcs_eqs_prog_def
  by (rule pcs_terminates_via_solve_c)

section \<open>Solved-result table\<close>

text \<open>
  The solved call-string D/G system, read as a \<^typ>\<open>(call_string, parity abs_state)
  analysis_result\<close>. The covered-key set is the solver's own, never an enumerated
  theoretical context space.
\<close>

definition analyse_parity_call_string_result_for ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, parity abs_state) analysis_result" where
  "analyse_parity_call_string_result_for k gs p =
     Analysis_Result
       (fst (pcs_sol_prog k gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (pcs_sol_prog k gs p) (Inl (v, ctx))))))"

declare analyse_parity_call_string_result_for_def [code del]

lemma analyse_parity_call_string_result_for_code [code]:
  "analyse_parity_call_string_result_for k gs p =
     (let sol = pcs_sol_prog k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_parity_call_string_result_for_def Let_def by (rule refl)

definition analyse_parity_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, parity abs_state) analysis_result" where
  "analyse_parity_call_string_result k p =
     analyse_parity_call_string_result_for k (declared_global p) p"

section \<open>Contextual check report\<close>

text \<open>
  \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> are generic in the
  context type already, so nothing call-string-specific is needed here beyond supplying
  the call-string result table and Parity's own \<open>parity_classify_check\<close>.
\<close>

definition pcs_check_projection ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> (call_string \<times> contextual_verdict) set) list" where
  "pcs_check_projection k p =
     classify_checks_ctx (prog_cfg p)
       (analyse_parity_call_string_result_for k (declared_global p) p)
       parity_classify_check"

definition pcs_verdict_report_prog ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "pcs_verdict_report_prog k p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (pcs_check_projection k p)"

lemma pcs_verdict_report_prog_eq:
  "pcs_verdict_report_prog k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_parity_call_string_result_for k (declared_global p) p)
       parity_classify_check"
  unfolding pcs_verdict_report_prog_def pcs_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_parity_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_parity_call_string_report k p = pcs_verdict_report_prog k p"

end
