theory Example_Interval_DG_CallString_K
  imports
    Example_Interval_DG_Ctx_Sound
    "Voblint_Analysis.Activation_Backbone"
    "Voblint_Analysis.DG_Ctx_Activation"
    "Voblint_Analysis.Call_String_Context"
begin

section \<open>A computed 2-call-string context, routed by truncated call history\<close>

text \<open>
  Mechanical proof-of-concept for \<^file>\<open>../../../docs/CALLSTRING_CONTEXT_DESIGN.md\<close>: does a
  bounded k-call-string context work as a plain \<^locale>\<open>routed_context\<close> interpretation, the
  same way \<open>Example_Interval_DG_CallString.thy\<close>'s depth-1, untruncated
  \<open>route_cs\<close> already does? This theory answers that mechanically, at \<open>k = 2\<close>, on the same
  \<open>twice\<close> program, consuming \<open>Call_String_Context.thy\<close>'s \<open>cs_route\<close>/\<open>cs_enterc\<close> rather than
  restating them locally.

  \<^bold>\<open>What this does and does not show.\<close> \<open>twice\<close>'s two calls are both direct children of
  \<open>main\<close> (root context \<open>[]\<close>), so \<open>cs_route 2 u [] d ca = take 2 [u] = [u]\<close> --- the
  2-call-string contexts computed here are observably isomorphic to the 1-call-string contexts
  \<open>Example_Interval_DG_CallString.thy\<close> already computes, just list-wrapped. This theory is
  the design doc's Stage 1 (mechanical: same solver, same domain, no locale changes, trivial
  \<open>route_enterc_agree\<close>) --- it is deliberately \<^emph>\<open>not\<close> Stage 3 (a precision witness needs a
  program with real call nesting, so a k=1 and a k=2 context actually differ; \<open>twice\<close> is too
  shallow for that).
\<close>

subsection \<open>A call-string-keyed global-key type\<close>

datatype gk_2 = Global2 | Seed2 pp "cfg_node list"

subsection \<open>The routed equation system and its computed solution\<close>

definition twice_2_eqs :: "(pp \<times> cfg_node list, gk_2, (ivl st, ivl st) dg_state) eqsT" where
  "twice_2_eqs =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
       (routed_cmb Spoly Global2) (routed_extra twice_cfg Spoly Seed2 Global2)
       twice_cfg Spoly bot cinit_ivl_st (restrict_global_st cinit_ivl_st)"

definition twice_2_sol ::
  "(pp \<times> cfg_node list) set \<times> (pp \<times> cfg_node list + gk_2 \<Rightarrow> (ivl st, ivl st) dg_state)" where
  "twice_2_sol = TD_side_warrowing_apinis_Interp_solve twice_2_eqs
                    (cfg_exit twice_cfg, [])"

lemma twice_2_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c twice_2_eqs (cfg_exit twice_cfg, [])
     \<noteq> None"
  by eval

subsection \<open>The two calling contexts, truncated to length 2\<close>

definition ctx_call1_2 :: "cfg_node list" where "ctx_call1_2 = [Statement 2]"
definition ctx_call2_2 :: "cfg_node list" where "ctx_call2_2 = [Statement 3]"

lemma contexts_distinct_2: "ctx_call1_2 \<noteq> ctx_call2_2"
  by (simp add: ctx_call1_2_def ctx_call2_2_def)

subsection \<open>Coverage\<close>

lemma entry_covered_2: "(cfg_entry twice_cfg, []) \<in> fst twice_2_sol"
  unfolding twice_2_sol_def twice_2_eqs_def by eval

lemma twice_fwd_closed_all_2:
  "\<forall>(u, c)\<in>fst twice_2_sol. \<forall>(u', a, v)\<in>intra twice_cfg.
      u = u' \<longrightarrow> (v, c) \<in> fst twice_2_sol"
  unfolding twice_2_sol_def twice_2_eqs_def by eval

lemma twice_fwd_closed_2:
  assumes "(u, ctx) \<in> fst twice_2_sol" and "(u, a, v) \<in> intra twice_cfg"
  shows "(v, ctx) \<in> fst twice_2_sol"
  using twice_fwd_closed_all_2 assms by fastforce

lemma callee_covered_call1_2: "(FunctionEntry ''twice'', ctx_call1_2) \<in> fst twice_2_sol"
  unfolding ctx_call1_2_def twice_2_sol_def twice_2_eqs_def by eval
lemma callee_covered_call2_2: "(FunctionEntry ''twice'', ctx_call2_2) \<in> fst twice_2_sol"
  unfolding ctx_call2_2_def twice_2_sol_def twice_2_eqs_def by eval

lemma enter_callers_only_root_2:
  "\<forall>(p, ctx)\<in>fst twice_2_sol.
     (p = Statement 2 \<or> p = Statement 3) \<longrightarrow> ctx = []"
  unfolding twice_2_sol_def twice_2_eqs_def by eval

lemma covered_ret5_2: "(Statement 3, []) \<in> fst twice_2_sol"
  unfolding twice_2_sol_def twice_2_eqs_def by eval
lemma covered_ret7_2: "(Statement 4, []) \<in> fst twice_2_sol"
  unfolding twice_2_sol_def twice_2_eqs_def by eval
lemma callee_exit_covered_call1_2: "(FunctionResult ''twice'', ctx_call1_2) \<in> fst twice_2_sol"
  unfolding twice_2_sol_def twice_2_eqs_def ctx_call1_2_def by eval
lemma callee_exit_covered_call2_2: "(FunctionResult ''twice'', ctx_call2_2) \<in> fst twice_2_sol"
  unfolding twice_2_sol_def twice_2_eqs_def ctx_call2_2_def by eval

section \<open>Abstract transport of the routed solution\<close>

text \<open>Same argument as \<open>Example_Interval_DG_CallString\<close>'s \<open>route_cs\<close> commute lemmas:
  \<open>cs_route\<close> ignores its data argument, so every \<^const>\<open>Side\<close> key computed from it is
  literally the same term on the executable and the abstract carrier.\<close>

lemma dg_tree_st_commute_frame_read_2:
  "dg_tree_st_commute env
     (QueryG (Seed2 v ctx) (\<lambda>s. Answer (DG (globs s) bot)))
     (QueryG (Seed2 v ctx) (\<lambda>s. Answer (DG (globs s) bot)))"
  by (simp add: dg_tree_st_commute_def fun_of_dg_st_simps fun_of_st_bot o_def
                dep_aux_def bot_fun_def)

lemma dg_tree_st_commute_routed_cmb_2:
  "dg_tree_st_commute env (routed_cmb Spoly Global2 (cs_route 2) ctx ca cc ex)
                          (routed_cmb Sabs Global2 (cs_route 2) ctx ca cc ex)"
  unfolding routed_cmb_def Let_def
  by (cases ca)
     (simp_all add: dg_tree_st_commute_def fun_of_dg_st_simps fun_of_st_bot o_def
                    cs_route_def dgs_combine_fst_commute_gen dgs_combine_snd_commute_gen
                    dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

lemma dg_tree_st_commute_routed_enter_pub_2:
  "dg_tree_st_commute env
     (with_call a (\<lambda>dst fs as. do {
        entry_state \<leftarrow> read_local (v, ctx);
        globals_state \<leftarrow> read_global Global2;
        publish_global Global2 (enter_global Spoly fs as (locals entry_state) (globs globals_state));
        publish_seed (Seed2 w (cs_route 2 v ctx (locals entry_state) a))
          (enter_local Spoly fs as (locals entry_state) (globs globals_state));
        answer_local bot
      }))
     (with_call a (\<lambda>dst fs as. do {
        entry_state \<leftarrow> read_local (v, ctx);
        globals_state \<leftarrow> read_global Global2;
        publish_global Global2 (enter_global Sabs fs as (locals entry_state) (globs globals_state));
        publish_seed (Seed2 w (cs_route 2 v ctx (locals entry_state) a))
          (enter_local Sabs fs as (locals entry_state) (globs globals_state));
        answer_local bot
      }))"
  by (cases a)
     (simp add: dg_tree_st_commute_def fun_of_dg_st_simps fun_of_st_bot o_def
                cs_route_def dgs_enter_fst_commute_gen dgs_enter_snd_commute_gen
                dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

lemma hextra_commute_routed_2:
  "list_all2 (dg_tree_st_commute env)
     (routed_extra twice_cfg Spoly Seed2 Global2 (cs_route 2) ctx w)
     (routed_extra twice_cfg Sabs Seed2 Global2 (cs_route 2) ctx w)"
  unfolding routed_extra_def Let_def
  by (auto simp: list_all2_appendI list_all2_map1 list_all2_map2 list_all2_refl split_beta
                 dg_tree_st_commute_frame_read_2 dg_tree_st_commute_routed_enter_pub_2
           split: cfg_node.split)

lemma twice_2_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk_2) TYPE((ivl st, ivl st) dg_state)
     twice_2_eqs (cfg_exit twice_cfg, [])"
  using twice_2_terminates
  unfolding TD_side_warrowing_apinis_Interp.term_equivalence
            TD_side_warrowing_apinis_Interp.solve_c_dom_def
  by simp

lemma twice_2_pp_st:
  "part_post_solution twice_2_eqs (cfg_exit twice_cfg, [])
     (snd twice_2_sol) (fst twice_2_sol)"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF twice_2_solve_dom, of "fst twice_2_sol" "snd twice_2_sol"]
  unfolding twice_2_sol_def by simp

theorem twice_2_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
        (routed_cmb Sabs Global2) (routed_extra twice_cfg Sabs Seed2 Global2) twice_cfg Sabs
        (fun_of_st (bot::ivl st)) (fun_of_st cinit_ivl_st) (fun_of_st (restrict_global_st cinit_ivl_st)))
     (cfg_exit twice_cfg, []) (fun_of_dg_st \<circ> snd twice_2_sol) (fst twice_2_sol)"
proof -
  have pp': "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
          (routed_cmb Spoly Global2) (routed_extra twice_cfg Spoly Seed2 Global2) twice_cfg Spoly
          bot cinit_ivl_st (restrict_global_st cinit_ivl_st))
       (cfg_exit twice_cfg, []) (snd twice_2_sol) (fst twice_2_sol)"
    using twice_2_pp_st unfolding twice_2_eqs_def by simp
  have ivl_Hstep_2:
    "map_prod fun_of_st fun_of_st (dg_spec_step Spoly a d g') =
       dg_spec_step Sabs a (fun_of_st d) (fun_of_st g')" for a d g'
    unfolding Spoly_def by (rule ivl_Hstep)
  show ?thesis
    by (rule part_post_solution_seed_dg_st_to_abs
          [where pred_sel = intra_predecessor_list and gkey = "\<lambda>_. Global2"
             and route_st = "cs_route 2" and route_abs = "cs_route 2"
             and cmb_st = "routed_cmb Spoly Global2" and cmb_abs = "routed_cmb Sabs Global2"
             and extra_st = "routed_extra twice_cfg Spoly Seed2 Global2"
             and extra_abs = "routed_extra twice_cfg Sabs Seed2 Global2"
             and g = twice_cfg and S_st = Spoly and S_abs = Sabs,
           OF ivl_Hstep_2 cs_route_indep_of_data dg_tree_st_commute_routed_cmb_2
              hextra_commute_routed_2 pp'])
qed

section \<open>Activation-indexed collecting soundness for the 2-call-string-routed solution\<close>

abbreviation sigma_2 :: "pp \<times> cfg_node list + gk_2 \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state" where
  "sigma_2 \<equiv> fun_of_dg_st \<circ> snd twice_2_sol"

abbreviation gen_2_abs :: "(pp \<times> cfg_node list, gk_2, (ivl abs_state, ivl abs_state) dg_state) eqsT" where
  "gen_2_abs \<equiv> side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
       (routed_cmb Sabs Global2) (routed_extra twice_cfg Sabs Seed2 Global2) twice_cfg Sabs
       (fun_of_st (bot::ivl st)) (fun_of_st cinit_ivl_st) (fun_of_st (restrict_global_st cinit_ivl_st))"

lemma pp_eq_bound_2:
  "(v, ctx) \<in> fst twice_2_sol
     \<Longrightarrow> eq gen_2_abs (v, ctx) sigma_2 \<le> sigma_2 (Inl (v, ctx))"
  using twice_2_pp_abs by simp

lemma side_acc_dg_ge_2: "acc \<le> side_acc_dg acc \<tau> ts"
proof (induction ts arbitrary: acc)
  case (Cons t ts)
  show ?case
    using Cons.IH[of "acc \<squnion> locals (traverse_rhs t \<tau>)"]
    by (simp add: le_supI1)
qed simp

definition ivl_ctx_sg_2 :: "pp \<times> cfg_node list + gk_2 \<Rightarrow> ivl abs_state" where
  "ivl_ctx_sg_2 k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst twice_2_sol
           then locals (sigma_2 (Inl (v, ctx))) \<squnion> globs (sigma_2 (Inr Global2))
           else bot)
      | Inr _ \<Rightarrow> bot)"

lemma ivl_ctx_sg_2_covered:
  "(v, ctx) \<in> fst twice_2_sol
   \<Longrightarrow> ivl_ctx_sg_2 (Inl (v, ctx)) = locals (sigma_2 (Inl (v, ctx))) \<squnion> globs (sigma_2 (Inr Global2))"
  by (simp add: ivl_ctx_sg_2_def)

lemma ivl_ctx_sg_2_uncovered_empty:
  "(v, ctx) \<notin> fst twice_2_sol \<Longrightarrow> \<lbrakk>ivl_ctx_sg_2 (Inl (v, ctx))\<rbrakk> = {}"
  by (simp add: ivl_ctx_sg_2_def gamma_state_bot)

lemma entry_locals_ge_s0d_2:
  assumes cov: "(cfg_entry twice_cfg, []) \<in> fst twice_2_sol"
  shows "fun_of_st cinit_ivl_st \<le> locals (sigma_2 (Inl (cfg_entry twice_cfg, [])))"
proof -
  have "fun_of_st cinit_ivl_st
          \<le> locals (eq gen_2_abs (cfg_entry twice_cfg, []) sigma_2)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_2], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma_2 (Inl (cfg_entry twice_cfg, [])))"
    using pp_eq_bound_2[OF cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

interpretation twice_2_dg: dg_ctx_activation Sabs is_global twice_cfg Global2 "cs_route 2"
    "routed_cmb Sabs Global2" "routed_extra twice_cfg Sabs Seed2 Global2"
    "fun_of_st (bot::ivl st)" "fun_of_st cinit_ivl_st" "fun_of_st (restrict_global_st cinit_ivl_st)"
    sigma_2 "fst twice_2_sol" "(cfg_exit twice_cfg, [])" ivl_ctx_sg_2
proof unfold_locales
  show "finite (intra twice_cfg)" by (rule twice_finE)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
             (routed_cmb Sabs Global2) (routed_extra twice_cfg Sabs Seed2 Global2) twice_cfg Sabs
             (fun_of_st (bot::ivl st)) (fun_of_st cinit_ivl_st)
             (fun_of_st (restrict_global_st cinit_ivl_st)))
          (cfg_exit twice_cfg, []) sigma_2 (fst twice_2_sol)"
    by (rule twice_2_pp_abs)
next
  fix v ctx
  assume "(v, ctx) \<in> fst twice_2_sol"
  thus "ivl_ctx_sg_2 (Inl (v, ctx)) = locals (sigma_2 (Inl (v, ctx))) \<squnion> globs (sigma_2 (Inr Global2))"
    by (rule ivl_ctx_sg_2_covered)
next
  fix v ctx
  assume "(v, ctx) \<notin> fst twice_2_sol"
  thus "\<lbrakk>ivl_ctx_sg_2 (Inl (v, ctx))\<rbrakk> = {}"
    by (rule ivl_ctx_sg_2_uncovered_empty)
next
  fix u a v ctx
  assume "(u, ctx) \<in> fst twice_2_sol" "(u, a, v) \<in> intra twice_cfg"
  thus "(v, ctx) \<in> fst twice_2_sol" by (rule twice_fwd_closed_2)
qed

text \<open>\<open>cs_route 2\<close> and \<open>cs_enterc 2\<close> are the identical closed term \<open>take 2 (u # ctx)\<close>, so
  \<open>route_enterc_agree\<close> is \<open>Call_String_Context.thy\<close>'s \<open>cs_route_enterc_agree\<close> directly ---
  exactly the claim \<^file>\<open>../../../docs/CALLSTRING_CONTEXT_DESIGN.md\<close> made about \<open>k > 1\<close>
  needing no case split on the abstract value, unlike \<open>route_cs\<close>'s already-trivial \<open>k = 1\<close>
  case.\<close>

interpretation twice_2_routed: routed_context Sabs is_global twice_cfg Global2 "cs_route 2"
    "fun_of_st (bot::ivl st)" "fun_of_st cinit_ivl_st" "fun_of_st (restrict_global_st cinit_ivl_st)"
    sigma_2 "fst twice_2_sol" "(cfg_exit twice_cfg, [])" ivl_ctx_sg_2
    Seed2 "cs_enterc 2"
proof (unfold_locales, goal_cases FinC SeedKey RouteAgree CallFwd CombFwd EnterAgree)
  case FinC
  show ?case by (rule twice_finC)
next
  case (SeedKey p ctx)
  show ?case by simp
next
  case (RouteAgree u ctx dst pars args p cont s)
  show ?case by (rule cs_route_enterc_agree)
next
  case (CallFwd u ctx dst pars args p cont)
  note covU = CallFwd(1) and ce = CallFwd(2)
  from ce consider
      (c1) "u = Statement 2" "p = ''twice''"
    | (c2) "u = Statement 3" "p = ''twice''"
    unfolding twice_calls by auto
  thus ?case
  proof cases
    case c1
    have ctx0: "ctx = []" using covU c1 enter_callers_only_root_2 by fastforce
    thus ?thesis using c1 callee_covered_call1_2 by (simp add: cs_route_def ctx_call1_2_def)
  next
    case c2
    have ctx0: "ctx = []" using covU c2 enter_callers_only_root_2 by fastforce
    thus ?thesis using c2 callee_covered_call2_2 by (simp add: cs_route_def ctx_call2_2_def)
  qed
next
  case (CombFwd cl c1 dst pars args p cont)
  note covCl = CombFwd(1) and ce = CombFwd(2)
  show ?case
    using ce covCl enter_callers_only_root_2 covered_ret5_2 covered_ret7_2
    unfolding twice_calls by auto
next
  case (EnterAgree cl s es dst pars args p cont)
  note ces = EnterAgree(1) and ce = EnterAgree(2)
  show ?case
    using ces ce unfolding call_enter_store_def by (auto simp: twice_calls)
qed

lemma ivl_ctx_sg_2_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls twice_cfg"
    and "s \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (u, ctx))\<rbrakk>"
  shows "call_enter is_global (CallEdge dst xs es) s
           \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (FunctionEntry p,
                 cs_enterc 2 u ctx (call_enter is_global (CallEdge dst xs es) s)))\<rbrakk>"
  by (rule twice_2_routed.routed_context_call[OF assms])

lemma ivl_ctx_sg_2_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls twice_cfg"
    and "s \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (cl, c1))\<rbrakk>"
    and "t \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (FunctionResult p, cs_enterc 2 cl c1 es))\<rbrakk>"
    and "call_enter_store is_global twice_cfg cl s es"
  shows "combine_collect is_global dst s t \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (v, c1))\<rbrakk>"
  by (rule twice_2_routed.routed_context_comb[OF assms])

section \<open>The headline theorem: 2-call-string activation collecting soundness\<close>

lemma cinit_le_cinit_ivl_st_2: "cinit_stores is_global \<subseteq> \<lbrakk>fun_of_st cinit_ivl_st\<rbrakk>"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_st_cinit_ivl_st)

theorem twice_2_activation_collect_sound:
  "activation_collect is_global (cs_enterc 2) [] twice_cfg (cinit_stores is_global) v ctx
     \<subseteq> \<lbrakk>ivl_ctx_sg_2 (Inl (v, ctx))\<rbrakk>"
proof (rule activation_collect_sound[where sg = ivl_ctx_sg_2 and enterc = "cs_enterc 2"
        and seedc = "[]" and S = "cinit_stores is_global" and g = twice_cfg and gs = is_global])
  \<comment> \<open>ENTRY_G\<close>
  fix s assume "s \<in> cinit_stores is_global"
  hence "s \<in> \<lbrakk>fun_of_st cinit_ivl_st\<rbrakk>" using cinit_le_cinit_ivl_st_2 by blast
  also have "\<lbrakk>fun_of_st cinit_ivl_st\<rbrakk>
        \<subseteq> \<lbrakk>locals (sigma_2 (Inl (cfg_entry twice_cfg, [])))\<rbrakk>"
    by (rule gamma_state_mono[OF entry_locals_ge_s0d_2[OF entry_covered_2]])
  also have "\<dots> \<subseteq> \<lbrakk>ivl_ctx_sg_2 (Inl (cfg_entry twice_cfg, []))\<rbrakk>"
    unfolding ivl_ctx_sg_2_covered[OF entry_covered_2] by (rule gamma_state_sup_ub1)
  finally show "s \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (cfg_entry twice_cfg, []))\<rbrakk>" .
next
  \<comment> \<open>EDGE --- discharged generically off the post-solution by \<open>dg_ctx_activation\<close>.\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> intra twice_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (v, c))\<rbrakk>"
    by (rule twice_2_dg.dg_ctx_act_edge)
next
  \<comment> \<open>CALL --- enter routed to the truncated call string.\<close>
  show "\<And>u dst pars args p cont c s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls twice_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (u, c))\<rbrakk>
        \<Longrightarrow> call_enter is_global (CallEdge dst pars args) s
             \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (FunctionEntry p,
                    cs_enterc 2 u c (call_enter is_global (CallEdge dst pars args) s)))\<rbrakk>"
    by (rule ivl_ctx_sg_2_seed)
next
  \<comment> \<open>COMB --- return combine at the caller's own truncated context.\<close>
  show "\<And>cl dst pars args p cont c1 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls twice_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (cl, c1))\<rbrakk>
        \<Longrightarrow> t \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (FunctionResult p, cs_enterc 2 cl c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store is_global twice_cfg cl s es
        \<Longrightarrow> combine_collect is_global dst s t \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (cont, c1))\<rbrakk>"
    by (rule ivl_ctx_sg_2_comb)
qed

end

