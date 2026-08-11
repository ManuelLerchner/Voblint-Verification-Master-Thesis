theory Example_Interval_DG_CallString_K2
  imports
    Example_Interval_DG_CallString_K1
begin

section \<open>A computed 2-call-string context, routed by truncated call history\<close>

text \<open>
  The \<open>k = 2\<close> sibling of \<open>Example_Interval_DG_CallString_K1.thy\<close>, same \<open>nest\<close> program:
  \<open>g\<close>'s single call site is reached from two different \<open>f\<close> activations. At \<open>k = 1\<close> both
  collapse into one merged context; at \<open>k = 2\<close> the call string also records which \<open>f\<close> call
  led there, so the two stay separate.
\<close>

subsection \<open>A call-string-keyed global-key type\<close>

datatype gk_2 = Global2 | Seed2 (seed2_pp: pp) (seed2_cs: "cfg_node list")

subsection \<open>The routed equation system and its computed solution\<close>

definition nest_2_eqs :: "(pp \<times> cfg_node list, gk_2, (ivl exec_dg_st, ivl exec_dg_st) dg_state) eqsT" where
  "nest_2_eqs =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
       (routed_cmb Spoly Global2) (routed_extra nest_cfg Spoly Seed2 Global2)
       nest_cfg Spoly bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st)"

definition nest_2_sol ::
  "(pp \<times> cfg_node list) set \<times> (pp \<times> cfg_node list + gk_2 \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)" where
  "nest_2_sol = TD_side_warrowing_apinis_Interp_solve nest_2_eqs
                    (cfg_exit nest_cfg, [])"

lemma nest_2_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c nest_2_eqs (cfg_exit nest_cfg, [])
     \<noteq> None"
  by eval

subsection \<open>Coverage\<close>

lemma entry_covered_2: "(cfg_entry nest_cfg, []) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def nest_entry by eval

lemma nest_fwd_closed_all_2:
  "\<forall>(u, c)\<in>fst nest_2_sol. \<forall>(u', a, v)\<in>intra nest_cfg.
      u = u' \<longrightarrow> (v, c) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma nest_fwd_closed_2:
  assumes "(u, ctx) \<in> fst nest_2_sol" and "(u, a, v) \<in> intra nest_cfg"
  shows "(v, ctx) \<in> fst nest_2_sol"
  using nest_fwd_closed_all_2 assms by fastforce

text \<open>Unlike \<open>k = 1\<close>, \<open>g\<close>'s call site is now covered at two \<^emph>\<open>distinct\<close> two-element
  contexts, one per \<open>f\<close> activation that reaches it.\<close>

lemma enter_callers_only_root_main_2:
  "\<forall>(p, ctx)\<in>fst nest_2_sol.
     (p = Statement 5 \<or> p = Statement 6) \<longrightarrow> ctx = []"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma enter_callers_g_2:
  "\<forall>(p, ctx)\<in>fst nest_2_sol.
     p = Statement 2 \<longrightarrow> ctx = [Statement 5] \<or> ctx = [Statement 6]"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma callee_covered_f3_2: "(FunctionEntry (STR ''f''), [Statement 5]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval
lemma callee_covered_f10_2: "(FunctionEntry (STR ''f''), [Statement 6]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval
lemma callee_covered_g_f3_2: "(FunctionEntry (STR ''g''), [Statement 2, Statement 5]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval
lemma callee_covered_g_f10_2: "(FunctionEntry (STR ''g''), [Statement 2, Statement 6]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma covered_ret6_2: "(Statement 6, []) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval
lemma covered_ret7_2: "(Statement 7, []) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval
lemma covered_ret3_f3_2: "(Statement 3, [Statement 5]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval
lemma covered_ret3_f10_2: "(Statement 3, [Statement 6]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma callee_exit_f3_2: "(FunctionResult (STR ''f''), [Statement 5]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval
lemma callee_exit_f10_2: "(FunctionResult (STR ''f''), [Statement 6]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval
lemma callee_exit_g_f3_2: "(FunctionResult (STR ''g''), [Statement 2, Statement 5]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval
lemma callee_exit_g_f10_2: "(FunctionResult (STR ''g''), [Statement 2, Statement 6]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

section \<open>Abstract transport of the routed solution\<close>

lemma dg_tree_st_commute_frame_read_2:
  "dg_tree_st_commute_for nest_gs env
     (QueryG (Seed2 v ctx) (\<lambda>s. Answer (DG (globs s) bot)))
     (QueryG (Seed2 v ctx) (\<lambda>s. Answer (DG (globs s) bot)))"
  by (simp add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                dep_aux_def bot_fun_def)

lemma dg_tree_st_commute_routed_cmb_2:
  "dg_tree_st_commute_for nest_gs env (routed_cmb Spoly Global2 (cs_route 2) ctx ca cc ex)
                          (routed_cmb Sabs Global2 (cs_route 2) ctx ca cc ex)"
  unfolding routed_cmb_def Let_def
  by (cases ca)
     (simp_all add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                    cs_route_def dgs_combine_fst_commute_gen dgs_combine_snd_commute_gen
                    dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

lemma dg_tree_st_commute_routed_enter_pub_2:
  "dg_tree_st_commute_for nest_gs env
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
     (simp add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                cs_route_def dgs_enter_fst_commute_gen dgs_enter_snd_commute_gen
                dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

lemma hextra_commute_routed_2:
  "list_all2 (dg_tree_st_commute_for nest_gs env)
     (routed_extra nest_cfg Spoly Seed2 Global2 (cs_route 2) ctx w)
     (routed_extra nest_cfg Sabs Seed2 Global2 (cs_route 2) ctx w)"
  unfolding routed_extra_def Let_def
  by (auto simp: list_all2_appendI list_all2_map1 list_all2_map2 list_all2_refl split_beta
                 dg_tree_st_commute_frame_read_2 dg_tree_st_commute_routed_enter_pub_2
           split: cfg_node.split)

lemma nest_2_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk_2) TYPE((ivl exec_dg_st, ivl exec_dg_st) dg_state)
     nest_2_eqs (cfg_exit nest_cfg, [])"
  using nest_2_terminates
  unfolding TD_side_warrowing_apinis_Interp.term_equivalence
            TD_side_warrowing_apinis_Interp.solve_c_dom_def
  by simp

lemma nest_2_pp_st:
  "part_post_solution nest_2_eqs (cfg_exit nest_cfg, [])
     (snd nest_2_sol) (fst nest_2_sol)"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF nest_2_solve_dom, of "fst nest_2_sol" "snd nest_2_sol"]
  unfolding nest_2_sol_def by simp

theorem nest_2_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
        (routed_cmb Sabs Global2) (routed_extra nest_cfg Sabs Seed2 Global2) nest_cfg Sabs
        (fun_of_exec_dg_st_for nest_gs (bot::ivl exec_dg_st)) (fun_of_exec_dg_st_for nest_gs cinit_ivl_st) (fun_of_exec_dg_st_for nest_gs (restrict_global_resolved_q cinit_ivl_st)))
     (cfg_exit nest_cfg, []) (fun_of_dg_st_for nest_gs \<circ> snd nest_2_sol) (fst nest_2_sol)"
proof -
  have pp': "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
          (routed_cmb Spoly Global2) (routed_extra nest_cfg Spoly Seed2 Global2) nest_cfg Spoly
          bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st))
       (cfg_exit nest_cfg, []) (snd nest_2_sol) (fst nest_2_sol)"
    using nest_2_pp_st unfolding nest_2_eqs_def by simp
  have ivl_Hstep_2:
    "map_prod (fun_of_exec_dg_st_for nest_gs) (fun_of_exec_dg_st_for nest_gs) (dg_spec_step Spoly a d g') =
       dg_spec_step Sabs a (fun_of_exec_dg_st_for nest_gs d) (fun_of_exec_dg_st_for nest_gs g')" for a d g'
    unfolding Spoly_def by (rule ivl_Hstep)
  show ?thesis
    by (rule part_post_solution_seed_dg_st_to_abs_for
          [where gs = nest_gs and pred_sel = intra_predecessor_list and gkey = "\<lambda>_. Global2"
             and route_st = "cs_route 2" and route_abs = "cs_route 2"
             and cmb_st = "routed_cmb Spoly Global2" and cmb_abs = "routed_cmb Sabs Global2"
             and extra_st = "routed_extra nest_cfg Spoly Seed2 Global2"
             and extra_abs = "routed_extra nest_cfg Sabs Seed2 Global2"
             and g = nest_cfg and S_st = Spoly and S_abs = Sabs,              OF ivl_Hstep_2 cs_route_indep_of_data dg_tree_st_commute_routed_cmb_2
              hextra_commute_routed_2 pp'])
qed

section \<open>Activation-indexed collecting soundness for the 2-call-string-routed solution\<close>

abbreviation sigma_2 :: "pp \<times> cfg_node list + gk_2 \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state" where
  "sigma_2 \<equiv> fun_of_dg_st_for nest_gs \<circ> snd nest_2_sol"

abbreviation gen_2_abs :: "(pp \<times> cfg_node list, gk_2, (ivl abs_state, ivl abs_state) dg_state) eqsT" where
  "gen_2_abs \<equiv> side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
       (routed_cmb Sabs Global2) (routed_extra nest_cfg Sabs Seed2 Global2) nest_cfg Sabs
       (fun_of_exec_dg_st_for nest_gs (bot::ivl exec_dg_st)) (fun_of_exec_dg_st_for nest_gs cinit_ivl_st) (fun_of_exec_dg_st_for nest_gs (restrict_global_resolved_q cinit_ivl_st))"

lemma pp_eq_bound_2:
  "(v, ctx) \<in> fst nest_2_sol
     \<Longrightarrow> eq gen_2_abs (v, ctx) sigma_2 \<le> sigma_2 (Inl (v, ctx))"
  using nest_2_pp_abs by simp

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
          (if (v, ctx) \<in> fst nest_2_sol
           then combine_env\<^sup># nest_gs (locals (sigma_2 (Inl (v, ctx)))) (globs (sigma_2 (Inr Global2)))
           else bot)
      | Inr _ \<Rightarrow> bot)"

lemma ivl_ctx_sg_2_covered:
  "(v, ctx) \<in> fst nest_2_sol
   \<Longrightarrow> ivl_ctx_sg_2 (Inl (v, ctx))
       = combine_env\<^sup># nest_gs (locals (sigma_2 (Inl (v, ctx)))) (globs (sigma_2 (Inr Global2)))"
  by (simp add: ivl_ctx_sg_2_def)

lemma ivl_ctx_sg_2_uncovered_empty:
  "(v, ctx) \<notin> fst nest_2_sol \<Longrightarrow> \<lbrakk>ivl_ctx_sg_2 (Inl (v, ctx))\<rbrakk> = {}"
  by (simp add: ivl_ctx_sg_2_def gamma_state_bot)

lemma entry_locals_ge_s0d_2:
  assumes cov: "(cfg_entry nest_cfg, []) \<in> fst nest_2_sol"
  shows "fun_of_exec_dg_st_for nest_gs cinit_ivl_st \<le> locals (sigma_2 (Inl (cfg_entry nest_cfg, [])))"
proof -
  have "fun_of_exec_dg_st_for nest_gs cinit_ivl_st
          \<le> locals (eq gen_2_abs (cfg_entry nest_cfg, []) sigma_2)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_2], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma_2 (Inl (cfg_entry nest_cfg, [])))"
    using pp_eq_bound_2[OF cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

interpretation nest_2_dg: dg_ctx_activation Sabs nest_gs nest_cfg Global2 "cs_route 2"
    "routed_cmb Sabs Global2" "routed_extra nest_cfg Sabs Seed2 Global2"
    "fun_of_exec_dg_st_for nest_gs (bot::ivl exec_dg_st)" "fun_of_exec_dg_st_for nest_gs cinit_ivl_st" "fun_of_exec_dg_st_for nest_gs (restrict_global_resolved_q cinit_ivl_st)"
    sigma_2 "fst nest_2_sol" "(cfg_exit nest_cfg, [])" ivl_ctx_sg_2
proof unfold_locales
  show "finite (intra nest_cfg)" by (rule nest_finE)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
             (routed_cmb Sabs Global2) (routed_extra nest_cfg Sabs Seed2 Global2) nest_cfg Sabs
             (fun_of_exec_dg_st_for nest_gs (bot::ivl exec_dg_st)) (fun_of_exec_dg_st_for nest_gs cinit_ivl_st)
             (fun_of_exec_dg_st_for nest_gs (restrict_global_resolved_q cinit_ivl_st)))
          (cfg_exit nest_cfg, []) sigma_2 (fst nest_2_sol)"
    by (rule nest_2_pp_abs)
next
  fix v ctx
  assume "(v, ctx) \<in> fst nest_2_sol"
  thus "ivl_ctx_sg_2 (Inl (v, ctx))
          = combine_env\<^sup># nest_gs (locals (sigma_2 (Inl (v, ctx)))) (globs (sigma_2 (Inr Global2)))"
    by (rule ivl_ctx_sg_2_covered)
next
  fix v ctx
  assume "(v, ctx) \<notin> fst nest_2_sol"
  thus "\<lbrakk>ivl_ctx_sg_2 (Inl (v, ctx))\<rbrakk> = {}"
    by (rule ivl_ctx_sg_2_uncovered_empty)
next
  fix u a v ctx
  assume "(u, ctx) \<in> fst nest_2_sol" "(u, a, v) \<in> intra nest_cfg"
  thus "(v, ctx) \<in> fst nest_2_sol" by (rule nest_fwd_closed_2)
qed

text \<open>Unlike \<open>k = 1\<close>, \<open>CallFwd\<close>'s \<open>Statement 2\<close> case now genuinely splits: \<open>g\<close>'s call site
  is covered at two distinct one-element contexts, and \<open>take 2\<close> keeps them apart after
  routing, so each needs its own coverage witness.\<close>

interpretation nest_2_routed: routed_context Sabs nest_gs nest_cfg Global2 "cs_route 2"
    "fun_of_exec_dg_st_for nest_gs (bot::ivl exec_dg_st)" "fun_of_exec_dg_st_for nest_gs cinit_ivl_st" "fun_of_exec_dg_st_for nest_gs (restrict_global_resolved_q cinit_ivl_st)"
    sigma_2 "fst nest_2_sol" "(cfg_exit nest_cfg, [])" ivl_ctx_sg_2
    Seed2 "cs_enterc 2"
proof (unfold_locales, goal_cases FinC SeedKey RouteAgree CallFwd CombFwd EnterAgree)
  case FinC
  show ?case by (rule nest_finC)
next
  case (SeedKey p ctx)
  show ?case by simp
next
  case (RouteAgree u ctx dst pars args p cont s)
  show ?case by (rule cs_route_enterc_agree)
next
  case (CallFwd u ctx dst pars args p cont)
  note covU = CallFwd(1) and ce = CallFwd(2)
  from ce nest_calls_shape have
    "(u = Statement 2 \<and> p = (STR ''g'') \<and> cont = Statement 3) \<or>
     (u = Statement 5 \<and> p = (STR ''f'') \<and> cont = Statement 6) \<or>
     (u = Statement 6 \<and> p = (STR ''f'') \<and> cont = Statement 7)"
    by fastforce
  then consider
      (c1) "u = Statement 2" "p = (STR ''g'')"
    | (c2) "u = Statement 5" "p = (STR ''f'')"
    | (c3) "u = Statement 6" "p = (STR ''f'')"
    by blast
  thus ?case
  proof cases
    case c1
    from covU c1 enter_callers_g_2 have "ctx = [Statement 5] \<or> ctx = [Statement 6]" by fastforce
    thus ?thesis
    proof
      assume "ctx = [Statement 5]"
      thus ?thesis using c1 callee_covered_g_f3_2 by (simp add: cs_route_def)
    next
      assume "ctx = [Statement 6]"
      thus ?thesis using c1 callee_covered_g_f10_2 by (simp add: cs_route_def)
    qed
  next
    case c2
    have ctx0: "ctx = []" using covU c2 enter_callers_only_root_main_2 by fastforce
    thus ?thesis using c2 callee_covered_f3_2 by (simp add: cs_route_def)
  next
    case c3
    have ctx0: "ctx = []" using covU c3 enter_callers_only_root_main_2 by fastforce
    thus ?thesis using c3 callee_covered_f10_2 by (simp add: cs_route_def)
  qed
next
  case (CombFwd cl c1 dst pars args p cont)
  note covCl = CombFwd(1) and ce = CombFwd(2)
  show ?case
    using ce covCl enter_callers_only_root_main_2 enter_callers_g_2
          covered_ret3_f3_2 covered_ret3_f10_2 covered_ret6_2 covered_ret7_2
          nest_calls_shape
    by fastforce
next
  case (EnterAgree cl s es dst pars args p cont)
  note ces = EnterAgree(1) and ce = EnterAgree(2)
  show ?case
    using ces ce nest_calls_unique_site unfolding call_enter_store_def by fastforce
qed

lemma ivl_ctx_sg_2_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls nest_cfg"
    and "s \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (u, ctx))\<rbrakk>"
  shows "call_enter nest_gs (CallEdge dst xs es) s
           \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (FunctionEntry p,
                 cs_enterc 2 u ctx (call_enter nest_gs (CallEdge dst xs es) s)))\<rbrakk>"
  by (rule nest_2_routed.routed_context_call[OF assms])

lemma ivl_ctx_sg_2_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls nest_cfg"
    and "s \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (cl, c1))\<rbrakk>"
    and "t \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (FunctionResult p, cs_enterc 2 cl c1 es))\<rbrakk>"
    and "call_enter_store nest_gs nest_cfg cl s es"
  shows "combine_collect nest_gs dst s t \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (v, c1))\<rbrakk>"
  by (rule nest_2_routed.routed_context_comb[OF assms])

section \<open>The headline theorem: 2-call-string activation collecting soundness\<close>

lemma cinit_le_cinit_ivl_st_2: "cinit_stores nest_gs \<subseteq> \<lbrakk>fun_of_exec_dg_st_for nest_gs cinit_ivl_st\<rbrakk>"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for)

theorem nest_2_activation_collect_sound:
  "activation_collect nest_gs (admiss_exact (cs_enterc 2)) [] nest_cfg (cinit_stores nest_gs) v ctx
     \<subseteq> \<lbrakk>ivl_ctx_sg_2 (Inl (v, ctx))\<rbrakk>"
proof (rule activation_collect_sound[where sg = ivl_ctx_sg_2 and admiss = "admiss_exact (cs_enterc 2)"
        and startcontext = "[]"
        and S = "cinit_stores nest_gs" and g = nest_cfg and gs = nest_gs])
  \<comment> \<open>ENTRY_G\<close>
  text \<open>Both the local seed \<open>s0d\<close> and the global seed \<open>s0g\<close> are \<open>cinit_ivl_st\<close>'s own
    projections, so routing them back together through \<open>combine_env\<^sup>#\<close> exactly recovers
    \<open>s0d\<close>; the membership transports through \<open>gamma_unit_mono\<close> componentwise, needing
    the caller's local bound (\<open>entry_locals_ge_s0d_2\<close>) and the entry's global-seed
    bound (\<open>nest_2_dg.pp_entry_s0g_bound\<close>) separately instead of one joined bound.\<close>
  fix s assume "s \<in> cinit_stores nest_gs"
  hence "s \<in> \<lbrakk>fun_of_exec_dg_st_for nest_gs cinit_ivl_st\<rbrakk>" using cinit_le_cinit_ivl_st_2 by blast
  also have "\<lbrakk>fun_of_exec_dg_st_for nest_gs cinit_ivl_st\<rbrakk>
        = gamma_unit nest_gs (fun_of_exec_dg_st_for nest_gs cinit_ivl_st)
            (fun_of_exec_dg_st_for nest_gs (restrict_global_resolved_q cinit_ivl_st))"
    unfolding gamma_unit_def fun_of_exec_dg_st_for_def
    by (rule arg_cong[where f = gamma_state], rule ext)
       (simp add: combine_env_abs_def restrict_global_for_def)
  also have "\<dots> \<subseteq> gamma_unit nest_gs (locals (sigma_2 (Inl (cfg_entry nest_cfg, []))))
                   (globs (sigma_2 (Inr Global2)))"
    by (rule gamma_unit_mono[OF entry_locals_ge_s0d_2[OF entry_covered_2]
          nest_2_dg.pp_entry_s0g_bound[OF entry_covered_2]])
  also have "\<dots> = \<lbrakk>ivl_ctx_sg_2 (Inl (cfg_entry nest_cfg, []))\<rbrakk>"
    unfolding ivl_ctx_sg_2_covered[OF entry_covered_2] gamma_unit_def by (rule refl)
  finally show "s \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (cfg_entry nest_cfg, []))\<rbrakk>" .
next
  \<comment> \<open>EDGE --- discharged generically off the post-solution by \<open>dg_ctx_activation\<close>.\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> intra nest_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (u, c))\<rbrakk> \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (v, c))\<rbrakk>"
    by (rule nest_2_dg.dg_ctx_act_edge)
next
  \<comment> \<open>ADMISS_TOTAL --- \<open>admiss_exact\<close> is total since \<open>cs_enterc 2\<close> is a function.\<close>
  show "\<And>u c s. \<exists>c'. admiss_exact (cs_enterc 2) u c s c'"
    by (simp add: admiss_exact_def)
next
  \<comment> \<open>CALL --- enter routed to the truncated call string.\<close>
  fix u dst pars args p cont c s c'
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls nest_cfg"
    and sm: "s \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (u, c))\<rbrakk>"
    and adm: "admiss_exact (cs_enterc 2) u c (call_enter nest_gs (CallEdge dst pars args) s) c'"
  show "call_enter nest_gs (CallEdge dst pars args) s
          \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (FunctionEntry p, c'))\<rbrakk>"
    using adm ivl_ctx_sg_2_seed[OF ce sm] by (simp add: admiss_exact_def)
next
  \<comment> \<open>COMB --- return combine at the caller's own truncated context.\<close>
  fix cl dst pars args p cont c1 c2 s t es
  assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls nest_cfg"
    and sm: "s \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (cl, c1))\<rbrakk>"
    and adm: "admiss_exact (cs_enterc 2) cl c1 es c2"
    and tm: "t \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (FunctionResult p, c2))\<rbrakk>"
    and ces: "call_enter_store nest_gs nest_cfg cl s es"
  show "combine_collect nest_gs dst s t \<in> \<lbrakk>ivl_ctx_sg_2 (Inl (cont, c1))\<rbrakk>"
    using adm tm ivl_ctx_sg_2_comb[OF ce sm _ ces] by (simp add: admiss_exact_def)
qed

section \<open>Call-string-context-expanded analysis graph\<close>

definition nest_2_graph_config ::
  "(cfg_node list, gk_2, (ivl exec_dg_st, ivl exec_dg_st) dg_state, ivl exec_dg_st) analysis_graph_config" where
  "nest_2_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>u ctx action d. cs_route 2 u ctx d action),
      show_context = (\<lambda>ctx. ''['' @ join_source '', '' (map string_of_cfg_node ctx) @ '']''),
      locals_for_pp = (\<lambda>p.
        let sc = compiled_procedure_scope nest_gs nest_pi nest_procs (STR ''main'') nest_main
          nest_cfg p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope nest_gs nest_pi nest_procs (STR ''main'') nest_main
          nest_cfg p)),
      globals_to_show = [],
      show_local = (\<lambda>p ctx vars d. map (\<lambda>x.
        String.explode x @ ''='' @ string_of_ivl (nest_lookup_exec_dg_st d x)) vars),
      format_return = (\<lambda>p ctx ret d.
        if nest_lookup_exec_dg_st d ret = ivl_top then []
        else [''ret='' @ string_of_ivl (nest_lookup_exec_dg_st d ret)]),
      show_global = (\<lambda>k vars s. [''(none)'']),
      show_global_key = (\<lambda>k. case k of Global2 \<Rightarrow> ''Global'' | Seed2 p ctx \<Rightarrow> ''Seed''),
      is_shared_global = (\<lambda>k. case k of Global2 \<Rightarrow> True | Seed2 _ _ \<Rightarrow> False),
      show_internal_globals = False,
      owner_of = String.explode o compiled_owner_of nest_pi nest_procs (STR ''main'') nest_main,
      cluster_label = (\<lambda>owner ctx.
        if owner = ''main'' \<and> ctx = [] then ''main / root context''
        else owner @ '' / call string='' @ ''['' @ join_source '', '' (map string_of_cfg_node ctx) @ '']''),
      source_text = Some (pretty_string_of_program nest_pi nest_procs nest_main []),
      node_annotation = (\<lambda>_. None)
    \<rparr>"

definition nest_2_contexts_for_pp :: "pp \<Rightarrow> cfg_node list list" where
  "nest_2_contexts_for_pp p =
    (let owner = compiled_owner_of nest_pi nest_procs (STR ''main'') nest_main p
     in if owner = (STR ''main'') then [[]]
        else if owner = (STR ''f'') then [[Statement 5], [Statement 6]]
        else [[Statement 2, Statement 5], [Statement 2, Statement 6]])"

definition nest_2_local_graph_domain :: "(pp \<times> cfg_node list + gk_2) list" where
  "nest_2_local_graph_domain =
    contextual_graph_domain nest_cfg nest_2_contexts_for_pp"

definition nest_2_seed_keys :: "gk_2 list" where
  "nest_2_seed_keys =
     map (\<lambda>ctx. Seed2 (FunctionEntry (STR ''f'')) ctx) [[Statement 5], [Statement 6]]
     @ map (\<lambda>ctx. Seed2 (FunctionEntry (STR ''g'')) ctx) [[Statement 2, Statement 5], [Statement 2, Statement 6]]"

definition nest_2_graph_domain :: "(pp \<times> cfg_node list + gk_2) list" where
  "nest_2_graph_domain =
    nest_2_local_graph_domain @ map Inr nest_2_seed_keys"

definition nest_2_graph :: "(cfg_node list, gk_2) analysis_graph" where
  "nest_2_graph =
    build_analysis_graph nest_2_graph_config nest_cfg nest_2_graph_domain
      (snd nest_2_sol)"

definition nest_2_dot :: String.literal where
  "nest_2_dot =
    String.implode
      (analysis_graph_to_dot nest_2_graph_config nest_cfg (snd nest_2_sol)
        nest_2_graph)"

lemma nest_2_graph_wf: "analysis_graph_wf nest_2_graph" by eval

lemma nest_2_graph_domain_is_covered:
  "list_all (\<lambda>x. case x of Inl pc \<Rightarrow> pc \<in> fst nest_2_sol | Inr _ \<Rightarrow> True)
    nest_2_graph_domain" by eval

lemma nest_2_dot_nonempty: "String.explode nest_2_dot \<noteq> []" by eval

ML_val \<open>writeln (@{code nest_2_dot})\<close>

end

