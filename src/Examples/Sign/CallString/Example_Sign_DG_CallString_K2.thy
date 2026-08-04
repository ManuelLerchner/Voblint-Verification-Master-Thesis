theory Example_Sign_DG_CallString_K2
  imports
    Example_Sign_DG_CallString_K1
begin

section \<open>A computed 2-call-string context, routed by truncated call history\<close>

text \<open>
  The \<open>k = 2\<close> sibling of \<open>Example_Sign_DG_CallString_K1.thy\<close>, same \<open>sign_nest\<close> program:
  \<open>g\<close>'s single call site is reached from two different \<open>f\<close> activations. At \<open>k = 1\<close> both
  collapse into one merged context and \<open>g\<close>'s entry parameter joins to \<open>STop\<close>; at \<open>k = 2\<close> the
  call string also records which \<open>f\<close> call led there, so the two activations stay separate
  and \<open>g\<close>'s entry parameter is \<open>SPos\<close> in one context, \<open>SNeg\<close> in the other.
\<close>

subsection \<open>A call-string-keyed global-key type\<close>

datatype gk_2 = Global2 | Seed2 (seed2_pp: pp) (seed2_cs: "cfg_node list")

subsection \<open>The routed equation system and its computed solution\<close>

definition sign_nest_2_eqs :: "(pp \<times> cfg_node list, gk_2, (sign exec_dg_st, sign exec_dg_st) dg_state) eqsT" where
  "sign_nest_2_eqs =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
       (routed_cmb Spoly Global2) (routed_extra sign_nest_cfg Spoly Seed2 Global2)
       sign_nest_cfg Spoly bot cinit_sign_st (restrict_global_resolved_q cinit_sign_st)"

definition sign_nest_2_sol ::
  "(pp \<times> cfg_node list) set \<times> (pp \<times> cfg_node list + gk_2 \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "sign_nest_2_sol = TD_side_always_join_Interp_solve sign_nest_2_eqs (cfg_exit sign_nest_cfg, [])"

lemma sign_nest_2_terminates:
  "TD_side_always_join_Interp_solve_c sign_nest_2_eqs (cfg_exit sign_nest_cfg, []) \<noteq> None"
  by eval

subsection \<open>Coverage\<close>

lemma entry_covered_2: "(cfg_entry sign_nest_cfg, []) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def sign_nest_entry by eval

lemma sign_nest_fwd_closed_all_2:
  "\<forall>(u, c)\<in>fst sign_nest_2_sol. \<forall>(u', a, v)\<in>intra sign_nest_cfg.
      u = u' \<longrightarrow> (v, c) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval

lemma sign_nest_fwd_closed_2:
  assumes "(u, ctx) \<in> fst sign_nest_2_sol" and "(u, a, v) \<in> intra sign_nest_cfg"
  shows "(v, ctx) \<in> fst sign_nest_2_sol"
  using sign_nest_fwd_closed_all_2 assms by fastforce

text \<open>Unlike \<open>k = 1\<close>, \<open>g\<close>'s call site is now covered at two \<^emph>\<open>distinct\<close> two-element
  contexts, one per \<open>f\<close> activation that reaches it.\<close>

lemma enter_callers_only_root_main_2:
  "\<forall>(p, ctx)\<in>fst sign_nest_2_sol.
     (p = Statement 5 \<or> p = Statement 6) \<longrightarrow> ctx = []"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval

lemma enter_callers_g_2:
  "\<forall>(p, ctx)\<in>fst sign_nest_2_sol.
     p = Statement 2 \<longrightarrow> ctx = [Statement 5] \<or> ctx = [Statement 6]"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval

lemma callee_covered_fpos_2: "(FunctionEntry ''f'', [Statement 5]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval
lemma callee_covered_fneg_2: "(FunctionEntry ''f'', [Statement 6]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval
lemma callee_covered_g_fpos_2: "(FunctionEntry ''g'', [Statement 2, Statement 5]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval
lemma callee_covered_g_fneg_2: "(FunctionEntry ''g'', [Statement 2, Statement 6]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval

lemma covered_ret6_2: "(Statement 6, []) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval
lemma covered_ret7_2: "(Statement 7, []) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval
lemma covered_ret3_fpos_2: "(Statement 3, [Statement 5]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval
lemma covered_ret3_fneg_2: "(Statement 3, [Statement 6]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval

lemma callee_exit_fpos_2: "(FunctionResult ''f'', [Statement 5]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval
lemma callee_exit_fneg_2: "(FunctionResult ''f'', [Statement 6]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval
lemma callee_exit_g_fpos_2: "(FunctionResult ''g'', [Statement 2, Statement 5]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval
lemma callee_exit_g_fneg_2: "(FunctionResult ''g'', [Statement 2, Statement 6]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval

section \<open>Abstract transport of the routed solution\<close>

text \<open>The combine/enter commute lemmas are the same generic \<open>Spoly\<close>/\<open>Sabs\<close> facts proved
  once in \<open>Example_Sign_DG_CallString_K1.thy\<close> (\<open>dgs_combine_snd_commute_gen\<close> etc.);
  only the tree-shaped wrappers below are re-derived for the \<open>Global2\<close>/\<open>Seed2\<close> key type.\<close>

lemma dg_tree_st_commute_frame_read_2:
  "dg_tree_st_commute_for sign_nest_gs env
     (QueryG (Seed2 v ctx) (\<lambda>s. Answer (DG (globs s) bot)))
     (QueryG (Seed2 v ctx) (\<lambda>s. Answer (DG (globs s) bot)))"
  by (simp add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                dep_aux_def bot_fun_def)

lemma dg_tree_st_commute_routed_cmb_2:
  "dg_tree_st_commute_for sign_nest_gs env (routed_cmb Spoly Global2 (cs_route 2) ctx ca cc ex)
                          (routed_cmb Sabs Global2 (cs_route 2) ctx ca cc ex)"
  unfolding routed_cmb_def Let_def
  by (cases ca)
     (simp_all add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                    cs_route_def dgs_combine_fst_commute_gen dgs_combine_snd_commute_gen
                    dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

lemma dg_tree_st_commute_routed_enter_pub_2:
  "dg_tree_st_commute_for sign_nest_gs env
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
  "list_all2 (dg_tree_st_commute_for sign_nest_gs env)
     (routed_extra sign_nest_cfg Spoly Seed2 Global2 (cs_route 2) ctx w)
     (routed_extra sign_nest_cfg Sabs Seed2 Global2 (cs_route 2) ctx w)"
  unfolding routed_extra_def Let_def
  by (auto simp: list_all2_appendI list_all2_map1 list_all2_map2 list_all2_refl split_beta
                 dg_tree_st_commute_frame_read_2 dg_tree_st_commute_routed_enter_pub_2
           split: cfg_node.split)

lemma sign_nest_2_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(gk_2) TYPE((sign exec_dg_st, sign exec_dg_st) dg_state)
     sign_nest_2_eqs (cfg_exit sign_nest_cfg, [])"
  using sign_nest_2_terminates
  unfolding TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  by simp

lemma sign_nest_2_pp_st:
  "part_post_solution sign_nest_2_eqs (cfg_exit sign_nest_cfg, [])
     (snd sign_nest_2_sol) (fst sign_nest_2_sol)"
  using TD_side_always_join_Interp.partial_post_solution
          [OF sign_nest_2_solve_dom, of "fst sign_nest_2_sol" "snd sign_nest_2_sol"]
  unfolding sign_nest_2_sol_def by simp

theorem sign_nest_2_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
        (routed_cmb Sabs Global2) (routed_extra sign_nest_cfg Sabs Seed2 Global2) sign_nest_cfg Sabs
        (fun_of_exec_dg_st_for sign_nest_gs (bot::sign exec_dg_st)) (fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st) (fun_of_exec_dg_st_for sign_nest_gs (restrict_global_resolved_q cinit_sign_st)))
     (cfg_exit sign_nest_cfg, []) (fun_of_dg_st_for sign_nest_gs \<circ> snd sign_nest_2_sol) (fst sign_nest_2_sol)"
proof -
  have pp': "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
          (routed_cmb Spoly Global2) (routed_extra sign_nest_cfg Spoly Seed2 Global2) sign_nest_cfg Spoly
          bot cinit_sign_st (restrict_global_resolved_q cinit_sign_st))
       (cfg_exit sign_nest_cfg, []) (snd sign_nest_2_sol) (fst sign_nest_2_sol)"
    using sign_nest_2_pp_st unfolding sign_nest_2_eqs_def by simp
  have sign_Hstep_2:
    "map_prod (fun_of_exec_dg_st_for sign_nest_gs) (fun_of_exec_dg_st_for sign_nest_gs) (dg_spec_step Spoly a d g') =
       dg_spec_step Sabs a (fun_of_exec_dg_st_for sign_nest_gs d) (fun_of_exec_dg_st_for sign_nest_gs g')" for a d g'
    unfolding Spoly_def by (rule sign_Hstep)
  show ?thesis
    by (rule part_post_solution_seed_dg_st_to_abs_for
          [where gs = sign_nest_gs and pred_sel = intra_predecessor_list and gkey = "\<lambda>_. Global2"
             and route_st = "cs_route 2" and route_abs = "cs_route 2"
             and cmb_st = "routed_cmb Spoly Global2" and cmb_abs = "routed_cmb Sabs Global2"
             and extra_st = "routed_extra sign_nest_cfg Spoly Seed2 Global2"
             and extra_abs = "routed_extra sign_nest_cfg Sabs Seed2 Global2"
             and g = sign_nest_cfg and S_st = Spoly and S_abs = Sabs,
           OF sign_Hstep_2 cs_route_indep_of_data dg_tree_st_commute_routed_cmb_2
              hextra_commute_routed_2 pp'])
qed

section \<open>Activation-indexed collecting soundness for the 2-call-string-routed solution\<close>

abbreviation sigma_2 :: "pp \<times> cfg_node list + gk_2 \<Rightarrow> (sign abs_state, sign abs_state) dg_state" where
  "sigma_2 \<equiv> fun_of_dg_st_for sign_nest_gs \<circ> snd sign_nest_2_sol"

abbreviation gen_2_abs :: "(pp \<times> cfg_node list, gk_2, (sign abs_state, sign abs_state) dg_state) eqsT" where
  "gen_2_abs \<equiv> side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
       (routed_cmb Sabs Global2) (routed_extra sign_nest_cfg Sabs Seed2 Global2) sign_nest_cfg Sabs
       (fun_of_exec_dg_st_for sign_nest_gs (bot::sign exec_dg_st)) (fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st) (fun_of_exec_dg_st_for sign_nest_gs (restrict_global_resolved_q cinit_sign_st))"

lemma pp_eq_bound_2:
  "(v, ctx) \<in> fst sign_nest_2_sol
     \<Longrightarrow> eq gen_2_abs (v, ctx) sigma_2 \<le> sigma_2 (Inl (v, ctx))"
  using sign_nest_2_pp_abs by simp

definition sign_ctx_sg_2 :: "pp \<times> cfg_node list + gk_2 \<Rightarrow> sign abs_state" where
  "sign_ctx_sg_2 k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst sign_nest_2_sol
           then locals (sigma_2 (Inl (v, ctx))) \<squnion> globs (sigma_2 (Inr Global2))
           else bot)
      | Inr _ \<Rightarrow> bot)"

lemma sign_ctx_sg_2_covered:
  "(v, ctx) \<in> fst sign_nest_2_sol
   \<Longrightarrow> sign_ctx_sg_2 (Inl (v, ctx)) = locals (sigma_2 (Inl (v, ctx))) \<squnion> globs (sigma_2 (Inr Global2))"
  by (simp add: sign_ctx_sg_2_def)

lemma sign_ctx_sg_2_uncovered_empty:
  "(v, ctx) \<notin> fst sign_nest_2_sol \<Longrightarrow> \<lbrakk>sign_ctx_sg_2 (Inl (v, ctx))\<rbrakk> = {}"
  by (simp add: sign_ctx_sg_2_def gamma_state_bot)

lemma entry_locals_ge_s0d_2:
  assumes cov: "(cfg_entry sign_nest_cfg, []) \<in> fst sign_nest_2_sol"
  shows "fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st \<le> locals (sigma_2 (Inl (cfg_entry sign_nest_cfg, [])))"
proof -
  have "fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st
          \<le> locals (eq gen_2_abs (cfg_entry sign_nest_cfg, []) sigma_2)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_1], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma_2 (Inl (cfg_entry sign_nest_cfg, [])))"
    using pp_eq_bound_2[OF cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

interpretation sign_nest_2_dg: dg_ctx_activation Sabs sign_nest_gs sign_nest_cfg Global2 "cs_route 2"
    "routed_cmb Sabs Global2" "routed_extra sign_nest_cfg Sabs Seed2 Global2"
    "fun_of_exec_dg_st_for sign_nest_gs (bot::sign exec_dg_st)" "fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st" "fun_of_exec_dg_st_for sign_nest_gs (restrict_global_resolved_q cinit_sign_st)"
    sigma_2 "fst sign_nest_2_sol" "(cfg_exit sign_nest_cfg, [])" sign_ctx_sg_2
proof unfold_locales
  show "finite (intra sign_nest_cfg)" by (rule sign_nest_finE)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global2) (cs_route 2)
             (routed_cmb Sabs Global2) (routed_extra sign_nest_cfg Sabs Seed2 Global2) sign_nest_cfg Sabs
             (fun_of_exec_dg_st_for sign_nest_gs (bot::sign exec_dg_st)) (fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st)
             (fun_of_exec_dg_st_for sign_nest_gs (restrict_global_resolved_q cinit_sign_st)))
          (cfg_exit sign_nest_cfg, []) sigma_2 (fst sign_nest_2_sol)"
    by (rule sign_nest_2_pp_abs)
next
  fix v ctx
  assume "(v, ctx) \<in> fst sign_nest_2_sol"
  thus "sign_ctx_sg_2 (Inl (v, ctx)) = locals (sigma_2 (Inl (v, ctx))) \<squnion> globs (sigma_2 (Inr Global2))"
    by (rule sign_ctx_sg_2_covered)
next
  fix v ctx
  assume "(v, ctx) \<notin> fst sign_nest_2_sol"
  thus "\<lbrakk>sign_ctx_sg_2 (Inl (v, ctx))\<rbrakk> = {}"
    by (rule sign_ctx_sg_2_uncovered_empty)
next
  fix u a v ctx
  assume "(u, ctx) \<in> fst sign_nest_2_sol" "(u, a, v) \<in> intra sign_nest_cfg"
  thus "(v, ctx) \<in> fst sign_nest_2_sol" by (rule sign_nest_fwd_closed_2)
qed

text \<open>Unlike \<open>k = 1\<close>, \<open>CallFwd\<close>'s \<open>Statement 2\<close> case now genuinely splits: \<open>g\<close>'s call site
  is covered at two distinct two-element contexts, and \<open>take 2\<close> keeps them apart after
  routing, so each needs its own coverage witness.\<close>

interpretation sign_nest_2_routed: routed_context Sabs sign_nest_gs sign_nest_cfg Global2 "cs_route 2"
    "fun_of_exec_dg_st_for sign_nest_gs (bot::sign exec_dg_st)" "fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st" "fun_of_exec_dg_st_for sign_nest_gs (restrict_global_resolved_q cinit_sign_st)"
    sigma_2 "fst sign_nest_2_sol" "(cfg_exit sign_nest_cfg, [])" sign_ctx_sg_2
    Seed2 "cs_enterc 2"
proof (unfold_locales, goal_cases FinC SeedKey RouteAgree CallFwd CombFwd EnterAgree)
  case FinC
  show ?case by (rule sign_nest_finC)
next
  case (SeedKey p ctx)
  show ?case by simp
next
  case (RouteAgree u ctx dst pars args p cont s)
  show ?case by (rule cs_route_enterc_agree)
next
  case (CallFwd u ctx dst pars args p cont)
  note covU = CallFwd(1) and ce = CallFwd(2)
  from ce sign_nest_calls_shape have
    "(u = Statement 2 \<and> p = ''g'' \<and> cont = Statement 3) \<or>
     (u = Statement 5 \<and> p = ''f'' \<and> cont = Statement 6) \<or>
     (u = Statement 6 \<and> p = ''f'' \<and> cont = Statement 7)"
    by fastforce
  then consider
      (c1) "u = Statement 2" "p = ''g''"
    | (c2) "u = Statement 5" "p = ''f''"
    | (c3) "u = Statement 6" "p = ''f''"
    by blast
  thus ?case
  proof cases
    case c1
    from covU c1 enter_callers_g_2 have "ctx = [Statement 5] \<or> ctx = [Statement 6]" by fastforce
    thus ?thesis
    proof
      assume "ctx = [Statement 5]"
      thus ?thesis using c1 callee_covered_g_fpos_2 by (simp add: cs_route_def)
    next
      assume "ctx = [Statement 6]"
      thus ?thesis using c1 callee_covered_g_fneg_2 by (simp add: cs_route_def)
    qed
  next
    case c2
    have ctx0: "ctx = []" using covU c2 enter_callers_only_root_main_2 by fastforce
    thus ?thesis using c2 callee_covered_fpos_2 by (simp add: cs_route_def)
  next
    case c3
    have ctx0: "ctx = []" using covU c3 enter_callers_only_root_main_2 by fastforce
    thus ?thesis using c3 callee_covered_fneg_2 by (simp add: cs_route_def)
  qed
next
  case (CombFwd cl c1 dst pars args p cont)
  note covCl = CombFwd(1) and ce = CombFwd(2)
  show ?case
    using ce covCl enter_callers_only_root_main_2 enter_callers_g_2
          covered_ret3_fpos_2 covered_ret3_fneg_2 covered_ret6_2 covered_ret7_2
          sign_nest_calls_shape
    by fastforce
next
  case (EnterAgree cl s es dst pars args p cont)
  note ces = EnterAgree(1) and ce = EnterAgree(2)
  show ?case
    using ces ce sign_nest_calls_unique_site unfolding call_enter_store_def by fastforce
qed

lemma sign_ctx_sg_2_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls sign_nest_cfg"
    and "s \<in> \<lbrakk>sign_ctx_sg_2 (Inl (u, ctx))\<rbrakk>"
  shows "call_enter sign_nest_gs (CallEdge dst xs es) s
           \<in> \<lbrakk>sign_ctx_sg_2 (Inl (FunctionEntry p,
                 cs_enterc 2 u ctx (call_enter sign_nest_gs (CallEdge dst xs es) s)))\<rbrakk>"
  by (rule sign_nest_2_routed.routed_context_call[OF assms])

lemma sign_ctx_sg_2_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls sign_nest_cfg"
    and "s \<in> \<lbrakk>sign_ctx_sg_2 (Inl (cl, c1))\<rbrakk>"
    and "t \<in> \<lbrakk>sign_ctx_sg_2 (Inl (FunctionResult p, cs_enterc 2 cl c1 es))\<rbrakk>"
    and "call_enter_store sign_nest_gs sign_nest_cfg cl s es"
  shows "combine_collect sign_nest_gs dst s t \<in> \<lbrakk>sign_ctx_sg_2 (Inl (v, c1))\<rbrakk>"
  by (rule sign_nest_2_routed.routed_context_comb[OF assms])

section \<open>The headline theorem: 2-call-string activation collecting soundness\<close>

lemma cinit_le_cinit_sign_st_2: "cinit_stores sign_nest_gs \<subseteq> \<lbrakk>fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st\<rbrakk>"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def fun_of_st_cinit_sign_st_for)

theorem sign_nest_2_activation_collect_sound:
  "activation_collect sign_nest_gs (cs_enterc 2) [] sign_nest_cfg (cinit_stores sign_nest_gs) v ctx
     \<subseteq> \<lbrakk>sign_ctx_sg_2 (Inl (v, ctx))\<rbrakk>"
proof (rule activation_collect_sound[where sg = sign_ctx_sg_2 and enterc = "cs_enterc 2"
        and seedc = "[]" and S = "cinit_stores sign_nest_gs" and g = sign_nest_cfg and gs = sign_nest_gs])
  \<comment> \<open>ENTRY_G\<close>
  fix s assume "s \<in> cinit_stores sign_nest_gs"
  hence "s \<in> \<lbrakk>fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st\<rbrakk>" using cinit_le_cinit_sign_st_2 by blast
  also have "\<lbrakk>fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st\<rbrakk>
        \<subseteq> \<lbrakk>locals (sigma_2 (Inl (cfg_entry sign_nest_cfg, [])))\<rbrakk>"
    by (rule gamma_state_mono[OF entry_locals_ge_s0d_2[OF entry_covered_2]])
  also have "\<dots> \<subseteq> \<lbrakk>sign_ctx_sg_2 (Inl (cfg_entry sign_nest_cfg, []))\<rbrakk>"
    unfolding sign_ctx_sg_2_covered[OF entry_covered_2] by (rule gamma_state_sup_ub1)
  finally show "s \<in> \<lbrakk>sign_ctx_sg_2 (Inl (cfg_entry sign_nest_cfg, []))\<rbrakk>" .
next
  \<comment> \<open>EDGE --- discharged generically off the post-solution by \<open>dg_ctx_activation\<close>.\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> intra sign_nest_cfg
        \<Longrightarrow> s \<in> \<lbrakk>sign_ctx_sg_2 (Inl (u, c))\<rbrakk> \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> \<lbrakk>sign_ctx_sg_2 (Inl (v, c))\<rbrakk>"
    by (rule sign_nest_2_dg.dg_ctx_act_edge)
next
  \<comment> \<open>CALL --- enter routed to the truncated call string.\<close>
  show "\<And>u dst pars args p cont c s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls sign_nest_cfg
        \<Longrightarrow> s \<in> \<lbrakk>sign_ctx_sg_2 (Inl (u, c))\<rbrakk>
        \<Longrightarrow> call_enter sign_nest_gs (CallEdge dst pars args) s
             \<in> \<lbrakk>sign_ctx_sg_2 (Inl (FunctionEntry p,
                    cs_enterc 2 u c (call_enter sign_nest_gs (CallEdge dst pars args) s)))\<rbrakk>"
    by (rule sign_ctx_sg_2_seed)
next
  \<comment> \<open>COMB --- return combine at the caller's own truncated context.\<close>
  show "\<And>cl dst pars args p cont c1 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls sign_nest_cfg
        \<Longrightarrow> s \<in> \<lbrakk>sign_ctx_sg_2 (Inl (cl, c1))\<rbrakk>
        \<Longrightarrow> t \<in> \<lbrakk>sign_ctx_sg_2 (Inl (FunctionResult p, cs_enterc 2 cl c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store sign_nest_gs sign_nest_cfg cl s es
        \<Longrightarrow> combine_collect sign_nest_gs dst s t \<in> \<lbrakk>sign_ctx_sg_2 (Inl (cont, c1))\<rbrakk>"
    by (rule sign_ctx_sg_2_comb)
qed

section \<open>The precision comparison: k=2 keeps \<open>g\<close>'s two activations separated where k=1 merges them\<close>

text \<open>
  A concrete, executable precision statement for this program and this D/G analysis: the
  1-call-string context collapses \<open>g\<close>'s two activations to one context and their join at
  \<open>STop\<close> loses all sign information, while the 2-call-string context keeps them apart and each
  retains its own exact sign. This is not a general "call strings always improve precision"
  claim --- it is the concrete forcing witness the sign lattice's finiteness lets us compute
  and verify outright, in the style of the paper's context-sensitivity discussion (Tilscher/
  Grass/Seidl, "Verifying a Solver for Mixed Flow-Sensitive Analyses").
\<close>

lemma sign_k1_g_entry_top:
  "sign_nest_lookup_exec_dg_st (locals (snd sign_nest_1_sol (Inl (FunctionEntry ''g'', [Statement 2])))) ''p'' = STop"
  by eval

lemma sign_k2_g_entry_fpos:
  "sign_nest_lookup_exec_dg_st (locals (snd sign_nest_2_sol (Inl (FunctionEntry ''g'', [Statement 2, Statement 5])))) ''p'' = SPos"
  by eval

lemma sign_k2_g_entry_fneg:
  "sign_nest_lookup_exec_dg_st (locals (snd sign_nest_2_sol (Inl (FunctionEntry ''g'', [Statement 2, Statement 6])))) ''p'' = SNeg"
  by eval

theorem sign_k2_strictly_more_precise_than_k1_at_g:
  "sign_nest_lookup_exec_dg_st (locals (snd sign_nest_2_sol (Inl (FunctionEntry ''g'', [Statement 2, Statement 5])))) ''p''
     < sign_nest_lookup_exec_dg_st (locals (snd sign_nest_1_sol (Inl (FunctionEntry ''g'', [Statement 2])))) ''p''"
  "sign_nest_lookup_exec_dg_st (locals (snd sign_nest_2_sol (Inl (FunctionEntry ''g'', [Statement 2, Statement 6])))) ''p''
     < sign_nest_lookup_exec_dg_st (locals (snd sign_nest_1_sol (Inl (FunctionEntry ''g'', [Statement 2])))) ''p''"
  by (simp_all add: sign_k1_g_entry_top sign_k2_g_entry_fpos sign_k2_g_entry_fneg
                     less_sign_def sign_le_refl)

end

