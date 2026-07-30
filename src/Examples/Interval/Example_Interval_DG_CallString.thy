theory Example_Interval_DG_CallString
  imports
    Example_Interval_DG_Ctx_Sound
    "Voblint_Analysis.Activation_Backbone"
    "Voblint_Analysis.DG_Ctx_Activation"
begin

section \<open>A computed 1-call-string context, routed by call site\<close>

text \<open>
  \<^cite>\<open>SeidlEtAl2026\<close>, Example 7: for 1-call-string context-sensitivity, the context set
  \<open>C\<close> is the call sites of the program plus a distinguished \<open>_main\<close> element, and
  \<open>context\<^bsub>u,f,args\<^esub> _ _ = u\<close> --- the new context is exactly the call site, ignoring
  both the calling context and the entered value.

  \<open>Example_Interval_DG_Ctx_Collect\<close> routes \<open>twice\<close>'s two calls by \<^emph>\<open>decoding\<close> the entered
  formal (\<open>ivl_enterc\<close>, partial tabulation, the paper's Example 8).  This theory
  routes the same program by call site instead: the context type is \<^typ>\<open>cfg_node\<close>, and
  \<open>route_cs u ctx d ca = u\<close> is exactly the paper's Example 7.  Before \<open>enterc\<close> carried the
  call site (\<open>CFG_Local_Trace.key\<close>, widened for issue \<open>#66\<close>/G1), a call-site-keyed context
  had no semantic key to be proved sound against; this theory witnesses that the gap is
  closed.
\<close>

subsection \<open>The call-site route\<close>

text \<open>\<open>route_cs\<close> ignores the calling context and the entered data entirely, so it commutes
  with \<^emph>\<open>any\<close> representation map on \<open>'d\<close> --- in particular the executable/abstract
  refinement \<^const>\<open>fun_of_st\<close> --- for free.  One definition serves both the executable and
  the abstract routing hook below.\<close>

definition route_cs :: "pp \<Rightarrow> cfg_node \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> cfg_node" where
  "route_cs u ctx d ca = u"

lemma route_cs_commute: "route_cs u ctx (d::ivl st) ca = route_cs u ctx (fun_of_st d) ca"
  by (simp add: route_cs_def)

subsection \<open>A call-site-keyed global-key type\<close>

text \<open>Distinct constructor names from \<open>gk\<close> (\<open>Example_Interval_DG_Ctx_Flagship\<close>): both
  theories are imported here, and \<open>Seed\<close> would otherwise be ambiguous.\<close>

datatype gk_cs = GlobalCS | SeedCS pp cfg_node

subsection \<open>The routed equation system and its computed solution\<close>

text \<open>The enter-seed and combine trees are the generic \<^const>\<open>routed_cmb\<close>/\<^const>\<open>routed_extra\<close>
  from \<^theory>\<open>Voblint_Analysis.Routed_Context\<close>, instantiated at the call-site route below and
  the \<open>SeedCS\<close>/\<open>GlobalCS\<close> keys, rather than a hand-copied structural mirror.\<close>

text \<open>The root context is \<^const>\<open>cfg_entry\<close> \<open>twice_cfg\<close> --- \<open>main\<close>'s own entry node, the
  paper's distinguished \<open>_main\<close> element.  It is never a call site inside \<open>twice\<close>, so it
  cannot collide with a routed context.\<close>

definition twice_cs_eqs :: "(pp \<times> cfg_node, gk_cs, (ivl st, ivl st) dg_state) eqsT" where
  "twice_cs_eqs =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. GlobalCS) route_cs
       (routed_cmb Spoly GlobalCS) (routed_extra twice_cfg Spoly SeedCS GlobalCS)
       twice_cfg Spoly bot cinit_ivl_st (restrict_global_st cinit_ivl_st)"

definition twice_cs_sol ::
  "(pp \<times> cfg_node) set \<times> (pp \<times> cfg_node + gk_cs \<Rightarrow> (ivl st, ivl st) dg_state)" where
  "twice_cs_sol = TD_side_warrowing_apinis_Interp_solve twice_cs_eqs
                    (cfg_exit twice_cfg, cfg_entry twice_cfg)"

lemma twice_cs_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c twice_cs_eqs (cfg_exit twice_cfg, cfg_entry twice_cfg)
     \<noteq> None"
  by eval

subsection \<open>The two calling contexts are the call sites themselves\<close>

text \<open>Unlike \<open>ctx_call1\<close> / \<open>ctx_call2\<close> (\<open>Example_Interval_DG_Ctx_Flagship\<close>, decoded from the
  solved entry store), these contexts are syntactic: no solution lookup, no argument
  decoding, known before the solver runs.\<close>

definition ctx_call1_cs :: cfg_node where "ctx_call1_cs = Statement 2"
definition ctx_call2_cs :: cfg_node where "ctx_call2_cs = Statement 3"

lemma contexts_distinct_cs: "ctx_call1_cs \<noteq> ctx_call2_cs"
  by (simp add: ctx_call1_cs_def ctx_call2_cs_def)

subsection \<open>Per-context exact results\<close>

lemma call1_p_at_entry_cs:
  "lookup_st (locals (snd twice_cs_sol (Inl (FunctionEntry ''twice'', ctx_call1_cs)))) ''p''
     = Ivl (Fin 3) (Fin 3)"
  unfolding ctx_call1_cs_def by eval

lemma call2_p_at_entry_cs:
  "lookup_st (locals (snd twice_cs_sol (Inl (FunctionEntry ''twice'', ctx_call2_cs)))) ''p''
     = Ivl (Fin 10) (Fin 10)"
  unfolding ctx_call2_cs_def by eval

lemma call1_ret_at_exit_cs:
  "lookup_st (locals (snd twice_cs_sol (Inl (FunctionResult ''twice'', ctx_call1_cs)))) ''#ret''
     = Ivl (Fin 6) (Fin 6)"
  unfolding ctx_call1_cs_def by eval

lemma call2_ret_at_exit_cs:
  "lookup_st (locals (snd twice_cs_sol (Inl (FunctionResult ''twice'', ctx_call2_cs)))) ''#ret''
     = Ivl (Fin 20) (Fin 20)"
  unfolding ctx_call2_cs_def by eval

lemma x_computed_cs:
  "lookup_st (locals (snd twice_cs_sol (Inl (Statement 3, cfg_entry twice_cfg)))) ''x''
     = Ivl (Fin 6) (Fin 6)"
  by eval

lemma y_computed_cs:
  "lookup_st (locals (snd twice_cs_sol (Inl (Statement 4, cfg_entry twice_cfg)))) ''y''
     = Ivl (Fin 20) (Fin 20)"
  by eval

subsection \<open>Seed slots and coverage\<close>

lemma seed_call1_cs:
  "lookup_st (globs (snd twice_cs_sol (Inr (SeedCS (FunctionEntry ''twice'') ctx_call1_cs)))) ''p''
     = Ivl (Fin 3) (Fin 3)"
  unfolding ctx_call1_cs_def by eval

lemma seed_call2_cs:
  "lookup_st (globs (snd twice_cs_sol (Inr (SeedCS (FunctionEntry ''twice'') ctx_call2_cs)))) ''p''
     = Ivl (Fin 10) (Fin 10)"
  unfolding ctx_call2_cs_def by eval

text \<open>The callee entry is materialized once per call-site context and never under the root
  context: the two calls are analyzed separately, exactly as under \<open>ivl_enterc\<close>, but
  the routing key is now the call site instead of a decoded value.\<close>
lemma callee_covered_call1_cs: "(FunctionEntry ''twice'', ctx_call1_cs) \<in> fst twice_cs_sol"
  unfolding ctx_call1_cs_def by eval
lemma callee_covered_call2_cs: "(FunctionEntry ''twice'', ctx_call2_cs) \<in> fst twice_cs_sol"
  unfolding ctx_call2_cs_def by eval
lemma callee_not_under_root_cs:
  "(FunctionEntry ''twice'', cfg_entry twice_cfg) \<notin> fst twice_cs_sol"
  by eval

section \<open>Abstract transport of the routed solution\<close>

text \<open>
  \<open>route_cs\<close> ignores its data argument, so it commutes with the executable/abstract
  refinement map for free (\<open>route_cs_commute\<close>) and every \<^const>\<open>Side\<close> key computed from it
  is \<^emph>\<open>literally\<close> the same term on the executable and the abstract carrier --- unlike
  \<open>Example_Interval_DG_Ctx_Sound\<close>'s \<open>route_commute\<close>, no representation-transport lemma is
  needed to see the two keys agree.
\<close>

lemma dg_tree_st_commute_frame_read_cs:
  "dg_tree_st_commute env
     (QueryG (SeedCS v ctx) (\<lambda>s. Answer (DG (globs s) bot)))
     (QueryG (SeedCS v ctx) (\<lambda>s. Answer (DG (globs s) bot)))"
  by (simp add: dg_tree_st_commute_def fun_of_dg_st_simps fun_of_st_bot o_def
                dep_aux_def bot_fun_def)

lemma dg_tree_st_commute_routed_cmb_cs:
  "dg_tree_st_commute env (routed_cmb Spoly GlobalCS route_cs ctx ca cc ex)
                          (routed_cmb Sabs GlobalCS route_cs ctx ca cc ex)"
  unfolding routed_cmb_def Let_def
  by (cases ca)
     (simp_all add: dg_tree_st_commute_def fun_of_dg_st_simps fun_of_st_bot o_def
                    route_cs_def dgs_combine_fst_commute_gen dgs_combine_snd_commute_gen
                    dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

lemma dg_tree_st_commute_routed_enter_pub_cs:
  "dg_tree_st_commute env
     (with_call a (\<lambda>dst fs as. do {
        entry_state \<leftarrow> read_local (v, ctx);
        globals_state \<leftarrow> read_global GlobalCS;
        publish_global GlobalCS (enter_global Spoly fs as (locals entry_state) (globs globals_state));
        publish_seed (SeedCS w (route_cs v ctx (locals entry_state) a))
          (enter_local Spoly fs as (locals entry_state) (globs globals_state));
        answer_local bot
      }))
     (with_call a (\<lambda>dst fs as. do {
        entry_state \<leftarrow> read_local (v, ctx);
        globals_state \<leftarrow> read_global GlobalCS;
        publish_global GlobalCS (enter_global Sabs fs as (locals entry_state) (globs globals_state));
        publish_seed (SeedCS w (route_cs v ctx (locals entry_state) a))
          (enter_local Sabs fs as (locals entry_state) (globs globals_state));
        answer_local bot
      }))"
  by (cases a)
     (simp add: dg_tree_st_commute_def fun_of_dg_st_simps fun_of_st_bot o_def
                route_cs_def dgs_enter_fst_commute_gen dgs_enter_snd_commute_gen
                dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

lemma hextra_commute_routed_cs:
  "list_all2 (dg_tree_st_commute env)
     (routed_extra twice_cfg Spoly SeedCS GlobalCS route_cs ctx w)
     (routed_extra twice_cfg Sabs SeedCS GlobalCS route_cs ctx w)"
  unfolding routed_extra_def Let_def
  by (auto simp: list_all2_appendI list_all2_map1 list_all2_map2 list_all2_refl split_beta
                 dg_tree_st_commute_frame_read_cs dg_tree_st_commute_routed_enter_pub_cs
           split: cfg_node.split)

lemma twice_cs_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk_cs) TYPE((ivl st, ivl st) dg_state)
     twice_cs_eqs (cfg_exit twice_cfg, cfg_entry twice_cfg)"
  using twice_cs_terminates
  unfolding TD_side_warrowing_apinis_Interp.term_equivalence
            TD_side_warrowing_apinis_Interp.solve_c_dom_def
  by simp

lemma twice_cs_pp_st:
  "part_post_solution twice_cs_eqs (cfg_exit twice_cfg, cfg_entry twice_cfg)
     (snd twice_cs_sol) (fst twice_cs_sol)"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF twice_cs_solve_dom, of "fst twice_cs_sol" "snd twice_cs_sol"]
  unfolding twice_cs_sol_def by simp

theorem twice_cs_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. GlobalCS) route_cs
        (routed_cmb Sabs GlobalCS) (routed_extra twice_cfg Sabs SeedCS GlobalCS) twice_cfg Sabs
        (fun_of_st (bot::ivl st)) (fun_of_st cinit_ivl_st) (fun_of_st (restrict_global_st cinit_ivl_st)))
     (cfg_exit twice_cfg, cfg_entry twice_cfg) (fun_of_dg_st \<circ> snd twice_cs_sol) (fst twice_cs_sol)"
proof -
  have pp': "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. GlobalCS) route_cs
          (routed_cmb Spoly GlobalCS) (routed_extra twice_cfg Spoly SeedCS GlobalCS) twice_cfg Spoly
          bot cinit_ivl_st (restrict_global_st cinit_ivl_st))
       (cfg_exit twice_cfg, cfg_entry twice_cfg) (snd twice_cs_sol) (fst twice_cs_sol)"
    using twice_cs_pp_st unfolding twice_cs_eqs_def by simp
  have ivl_Hstep_cs:
    "map_prod fun_of_st fun_of_st (dg_spec_step Spoly a d g') =
       dg_spec_step Sabs a (fun_of_st d) (fun_of_st g')" for a d g'
    unfolding Spoly_def by (rule ivl_Hstep)
  show ?thesis
    by (rule part_post_solution_seed_dg_st_to_abs
          [where pred_sel = intra_predecessor_list and gkey = "\<lambda>_. GlobalCS"
             and route_st = route_cs and route_abs = route_cs
             and cmb_st = "routed_cmb Spoly GlobalCS" and cmb_abs = "routed_cmb Sabs GlobalCS"
             and extra_st = "routed_extra twice_cfg Spoly SeedCS GlobalCS"
             and extra_abs = "routed_extra twice_cfg Sabs SeedCS GlobalCS"
             and g = twice_cfg and S_st = Spoly and S_abs = Sabs,
           OF ivl_Hstep_cs route_cs_commute dg_tree_st_commute_routed_cmb_cs
              hextra_commute_routed_cs pp'])
qed

section \<open>Activation-indexed collecting soundness for the call-site-routed solution\<close>

text \<open>The semantic context function: exactly \<^const>\<open>route_cs\<close>, restricted to a concrete
  \<^typ>\<open>store\<close>.  This is the \<open>enterc\<close> the paper's Example 7 asks for, and the widened
  \<^const>\<open>key\<close> (\<open>CFG_Local_Trace.thy\<close>, G1) is what lets it be stated at all.\<close>

definition enterc_cs :: "cfg_node \<Rightarrow> cfg_node \<Rightarrow> store \<Rightarrow> cfg_node" where
  "enterc_cs u ctx s = u"

abbreviation sigma_cs :: "pp \<times> cfg_node + gk_cs \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state" where
  "sigma_cs \<equiv> fun_of_dg_st \<circ> snd twice_cs_sol"

abbreviation gen_cs_abs :: "(pp \<times> cfg_node, gk_cs, (ivl abs_state, ivl abs_state) dg_state) eqsT" where
  "gen_cs_abs \<equiv> side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. GlobalCS) route_cs
       (routed_cmb Sabs GlobalCS) (routed_extra twice_cfg Sabs SeedCS GlobalCS) twice_cfg Sabs
       (fun_of_st (bot::ivl st)) (fun_of_st cinit_ivl_st) (fun_of_st (restrict_global_st cinit_ivl_st))"

lemma pp_eq_bound_cs:
  "(v, ctx) \<in> fst twice_cs_sol
     \<Longrightarrow> eq gen_cs_abs (v, ctx) sigma_cs \<le> sigma_cs (Inl (v, ctx))"
  using twice_cs_pp_abs by simp

text \<open>The accumulator fold only grows the start value --- generic in the strategy-tree
  shape, unrelated to \<open>ivl\<close> or the routing policy.\<close>
lemma side_acc_dg_ge_cs: "acc \<le> side_acc_dg acc \<tau> ts"
proof (induction ts arbitrary: acc)
  case (Cons t ts)
  show ?case
    using Cons.IH[of "acc \<squnion> locals (traverse_rhs t \<tau>)"]
    by (simp add: le_supI1)
qed simp

definition ivl_ctx_sg_cs :: "pp \<times> cfg_node + gk_cs \<Rightarrow> ivl abs_state" where
  "ivl_ctx_sg_cs k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst twice_cs_sol
           then locals (sigma_cs (Inl (v, ctx))) \<squnion> globs (sigma_cs (Inr GlobalCS))
           else bot)
      | Inr _ \<Rightarrow> bot)"

lemma ivl_ctx_sg_cs_covered:
  "(v, ctx) \<in> fst twice_cs_sol
   \<Longrightarrow> ivl_ctx_sg_cs (Inl (v, ctx)) = locals (sigma_cs (Inl (v, ctx))) \<squnion> globs (sigma_cs (Inr GlobalCS))"
  by (simp add: ivl_ctx_sg_cs_def)

lemma ivl_ctx_sg_cs_uncovered_empty:
  "(v, ctx) \<notin> fst twice_cs_sol \<Longrightarrow> \<lbrakk>ivl_ctx_sg_cs (Inl (v, ctx))\<rbrakk> = {}"
  by (simp add: ivl_ctx_sg_cs_def gamma_state_bot)

lemma entry_locals_ge_s0d_cs:
  assumes cov: "(cfg_entry twice_cfg, cfg_entry twice_cfg) \<in> fst twice_cs_sol"
  shows "fun_of_st cinit_ivl_st \<le> locals (sigma_cs (Inl (cfg_entry twice_cfg, cfg_entry twice_cfg)))"
proof -
  have "fun_of_st cinit_ivl_st
          \<le> locals (eq gen_cs_abs (cfg_entry twice_cfg, cfg_entry twice_cfg) sigma_cs)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_cs], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma_cs (Inl (cfg_entry twice_cfg, cfg_entry twice_cfg)))"
    using pp_eq_bound_cs[OF cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma entry_covered_cs: "(cfg_entry twice_cfg, cfg_entry twice_cfg) \<in> fst twice_cs_sol"
  unfolding twice_cs_sol_def twice_cs_eqs_def by eval

lemma twice_fwd_closed_all_cs:
  "\<forall>(u, c)\<in>fst twice_cs_sol. \<forall>(u', a, v)\<in>intra twice_cfg.
      u = u' \<longrightarrow> (v, c) \<in> fst twice_cs_sol"
  unfolding twice_cs_sol_def twice_cs_eqs_def by eval

lemma twice_fwd_closed_cs:
  assumes "(u, ctx) \<in> fst twice_cs_sol" and "(u, a, v) \<in> intra twice_cfg"
  shows "(v, ctx) \<in> fst twice_cs_sol"
  using twice_fwd_closed_all_cs assms by fastforce

interpretation twice_cs_dg: dg_ctx_activation Sabs is_global twice_cfg GlobalCS route_cs
    "routed_cmb Sabs GlobalCS" "routed_extra twice_cfg Sabs SeedCS GlobalCS"
    "fun_of_st (bot::ivl st)" "fun_of_st cinit_ivl_st" "fun_of_st (restrict_global_st cinit_ivl_st)"
    sigma_cs "fst twice_cs_sol" "(cfg_exit twice_cfg, cfg_entry twice_cfg)" ivl_ctx_sg_cs
proof unfold_locales
  show "finite (intra twice_cfg)" by (rule twice_finE)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. GlobalCS) route_cs
             (routed_cmb Sabs GlobalCS) (routed_extra twice_cfg Sabs SeedCS GlobalCS) twice_cfg Sabs
             (fun_of_st (bot::ivl st)) (fun_of_st cinit_ivl_st)
             (fun_of_st (restrict_global_st cinit_ivl_st)))
          (cfg_exit twice_cfg, cfg_entry twice_cfg) sigma_cs (fst twice_cs_sol)"
    by (rule twice_cs_pp_abs)
next
  fix v ctx
  assume "(v, ctx) \<in> fst twice_cs_sol"
  thus "ivl_ctx_sg_cs (Inl (v, ctx)) = locals (sigma_cs (Inl (v, ctx))) \<squnion> globs (sigma_cs (Inr GlobalCS))"
    by (rule ivl_ctx_sg_cs_covered)
next
  fix v ctx
  assume "(v, ctx) \<notin> fst twice_cs_sol"
  thus "\<lbrakk>ivl_ctx_sg_cs (Inl (v, ctx))\<rbrakk> = {}"
    by (rule ivl_ctx_sg_cs_uncovered_empty)
next
  fix u a v ctx
  assume "(u, ctx) \<in> fst twice_cs_sol" "(u, a, v) \<in> intra twice_cfg"
  thus "(v, ctx) \<in> fst twice_cs_sol" by (rule twice_fwd_closed_cs)
qed

section \<open>SEED_G and COMB: the two calls resumed at their own call site\<close>

text \<open>\<open>enterc_cs u ctx s = u\<close> unconditionally, so unlike \<open>ivl_ctx_sg_seed\<close> /
  \<open>ivl_ctx_sg_comb\<close> (\<open>Example_Interval_DG_Ctx_Collect\<close>), no \<open>enter_route_exact\<close> /
  \<open>comb_route\<close> lemma is needed to show the routed context is the one the executable bound
  was computed at: after fixing the call site by the \<open>twice_calls\<close> case split, the context is
  already syntactically \<open>ctx_call1_cs\<close> / \<open>ctx_call2_cs\<close>.  The remaining content --- that the
  executable enter/combine transfer stays under the routed slot --- is exactly the same
  numeric fact as the partial-tabulation instance, re-evaluated against \<^const>\<open>twice_cs_sol\<close>.\<close>

lemma enter_callers_only_root_cs:
  "\<forall>(p, ctx)\<in>fst twice_cs_sol.
     (p = Statement 2 \<or> p = Statement 3) \<longrightarrow> ctx = cfg_entry twice_cfg"
  unfolding twice_cs_sol_def twice_cs_eqs_def by eval

text \<open>SEED_G and COMB both land as corollaries of the routed interpretation below
  (\<open>twice_cs_routed.routed_context_call\<close> / \<open>routed_context_comb\<close>), once the coverage
  facts this section built are in scope.\<close>

lemma covered_ret5_cs: "(Statement 3, cfg_entry twice_cfg) \<in> fst twice_cs_sol"
  unfolding twice_cs_sol_def twice_cs_eqs_def by eval
lemma covered_ret7_cs: "(Statement 4, cfg_entry twice_cfg) \<in> fst twice_cs_sol"
  unfolding twice_cs_sol_def twice_cs_eqs_def by eval
lemma callee_exit_covered_call1_cs: "(FunctionResult ''twice'', ctx_call1_cs) \<in> fst twice_cs_sol"
  unfolding twice_cs_sol_def twice_cs_eqs_def ctx_call1_cs_def by eval
lemma callee_exit_covered_call2_cs: "(FunctionResult ''twice'', ctx_call2_cs) \<in> fst twice_cs_sol"
  unfolding twice_cs_sol_def twice_cs_eqs_def ctx_call2_cs_def by eval

subsection \<open>The routed interpretation and its CALL/COMB corollaries\<close>

text \<open>Both \<open>route_cs\<close> and \<open>enterc_cs\<close> are the constant function \<open>u\<close>, unconditionally: the
  route-agreement obligation \<open>route_enterc_agree\<close> is therefore a bare reflexivity, needing
  neither the coverage-restricted pinning nor the numeric per-call evaluation the
  partial-tabulation instance's routing needed. \<open>call_fwd\<close> and \<open>comb_fwd\<close> are the same
  coverage facts \<open>ivl_ctx_sg_cs_seed\<close> / \<open>ivl_ctx_sg_cs_comb\<close> used to need by hand.\<close>

interpretation twice_cs_routed: routed_context Sabs is_global twice_cfg GlobalCS route_cs
    "fun_of_st (bot::ivl st)" "fun_of_st cinit_ivl_st" "fun_of_st (restrict_global_st cinit_ivl_st)"
    sigma_cs "fst twice_cs_sol" "(cfg_exit twice_cfg, cfg_entry twice_cfg)" ivl_ctx_sg_cs
    SeedCS enterc_cs
proof (unfold_locales, goal_cases FinC SeedKey RouteAgree CallFwd CombFwd EnterAgree)
  case FinC
  show ?case by (rule twice_finC)
next
  case (SeedKey p ctx)
  show ?case by simp
next
  case (RouteAgree u ctx dst pars args p cont s)
  show ?case by (simp add: route_cs_def enterc_cs_def)
next
  case (CallFwd u ctx dst pars args p cont)
  note ce = CallFwd(2)
  from ce consider
      (c1) "u = Statement 2" "p = ''twice''"
    | (c2) "u = Statement 3" "p = ''twice''"
    unfolding twice_calls by auto
  thus ?case
  proof cases
    case c1
    thus ?thesis using callee_covered_call1_cs by (simp add: route_cs_def ctx_call1_cs_def)
  next
    case c2
    thus ?thesis using callee_covered_call2_cs by (simp add: route_cs_def ctx_call2_cs_def)
  qed
next
  case (CombFwd cl c1 dst pars args p cont)
  note covCl = CombFwd(1) and ce = CombFwd(2)
  show ?case
    using ce covCl enter_callers_only_root_cs covered_ret5_cs covered_ret7_cs
    unfolding twice_calls by auto
next
  case (EnterAgree cl s es dst pars args p cont)
  note ces = EnterAgree(1) and ce = EnterAgree(2)
  show ?case
    using ces ce unfolding call_enter_store_def by (auto simp: twice_calls)
qed

lemma ivl_ctx_sg_cs_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls twice_cfg"
    and "s \<in> \<lbrakk>ivl_ctx_sg_cs (Inl (u, ctx))\<rbrakk>"
  shows "call_enter is_global (CallEdge dst xs es) s
           \<in> \<lbrakk>ivl_ctx_sg_cs (Inl (FunctionEntry p,
                 enterc_cs u ctx (call_enter is_global (CallEdge dst xs es) s)))\<rbrakk>"
  by (rule twice_cs_routed.routed_context_call[OF assms])

lemma ivl_ctx_sg_cs_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls twice_cfg"
    and "s \<in> \<lbrakk>ivl_ctx_sg_cs (Inl (cl, c1))\<rbrakk>"
    and "t \<in> \<lbrakk>ivl_ctx_sg_cs (Inl (FunctionResult p, enterc_cs cl c1 es))\<rbrakk>"
    and "call_enter_store is_global twice_cfg cl s es"
  shows "combine_collect is_global dst s t \<in> \<lbrakk>ivl_ctx_sg_cs (Inl (v, c1))\<rbrakk>"
  by (rule twice_cs_routed.routed_context_comb[OF assms])

section \<open>The headline theorem: k-call-string activation collecting soundness\<close>

text \<open>Instantiating the generic \<open>activation_collect_sound\<close> --- unchanged since G1, only
  \<open>enterc\<close> widened to see the call site --- at \<open>enterc_cs\<close>.  This is the theorem the issue
  says has no image: a routed context that is \<^emph>\<open>literally\<close> the call site, certified against
  the same activation-collecting semantics as \<open>twice_activation_collect_sound\<close>
  (\<open>Example_Interval_DG_Ctx_Collect\<close>).\<close>

lemma cinit_le_cinit_ivl_st: "cinit_stores is_global \<subseteq> \<lbrakk>fun_of_st cinit_ivl_st\<rbrakk>"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_st_cinit_ivl_st)

theorem twice_cs_activation_collect_sound:
  "activation_collect is_global enterc_cs (cfg_entry twice_cfg) twice_cfg (cinit_stores is_global) v ctx
     \<subseteq> \<lbrakk>ivl_ctx_sg_cs (Inl (v, ctx))\<rbrakk>"
proof (rule activation_collect_sound[where sg = ivl_ctx_sg_cs and enterc = enterc_cs
        and seedc = "cfg_entry twice_cfg" and S = "cinit_stores is_global" and g = twice_cfg and gs = is_global])
  \<comment> \<open>ENTRY_G\<close>
  fix s assume "s \<in> cinit_stores is_global"
  hence "s \<in> \<lbrakk>fun_of_st cinit_ivl_st\<rbrakk>" using cinit_le_cinit_ivl_st by blast
  also have "\<lbrakk>fun_of_st cinit_ivl_st\<rbrakk>
        \<subseteq> \<lbrakk>locals (sigma_cs (Inl (cfg_entry twice_cfg, cfg_entry twice_cfg)))\<rbrakk>"
    by (rule gamma_state_mono[OF entry_locals_ge_s0d_cs[OF entry_covered_cs]])
  also have "\<dots> \<subseteq> \<lbrakk>ivl_ctx_sg_cs (Inl (cfg_entry twice_cfg, cfg_entry twice_cfg))\<rbrakk>"
    unfolding ivl_ctx_sg_cs_covered[OF entry_covered_cs] by (rule gamma_state_sup_ub1)
  finally show "s \<in> \<lbrakk>ivl_ctx_sg_cs (Inl (cfg_entry twice_cfg, cfg_entry twice_cfg))\<rbrakk>" .
next
  \<comment> \<open>EDGE --- discharged generically off the post-solution by \<open>dg_ctx_activation\<close>.\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> intra twice_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg_cs (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>ivl_ctx_sg_cs (Inl (v, c))\<rbrakk>"
    by (rule twice_cs_dg.dg_ctx_act_edge)
next
  \<comment> \<open>CALL --- enter routed to the call site itself: \<open>ivl_ctx_sg_cs_seed\<close>.\<close>
  show "\<And>u dst pars args p cont c s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls twice_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg_cs (Inl (u, c))\<rbrakk>
        \<Longrightarrow> call_enter is_global (CallEdge dst pars args) s
             \<in> \<lbrakk>ivl_ctx_sg_cs (Inl (FunctionEntry p,
                    enterc_cs u c (call_enter is_global (CallEdge dst pars args) s)))\<rbrakk>"
    by (rule ivl_ctx_sg_cs_seed)
next
  \<comment> \<open>COMB --- return combine at the caller's own call-site context.\<close>
  show "\<And>cl dst pars args p cont c1 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls twice_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg_cs (Inl (cl, c1))\<rbrakk>
        \<Longrightarrow> t \<in> \<lbrakk>ivl_ctx_sg_cs (Inl (FunctionResult p, enterc_cs cl c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store is_global twice_cfg cl s es
        \<Longrightarrow> combine_collect is_global dst s t \<in> \<lbrakk>ivl_ctx_sg_cs (Inl (cont, c1))\<rbrakk>"
    by (rule ivl_ctx_sg_cs_comb)
qed

section \<open>Call-site-context-expanded analysis graph\<close>

text \<open>The same exporter as \<^const>\<open>twice_ctx_graph\<close> (\<open>Example_Interval_DG_Ctx_Flagship\<close>),
  instantiated at the call-site context.  \<^const>\<open>string_of_cfg_node\<close> --- the CFG's own node
  printer --- doubles as \<open>show_context\<close>, since a context \<^emph>\<open>is\<close> a \<^typ>\<open>cfg_node\<close> here: the two
  routed callee clusters are labelled by the call site that created them, not by a decoded
  value.\<close>

definition twice_cs_graph_config ::
  "(cfg_node, gk_cs, (ivl st, ivl st) dg_state, ivl st) analysis_graph_config" where
  "twice_cs_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>u ctx action d. route_cs u ctx d action),
      show_context = string_of_cfg_node,
      locals_for_pp = (\<lambda>p.
        let sc = compiled_procedure_scope twice_pi twice_procs ''main'' twice_main
          twice_cfg p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope twice_pi twice_procs ''main'' twice_main
          twice_cfg p)),
      globals_to_show = [],
      show_local = (\<lambda>p ctx vars d. map (\<lambda>x.
        x @ ''='' @ string_of_ivl (lookup_st d x)) vars),
      format_return = (\<lambda>p ctx ret d.
        if lookup_st d ret = ivl_top then []
        else [''ret='' @ string_of_ivl (lookup_st d ret)]),
      show_global = (\<lambda>k vars s. [''(none)'']),
      show_global_key = (\<lambda>k. case k of GlobalCS \<Rightarrow> ''Global'' | SeedCS p ctx \<Rightarrow> ''Seed''),
      is_shared_global = (\<lambda>k. case k of GlobalCS \<Rightarrow> True | SeedCS _ _ \<Rightarrow> False),
      show_internal_globals = False,
      owner_of = compiled_owner_of twice_pi twice_procs ''main'' twice_main,
      cluster_label = (\<lambda>owner ctx.
        if owner = ''main'' \<and> ctx = cfg_entry twice_cfg then ''main / root context''
        else owner @ '' / call site='' @ string_of_cfg_node ctx),
      source_text = Some (pretty_string_of_program twice_pi twice_procs twice_main)
    \<rparr>"

definition twice_cs_contexts_for_pp :: "pp \<Rightarrow> cfg_node list" where
  "twice_cs_contexts_for_pp p =
    (if compiled_owner_of twice_pi twice_procs ''main'' twice_main p = ''main''
     then [cfg_entry twice_cfg] else [ctx_call1_cs, ctx_call2_cs])"

definition twice_cs_local_graph_domain :: "(pp \<times> cfg_node + gk_cs) list" where
  "twice_cs_local_graph_domain =
    contextual_graph_domain twice_cfg twice_cs_contexts_for_pp"

definition twice_cs_seed_keys :: "gk_cs list" where
  "twice_cs_seed_keys =
     map (\<lambda>ctx. SeedCS (FunctionEntry ''twice'') ctx) [ctx_call1_cs, ctx_call2_cs]"

definition twice_cs_graph_domain :: "(pp \<times> cfg_node + gk_cs) list" where
  "twice_cs_graph_domain =
    twice_cs_local_graph_domain @ map Inr twice_cs_seed_keys"

definition twice_cs_graph :: "(cfg_node, gk_cs) analysis_graph" where
  "twice_cs_graph =
    build_analysis_graph twice_cs_graph_config twice_cfg twice_cs_graph_domain
      (snd twice_cs_sol)"

definition twice_cs_dot :: String.literal where
  "twice_cs_dot =
    String.implode
      (analysis_graph_to_dot twice_cs_graph_config twice_cfg (snd twice_cs_sol)
        twice_cs_graph)"

lemma twice_cs_graph_wf: "analysis_graph_wf twice_cs_graph" by eval

lemma twice_cs_graph_domain_is_covered:
  "list_all (\<lambda>x. case x of Inl pc \<Rightarrow> pc \<in> fst twice_cs_sol | Inr _ \<Rightarrow> True)
    twice_cs_graph_domain" by eval

text \<open>The two callee clusters are labelled by the call sites \<open>Statement 2\<close> / \<open>Statement 3\<close>
  themselves --- distinct without decoding any argument --- unlike \<^const>\<open>twice_ctx_graph\<close>'s
  \<open>ctx_call1\<close>/\<open>ctx_call2\<close> clusters, which are labelled by the entered value \<open>[3,3]\<close>/\<open>[10,10]\<close>.\<close>

lemma twice_cs_graph_has_both_callees:
  "LocalNode (FunctionEntry ''twice'') ctx_call1_cs \<in> set (analysis_graph_nodes twice_cs_graph) \<and>
   LocalNode (FunctionEntry ''twice'') ctx_call2_cs \<in> set (analysis_graph_nodes twice_cs_graph)"
  by eval

lemma twice_cs_graph_hides_uncovered_root_callee:
  "LocalNode (FunctionEntry ''twice'') (cfg_entry twice_cfg) \<notin> set (analysis_graph_nodes twice_cs_graph)"
  by eval

lemma twice_cs_graph_enter_edges:
  "filter (\<lambda>e. case e of (_, EnterEdge _ _, _) \<Rightarrow> True | _ \<Rightarrow> False)
    (analysis_graph_edges twice_cs_graph) =
    [(LocalNode (Statement 2) (cfg_entry twice_cfg),
      EnterEdge ''twice'' (CallEdge (Some ''x'') [''p''] [VIMP_Syntax.N 3]),
      LocalNode (FunctionEntry ''twice'') ctx_call1_cs),
     (LocalNode (Statement 3) (cfg_entry twice_cfg),
      EnterEdge ''twice'' (CallEdge (Some ''y'') [''p''] [VIMP_Syntax.N 10]),
      LocalNode (FunctionEntry ''twice'') ctx_call2_cs)]" by eval

lemma twice_cs_graph_combine_edges:
  "filter (\<lambda>e. case e of (_, CombineEdge _ _ _, _) \<Rightarrow> True | _ \<Rightarrow> False)
    (analysis_graph_edges twice_cs_graph) =
    [(LocalNode (FunctionResult ''twice'') ctx_call1_cs,
      CombineEdge (Statement 2) (Some ''x'') (Some ''#ret''),
      LocalNode (Statement 3) (cfg_entry twice_cfg)),
     (LocalNode (FunctionResult ''twice'') ctx_call2_cs,
      CombineEdge (Statement 3) (Some ''y'') (Some ''#ret''),
      LocalNode (Statement 4) (cfg_entry twice_cfg))]"
  by eval

lemma twice_cs_dot_has_context_clusters: "String.explode twice_cs_dot \<noteq> []" by eval

ML_val \<open>writeln (@{code twice_cs_dot})\<close>

end
