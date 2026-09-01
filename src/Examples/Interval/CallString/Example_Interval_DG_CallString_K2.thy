theory Example_Interval_DG_CallString_K2
  imports
    Example_Interval_DG_CallString_K1
begin

section \<open>A computed 2-call-string context, routed by truncated call history\<close>

text \<open>
  The \<open>k = 2\<close> sibling of \<^theory>\<open>Voblint_Examples.Example_Interval_DG_CallString_K1\<close>, same
  \<open>nest\<close> program and same Base-style storage: \<open>g\<close>'s single call site is reached from two
  different \<open>f\<close> activations. At \<open>k = 1\<close> both collapse into one merged context; at \<open>k = 2\<close>
  the call string also records which \<open>f\<close> call led there, so the two stay separate. Only
  the bound changes --- the specification, the transport, and the routed locale are the
  ones \<open>k = 1\<close> already fixed.
\<close>

subsection \<open>The routed equation system and its computed solution\<close>

text \<open>Reuses \<^type>\<open>call_string_gk\<close> from \<^theory>\<open>Voblint_Core.Call_String_Context\<close> rather
  than minting its own global-key type: the key shape never depended on \<open>k\<close>, only the
  \<open>Seed\<close> payload's context length did.\<close>

definition nest_2_eqs ::
  "(pp \<times> cfg_node list, call_string_gk,
     (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "nest_2_eqs =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global) (cs_route 2)
      (\<lambda>ctx' src a. dg_spec_edge_tree nest_S_st a src Global)
      (routed_cmb_g nest_S_st Global Seed (static_resolve nest_cfg))
      (routed_extra_g Seed Global)
       nest_cfg Bot (Lifted cinit_ivl_st) Bot"

definition nest_2_sol ::
  "(pp \<times> cfg_node list) set
     \<times> (pp \<times> cfg_node list + call_string_gk
          \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "nest_2_sol = TD_side_warrowing_apinis_Interp_solve nest_2_eqs
                    (cfg_exit nest_cfg, [])"

lemma nest_2_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c nest_2_eqs (cfg_exit nest_cfg, [])
     \<noteq> None"
  by eval

subsection \<open>Coverage\<close>

text \<open>The full solved node set, computed once; every membership fact below is a
  \<open>simp\<close> lookup into this literal set instead of a separate \<open>eval\<close> re-derivation.\<close>

definition nest_2_nodes :: "(pp \<times> cfg_node list) set" where
  "nest_2_nodes = {
     (FunctionEntry (STR ''main''), []), (Statement 5, []), (Statement 6, []), (Statement 7, []),
     (FunctionEntry (STR ''f''), [Statement 5]), (Statement 2, [Statement 5]),
     (Statement 3, [Statement 5]), (FunctionResult (STR ''f''), [Statement 5]),
     (FunctionEntry (STR ''f''), [Statement 6]), (Statement 2, [Statement 6]),
     (Statement 3, [Statement 6]), (FunctionResult (STR ''f''), [Statement 6]),
     (FunctionEntry (STR ''g''), [Statement 2, Statement 5]), (Statement 0, [Statement 2, Statement 5]),
     (FunctionResult (STR ''g''), [Statement 2, Statement 5]),
     (FunctionEntry (STR ''g''), [Statement 2, Statement 6]), (Statement 0, [Statement 2, Statement 6]),
     (FunctionResult (STR ''g''), [Statement 2, Statement 6]),
     (FunctionResult (STR ''main''), [])}"

lemma nest_2_nodes_eq: "fst nest_2_sol = nest_2_nodes"
  unfolding nest_2_sol_def nest_2_eqs_def nest_2_nodes_def by eval

lemma entry_covered_2: "(cfg_entry nest_cfg, []) \<in> fst nest_2_sol"
  unfolding nest_entry nest_2_nodes_eq nest_2_nodes_def by simp

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
  unfolding nest_2_nodes_eq nest_2_nodes_def by simp

lemma enter_callers_g_2:
  "\<forall>(p, ctx)\<in>fst nest_2_sol.
     p = Statement 2 \<longrightarrow> ctx = [Statement 5] \<or> ctx = [Statement 6]"
  unfolding nest_2_nodes_eq nest_2_nodes_def by simp

lemma callee_covered_f3_2: "(FunctionEntry (STR ''f''), [Statement 5]) \<in> fst nest_2_sol"
  unfolding nest_2_nodes_eq nest_2_nodes_def by simp
lemma callee_covered_f10_2: "(FunctionEntry (STR ''f''), [Statement 6]) \<in> fst nest_2_sol"
  unfolding nest_2_nodes_eq nest_2_nodes_def by simp
lemma callee_covered_g_f3_2: "(FunctionEntry (STR ''g''), [Statement 2, Statement 5]) \<in> fst nest_2_sol"
  unfolding nest_2_nodes_eq nest_2_nodes_def by simp
lemma callee_covered_g_f10_2: "(FunctionEntry (STR ''g''), [Statement 2, Statement 6]) \<in> fst nest_2_sol"
  unfolding nest_2_nodes_eq nest_2_nodes_def by simp

lemma covered_ret6_2: "(Statement 6, []) \<in> fst nest_2_sol"
  unfolding nest_2_nodes_eq nest_2_nodes_def by simp
lemma covered_ret7_2: "(Statement 7, []) \<in> fst nest_2_sol"
  unfolding nest_2_nodes_eq nest_2_nodes_def by simp
lemma covered_ret3_f3_2: "(Statement 3, [Statement 5]) \<in> fst nest_2_sol"
  unfolding nest_2_nodes_eq nest_2_nodes_def by simp
lemma covered_ret3_f10_2: "(Statement 3, [Statement 6]) \<in> fst nest_2_sol"
  unfolding nest_2_nodes_eq nest_2_nodes_def by simp


section \<open>The solver's post-solution\<close>

lemma nest_2_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk)
     TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
     nest_2_eqs (cfg_exit nest_cfg, [])"
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF nest_2_terminates])

lemma nest_2_pp_st:
  "part_post_solution nest_2_eqs (cfg_exit nest_cfg, [])
     (snd nest_2_sol) (fst nest_2_sol)"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF nest_2_solve_dom, of "fst nest_2_sol" "snd nest_2_sol"]
  unfolding nest_2_sol_def by simp

section \<open>Activation-indexed collecting soundness for the 2-call-string-routed solution\<close>

definition nest_2_sg ::
  "pp \<times> cfg_node list + call_string_gk \<Rightarrow> ivl exec_dg_st lifted" where
  "nest_2_sg z =
     (case z of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst nest_2_sol then locals (snd nest_2_sol (Inl (v, ctx))) else Bot)
      | Inr _ \<Rightarrow> Bot)"

lemma nest_2_sg_covered:
  "(v, ctx) \<in> fst nest_2_sol
     \<Longrightarrow> nest_2_sg (Inl (v, ctx)) = locals (snd nest_2_sol (Inl (v, ctx)))"
  by (simp add: nest_2_sg_def)

lemma nest_2_sg_uncovered_empty:
  "(v, ctx) \<notin> fst nest_2_sol
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) (nest_2_sg (Inl (v, ctx)))) = {}"
  by (simp add: nest_2_sg_def)

text \<open>Unlike \<open>k = 1\<close>, \<open>call_fwd\<close>'s \<open>Statement 2\<close> case now genuinely splits: \<open>g\<close>'s call site
  is covered at two distinct one-element contexts, and \<open>take 2\<close> keeps them apart after
  routing, so each needs its own coverage witness. Everything else the routed locale asks
  for is discharged generically at \<^const>\<open>cs_route\<close>, exactly as at \<open>k = 1\<close>.\<close>

interpretation nest_2_cs: call_string_routed_context
    nest_S_st nest_gamma nest_gs nest_pi nest_procs 2 Bot "Lifted cinit_ivl_st" Bot
    "snd nest_2_sol" "fst nest_2_sol" "(cfg_exit nest_cfg, [])" nest_2_sg
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) m)"
proof (unfold_locales, unfold nest_cfg_compile,
       goal_cases FinE PP SgCov SgUncov Fwd CallFwd CombFwd)
  case FinE
  show ?case by (rule nest_finE)
next
  case PP
  show ?case by (rule nest_2_pp_st[unfolded nest_2_eqs_def])
next
  case (SgCov v c)
  show ?case using SgCov by (simp add: nest_2_sg_covered nest_gamma_def)
next
  case (SgUncov v c)
  show ?case using SgUncov by (rule nest_2_sg_uncovered_empty)
next
  case (Fwd u a v c)
  show ?case using Fwd by (rule nest_fwd_closed_2)
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
  show ?case
    using CombFwd enter_callers_only_root_main_2 enter_callers_g_2
          covered_ret3_f3_2 covered_ret3_f10_2 covered_ret6_2 covered_ret7_2
          nest_calls_shape
    by fastforce
qed

lemma nest_2_sg_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls nest_cfg"
    and "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) (nest_2_sg (Inl (u, ctx))))"
  shows "call_enter nest_gs (CallEdge dst xs es) s
           \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs)
               (nest_2_sg (Inl (FunctionEntry p,
                 cs_context 2 u ctx (call_enter nest_gs (CallEdge dst xs es) s)))))"
  by (rule nest_2_cs.routed_context_call[OF assms[unfolded nest_cfg_def]])

lemma nest_2_sg_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls nest_cfg"
    and "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) (nest_2_sg (Inl (cl, c1))))"
    and "t \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs)
               (nest_2_sg (Inl (FunctionResult p, cs_context 2 cl c1 es))))"
    and "call_enter_store nest_gs nest_cfg cl s es"
  shows "combine_collect nest_gs dst s t
           \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) (nest_2_sg (Inl (v, c1))))"
  by (rule nest_2_cs.routed_context_comb[OF assms[unfolded nest_cfg_def]])

section \<open>The headline theorem: 2-call-string activation collecting soundness\<close>

theorem nest_2_activation_collect_sound:
  "activation_collect nest_gs (cs_context 2) [] nest_cfg (cinit_stores nest_gs) v ctx
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) (nest_2_sg (Inl (v, ctx))))"
  by (rule nest_2_cs.activation_collect_sound[unfolded nest_cfg_compile,
            OF entry_covered_2 nest_cinit_le_cinit_ivl_st])


section \<open>What the second call-string frame buys\<close>

text \<open>Both \<open>f\<close> activations reach \<open>g\<close> through the same call site \<open>Statement 2\<close>, so at
  \<open>k = 1\<close> \<open>g\<close>'s entry unknown is updated twice from below and widens; at \<open>k = 2\<close> the
  retained second frame separates the two activations, each entry unknown is written
  once, and every value below is exact.\<close>

lemma nest_2_g_entry_first:
  "nest_lookup (locals (snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 5])))) (STR ''p'')
     = Ivl (Fin 3) (Fin 3)"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma nest_2_g_entry_second:
  "nest_lookup (locals (snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 6])))) (STR ''p'')
     = Ivl (Fin 10) (Fin 10)"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma nest_2_g_result_first:
  "nest_lookup (locals (snd nest_2_sol (Inl (FunctionResult (STR ''g''), [Statement 2, Statement 5])))) (STR ''#ret'')
     = Ivl (Fin 6) (Fin 6)"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma nest_2_g_result_second:
  "nest_lookup (locals (snd nest_2_sol (Inl (FunctionResult (STR ''g''), [Statement 2, Statement 6])))) (STR ''#ret'')
     = Ivl (Fin 20) (Fin 20)"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma nest_2_t_after_inner_return:
  "nest_lookup (locals (snd nest_2_sol (Inl (Statement 3, [Statement 5])))) (STR ''t'')
     = Ivl (Fin 6) (Fin 6)"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma nest_2_x_after_first_return:
  "nest_lookup (locals (snd nest_2_sol (Inl (Statement 6, [])))) (STR ''x'') = Ivl (Fin 6) (Fin 6)"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma nest_2_y_after_second_return:
  "nest_lookup (locals (snd nest_2_sol (Inl (Statement 7, [])))) (STR ''y'') = Ivl (Fin 20) (Fin 20)"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

text \<open>The precision witness: at \<open>g\<close>'s entry and at both of \<open>main\<close>'s destinations the
  \<open>k = 2\<close> value is strictly below the \<open>k = 1\<close> value, so the second retained frame is not
  merely a different key space --- it is strictly more precise on this program.\<close>

theorem nest_k2_strictly_more_precise_than_k1:
  "nest_lookup (locals (snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 5])))) (STR ''p'')
     < nest_lookup (locals (snd nest_1_sol (Inl (FunctionEntry (STR ''g''), [Statement 2])))) (STR ''p'')"
  "nest_lookup (locals (snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 6])))) (STR ''p'')
     < nest_lookup (locals (snd nest_1_sol (Inl (FunctionEntry (STR ''g''), [Statement 2])))) (STR ''p'')"
  "nest_lookup (locals (snd nest_2_sol (Inl (Statement 6, [])))) (STR ''x'')
     < nest_lookup (locals (snd nest_1_sol (Inl (Statement 6, [])))) (STR ''x'')"
  "nest_lookup (locals (snd nest_2_sol (Inl (Statement 7, [])))) (STR ''y'')
     < nest_lookup (locals (snd nest_1_sol (Inl (Statement 7, [])))) (STR ''y'')"
  by (simp_all add: nest_1_g_entry_merged nest_1_x_after_first_return nest_1_y_after_second_return
                    nest_2_g_entry_first nest_2_g_entry_second nest_2_x_after_first_return
                    nest_2_y_after_second_return less_ivl_def less_eq_ivl_def)


section \<open>Call-string-context-expanded analysis graph\<close>

definition nest_2_graph_config ::
  "(cfg_node list, call_string_gk,
     (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state, ivl exec_dg_st lifted)
     analysis_graph_config" where
  "nest_2_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>u ctx action d. Some (cs_route 2 u ctx d action)),
      context_key = String.implode o
        (\<lambda>ctx. ''['' @ join_source '', '' (map string_of_cfg_node ctx) @ '']''),
      show_context = (\<lambda>ctx. ''['' @ join_source '', '' (map string_of_cfg_node ctx) @ '']''),
      locals_for_pp = (\<lambda>p.
        let sc = compiled_procedure_scope nest_gs nest_pi nest_procs
          nest_cfg p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope nest_gs nest_pi nest_procs
          nest_cfg p)),
      globals_to_show = [],
      show_local = (\<lambda>p ctx vars d. map (\<lambda>x.
        String.explode x @ ''='' @ string_of_ivl (nest_lookup d x)) vars),
      format_return = (\<lambda>p ctx ret d.
        if nest_lookup d ret = ivl_top then []
        else [''ret='' @ string_of_ivl (nest_lookup d ret)]),
      show_global = (\<lambda>k vars s. [''(none)'']),
      show_global_key = (\<lambda>k. case k of Global \<Rightarrow> ''Global'' | Seed p ctx \<Rightarrow> ''Seed''),
      is_shared_global = (\<lambda>k. case k of Global \<Rightarrow> True | Seed _ _ \<Rightarrow> False),
      show_internal_globals = False,
      owner_of = String.explode o compiled_owner_of nest_pi nest_procs,
      cluster_label = (\<lambda>owner ctx.
        if owner = ''main'' \<and> ctx = [] then ''main / root context''
        else owner @ '' / call string='' @ ''['' @ join_source '', '' (map string_of_cfg_node ctx) @ '']''),
      source_text = Some (pretty_string_of_program nest_pi nest_procs nest_main []),
      node_annotation = (\<lambda>_ _. None)
    \<rparr>"

definition nest_2_contexts_for_pp :: "pp \<Rightarrow> cfg_node list list" where
  "nest_2_contexts_for_pp p =
    (let owner = compiled_owner_of nest_pi nest_procs p
     in if owner = (STR ''main'') then [[]]
        else if owner = (STR ''f'') then [[Statement 5], [Statement 6]]
        else [[Statement 2, Statement 5], [Statement 2, Statement 6]])"

definition nest_2_local_graph_domain :: "(pp \<times> cfg_node list + call_string_gk) list" where
  "nest_2_local_graph_domain =
    contextual_graph_domain nest_cfg nest_2_contexts_for_pp"

definition nest_2_seed_keys :: "call_string_gk list" where
  "nest_2_seed_keys =
     map (\<lambda>ctx. Seed (FunctionEntry (STR ''f'')) ctx) [[Statement 5], [Statement 6]]
     @ map (\<lambda>ctx. Seed (FunctionEntry (STR ''g'')) ctx) [[Statement 2, Statement 5], [Statement 2, Statement 6]]"

definition nest_2_graph_domain :: "(pp \<times> cfg_node list + call_string_gk) list" where
  "nest_2_graph_domain =
    nest_2_local_graph_domain @ map Inr nest_2_seed_keys"

definition nest_2_graph :: "(cfg_node list, call_string_gk) analysis_graph" where
  "nest_2_graph =
    build_analysis_graph nest_2_graph_config nest_cfg nest_2_graph_domain
      (snd nest_2_sol)"

definition nest_2_dot :: String.literal where
  "nest_2_dot =
    String.implode
      (analysis_graph_to_dot nest_2_graph_config nest_cfg (snd nest_2_sol)
        nest_2_graph)"

lemma nest_2_graph_wf: "analysis_graph_wf nest_2_graph"
  unfolding nest_2_graph_def nest_cfg_def
  by (rule build_analysis_graph_wf
        [OF calls_source_unique_compile_prog compile_prog_finite[THEN conjunct2]])

lemma nest_2_graph_domain_is_covered:
  "list_all (\<lambda>x. case x of Inl pc \<Rightarrow> pc \<in> fst nest_2_sol | Inr _ \<Rightarrow> True)
    nest_2_graph_domain" by eval

lemma nest_2_dot_nonempty: "String.explode nest_2_dot \<noteq> []" by eval


end


