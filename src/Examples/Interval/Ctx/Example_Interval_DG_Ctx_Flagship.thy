theory Example_Interval_DG_Ctx_Flagship
  imports
    Example_Interval_DG_IP_Flagship
    "Voblint_Analysis.Interval_Ctx_Entry_State_Sound"
    "Voblint_Analysis.Analysis_GraphViz"
begin

section \<open>Context-sensitive interval analysis of \<open>twice\<close> (executable)\<close>

text \<open>
  The production entry-state analysis
  (\<^theory>\<open>Voblint_Analysis.Interval_Ctx_Entry_State_Sound\<close>) run on
  \<^const>\<open>twice_program\<close>.  Each call to \<open>twice\<close> receives the abstract entry value
  of formal \<open>p\<close> as its context:

  \<^item> \<open>twice(3)\<close> uses context \<open>[3,3]\<close> and computes \<open>#ret = [6,6]\<close> and \<open>x = [6,6]\<close>;
  \<^item> \<open>twice(10)\<close> uses context \<open>[10,10]\<close> and computes \<open>#ret = [20,20]\<close> and \<open>y = [20,20]\<close>.

  The two repeated calls stay separate, whereas the monovariant baseline of
  \<^theory>\<open>Voblint_Examples.Example_Interval_DG_IP_Flagship\<close> forces one shared entry
  state and reports \<open>p = [3,10]\<close>, \<open>#ret = [6,20]\<close>, and \<open>x = y = [6,20]\<close>.  This
  entry-value key is finite for the two constant call sites.  A general interval
  analysis needs a finite canonical context representation because arbitrary interval
  states may grow under recursion and widening.

  Nothing solver-shaped is owned here: the equation system, its routing hook, the
  solver-global key type \<^type>\<open>gk\<close>, and the solved projection all come from the
  production analysis.  The local unknown carries the whole abstract state on the
  lifted carrier \<^typ>\<open>ivl exec_dg_st lifted\<close>, so a global is read where a local is
  and there is no separate solver-global slot holding program state.
\<close>

subsection \<open>The executable bottom predicate\<close>

text \<open>\<^const>\<open>entry_state_sol\<close> takes \<open>empty_pred\<close> as an explicit parameter.  At a
  concrete program it is \<^const>\<open>resolved_st_q_is_bot_for\<close> on that program's own
  declared globals, which is exact for \<^const>\<open>is_empty_state\<close>.\<close>

definition twice_empty_pred :: "ivl resolved_st_q \<Rightarrow> bool" where
  "twice_empty_pred = resolved_st_q_is_bot_for (declared_global_vars twice_program)"

lemma twice_exact: "twice_empty_pred s = is_empty_state (fun_of_resolved_st_q_for twice_gs s)"
  unfolding twice_empty_pred_def by (rule resolved_st_q_is_bot_for_iff) simp

text \<open>Reading one variable off a lifted whole-state local unknown: an unreachable
  point (\<^const>\<open>Bot\<close>) reads \<open>bot\<close> at every variable.\<close>
abbreviation twice_ctx_lookup :: "ivl exec_dg_st lifted \<Rightarrow> vname \<Rightarrow> ivl" where
  "twice_ctx_lookup d x \<equiv> (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> twice_lookup d0 x)"

subsection \<open>The routed equation system and its solution\<close>

text \<open>The main context is \<open>[]\<close> (\<open>main\<close> is the root activation, no formal binds it).\<close>

definition twice_ctx_sol ::
  "(pp \<times> ivl list) set
     \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "twice_ctx_sol = entry_state_sol twice_gs twice_empty_pred twice_pi twice_procs"

lemma twice_ctx_terminates_c:
  "TD_side_warrowing_apinis_Interp_solve_c
     (entry_state_eqs twice_gs twice_empty_pred twice_pi twice_procs)
     (cfg_exit twice_cfg, []) \<noteq> None"
  unfolding twice_cfg_def by eval

lemma twice_ctx_terminates:
  "entry_state_terminates twice_gs twice_empty_pred twice_pi twice_procs"
  using twice_ctx_terminates_c[unfolded twice_cfg_def]
  by (rule entry_state_terminates_via_solve_c)

subsection \<open>The two calling contexts are distinct\<close>

definition ctx_call1 :: "ivl list" where
  "ctx_call1 = entry_state_route twice_gs twice_empty_pred
                 (entry_state_entered twice_gs twice_empty_pred
                    (locals (snd twice_ctx_sol (Inl (Statement 2, []))))
                    (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3]))
                 (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3])"

definition ctx_call2 :: "ivl list" where
  "ctx_call2 = entry_state_route twice_gs twice_empty_pred
                 (entry_state_entered twice_gs twice_empty_pred
                    (locals (snd twice_ctx_sol (Inl (Statement 3, []))))
                    (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10]))
                 (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10])"

lemma ctx_call1_val: "ctx_call1 = [Ivl (Fin 3) (Fin 3)]"
  unfolding ctx_call1_def twice_ctx_sol_def twice_empty_pred_def by eval

lemma ctx_call2_val: "ctx_call2 = [Ivl (Fin 10) (Fin 10)]"
  unfolding ctx_call2_def twice_ctx_sol_def twice_empty_pred_def by eval

lemma contexts_distinct: "ctx_call1 \<noteq> ctx_call2"
  by (simp add: ctx_call1_val ctx_call2_val)

subsection \<open>Per-context exact results\<close>

text \<open>Callee entry parameter, per context --- against the monovariant \<open>p = [3,10]\<close>.\<close>
lemma call1_p_at_entry:
  "twice_ctx_lookup (locals (snd twice_ctx_sol (Inl (FunctionEntry (STR ''twice''), ctx_call1)))) (STR ''p'')
     = Ivl (Fin 3) (Fin 3)"
  unfolding twice_ctx_sol_def twice_empty_pred_def ctx_call1_def by eval

lemma call2_p_at_entry:
  "twice_ctx_lookup (locals (snd twice_ctx_sol (Inl (FunctionEntry (STR ''twice''), ctx_call2)))) (STR ''p'')
     = Ivl (Fin 10) (Fin 10)"
  unfolding twice_ctx_sol_def twice_empty_pred_def ctx_call2_def by eval

text \<open>Callee result return channel, per context --- \<^emph>\<open>not\<close> merged into the monovariant
  \<open>#ret = [6,20]\<close>.\<close>
lemma call1_ret_at_exit:
  "twice_ctx_lookup (locals (snd twice_ctx_sol (Inl (FunctionResult (STR ''twice''), ctx_call1)))) (STR ''#ret'')
     = Ivl (Fin 6) (Fin 6)"
  unfolding twice_ctx_sol_def twice_empty_pred_def ctx_call1_def by eval

lemma call2_ret_at_exit:
  "twice_ctx_lookup (locals (snd twice_ctx_sol (Inl (FunctionResult (STR ''twice''), ctx_call2)))) (STR ''#ret'')
     = Ivl (Fin 20) (Fin 20)"
  unfolding twice_ctx_sol_def twice_empty_pred_def ctx_call2_def by eval

text \<open>Caller destinations after each return, where the monovariant baseline reports
  \<open>x = y = [6,20]\<close>.\<close>
lemma x_computed:
  "twice_ctx_lookup (locals (snd twice_ctx_sol (Inl (Statement 3, [])))) (STR ''x'') = Ivl (Fin 6) (Fin 6)"
  unfolding twice_ctx_sol_def twice_empty_pred_def by eval

lemma y_computed:
  "twice_ctx_lookup (locals (snd twice_ctx_sol (Inl (Statement 4, [])))) (STR ''y'') = Ivl (Fin 20) (Fin 20)"
  unfolding twice_ctx_sol_def twice_empty_pred_def by eval

subsection \<open>Seed slots and coverage\<close>

text \<open>Each call publishes the entered store into its own context's seed slot.  The
  heterogeneous seed channel (\<^const>\<open>routed_cmb_g_contribution\<close> / \<^const>\<open>routed_extra_g\<close>)
  carries that store in the seed unknown's \<^const>\<open>locals\<close> half, the same carrier the
  callee entry reads it back on.\<close>
lemma seed_call1:
  "twice_ctx_lookup (locals (snd twice_ctx_sol (Inr (Seed (FunctionEntry (STR ''twice'')) ctx_call1)))) (STR ''p'')
     = Ivl (Fin 3) (Fin 3)"
  unfolding twice_ctx_sol_def twice_empty_pred_def ctx_call1_def by eval

lemma seed_call2:
  "twice_ctx_lookup (locals (snd twice_ctx_sol (Inr (Seed (FunctionEntry (STR ''twice'')) ctx_call2)))) (STR ''p'')
     = Ivl (Fin 10) (Fin 10)"
  unfolding twice_ctx_sol_def twice_empty_pred_def ctx_call2_def by eval

text \<open>The callee entry is materialized once per routed context and never under the
  main context: the two calls are analyzed separately.\<close>
lemma callee_covered_call1: "(FunctionEntry (STR ''twice''), ctx_call1) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_empty_pred_def ctx_call1_def by eval

lemma callee_covered_call2: "(FunctionEntry (STR ''twice''), ctx_call2) \<in> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_empty_pred_def ctx_call2_def by eval

lemma callee_not_under_main: "(FunctionEntry (STR ''twice''), []) \<notin> fst twice_ctx_sol"
  unfolding twice_ctx_sol_def twice_empty_pred_def by eval

subsection \<open>Context-expanded analysis graph\<close>

text \<open>The exporter is retyped for the lifted whole-state carrier the production
  analysis solves over: every reader below takes an \<^typ>\<open>ivl exec_dg_st lifted\<close> local
  value, and the routing hook is \<^const>\<open>entry_state_route\<close> itself.\<close>

definition twice_ctx_graph_config ::
  "(ivl list, gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state, ivl exec_dg_st lifted)
     analysis_graph_config" where
  "twice_ctx_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>_ ctx action d. Some (entry_state_route twice_gs twice_empty_pred
                 (entry_state_entered twice_gs twice_empty_pred d action) action)),
      context_key = String.implode o (\<lambda>ctx. concat (map (\<lambda>x. string_of_ivl x @ '' '') ctx)),
      show_context = (\<lambda>ctx. concat (map (\<lambda>x. string_of_ivl x @ '' '') ctx)),
      locals_for_pp = (\<lambda>p.
        let sc = compiled_procedure_scope twice_gs twice_pi twice_procs
          twice_cfg p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope twice_gs twice_pi twice_procs
          twice_cfg p)),
      globals_to_show = [],
      show_local = (\<lambda>p ctx vars d. map (\<lambda>x.
        String.explode x @ ''='' @ string_of_ivl (twice_ctx_lookup d x)) vars),
      format_return = (\<lambda>p ctx ret d.
        if twice_ctx_lookup d ret = ivl_top then []
        else [''ret='' @ string_of_ivl (twice_ctx_lookup d ret)]),
      show_global = (\<lambda>k vars s. [''(none)'']),
      show_global_key = (\<lambda>k. case k of Global \<Rightarrow> ''Global'' | Seed p ctx \<Rightarrow> ''Seed''),
      is_shared_global = (\<lambda>k. case k of Global \<Rightarrow> True | Seed _ _ \<Rightarrow> False),
      show_internal_globals = False,
      owner_of = String.explode o compiled_owner_of twice_pi twice_procs,
      cluster_label = (\<lambda>owner ctx.
        if owner = ''main'' \<and> ctx = [] then ''main / root context''
        else owner @ '' / context='' @ concat (map (\<lambda>x. string_of_ivl x @ '' '') ctx)),
      source_text = Some (pretty_string_of_program twice_pi twice_procs twice_main []),
      node_annotation = (\<lambda>_ _. None)
    \<rparr>"

definition twice_ctx_contexts_for_pp :: "pp \<Rightarrow> ivl list list" where
  "twice_ctx_contexts_for_pp p =
    (if compiled_owner_of twice_pi twice_procs p = (STR ''main'')
     then [[]] else [ctx_call1, ctx_call2])"

definition twice_ctx_local_graph_domain :: "(pp \<times> ivl list + gk) list" where
  "twice_ctx_local_graph_domain =
    contextual_graph_domain twice_cfg twice_ctx_contexts_for_pp"

definition twice_ctx_seed_keys :: "gk list" where
  "twice_ctx_seed_keys =
     map (\<lambda>ctx. Seed (FunctionEntry (STR ''twice'')) ctx) [ctx_call1, ctx_call2]"

definition twice_ctx_graph_domain :: "(pp \<times> ivl list + gk) list" where
  "twice_ctx_graph_domain =
    twice_ctx_local_graph_domain @ map Inr twice_ctx_seed_keys"

definition twice_ctx_graph :: "(ivl list, gk) analysis_graph" where
  "twice_ctx_graph =
    build_analysis_graph twice_ctx_graph_config twice_cfg twice_ctx_graph_domain
      (snd twice_ctx_sol)"

definition twice_ctx_dot :: String.literal where
  "twice_ctx_dot =
    String.implode
      (analysis_graph_to_dot twice_ctx_graph_config twice_cfg (snd twice_ctx_sol)
        twice_ctx_graph)"

lemma twice_ctx_graph_wf: "analysis_graph_wf twice_ctx_graph"
  unfolding twice_ctx_graph_def twice_cfg_def
  by (rule build_analysis_graph_wf
        [OF calls_source_unique_compile_prog compile_prog_finite[THEN conjunct2]])

lemma twice_ctx_graph_domain_is_covered:
  "list_all (\<lambda>x. case x of Inl pc \<Rightarrow> pc \<in> fst twice_ctx_sol | Inr _ \<Rightarrow> True)
    twice_ctx_graph_domain" by eval

lemma twice_ctx_graph_seed_keys_follow_enters:
  "map (\<lambda>e. case e of (_, EnterEdge _ _, LocalNode p ctx) \<Rightarrow> Seed p ctx
                  | _ \<Rightarrow> Global)
     (filter (\<lambda>e. case e of (_, EnterEdge _ _, _) \<Rightarrow> True | _ \<Rightarrow> False)
       (analysis_graph_edges twice_ctx_graph)) = twice_ctx_seed_keys" by eval

lemma twice_ctx_graph_has_both_callees:
  "LocalNode (FunctionEntry (STR ''twice'')) ctx_call1 \<in> set (analysis_graph_nodes twice_ctx_graph) \<and>
   LocalNode (FunctionEntry (STR ''twice'')) ctx_call2 \<in> set (analysis_graph_nodes twice_ctx_graph)"
  by eval

lemma twice_ctx_graph_hides_uncovered_main_callee:
  "LocalNode (FunctionEntry (STR ''twice'')) [] \<notin> set (analysis_graph_nodes twice_ctx_graph)"
  by eval

lemma twice_ctx_graph_omits_empty_globals:
  "filter (\<lambda>n. case n of GlobalNode _ \<Rightarrow> True | _ \<Rightarrow> False)
    (analysis_graph_nodes twice_ctx_graph) = []" by eval

lemma twice_ctx_graph_enter_edges:
  "filter (\<lambda>e. case e of (_, EnterEdge _ _, _) \<Rightarrow> True | _ \<Rightarrow> False)
    (analysis_graph_edges twice_ctx_graph) =
    [(LocalNode (Statement 2) [],
      EnterEdge ''twice'' (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3]),
      LocalNode (FunctionEntry (STR ''twice'')) ctx_call1),
     (LocalNode (Statement 3) [],
      EnterEdge ''twice'' (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10]),
      LocalNode (FunctionEntry (STR ''twice'')) ctx_call2)]" by eval

lemma twice_ctx_graph_combine_edges:
  "filter (\<lambda>e. case e of (_, CombineEdge _ _ _, _) \<Rightarrow> True | _ \<Rightarrow> False)
    (analysis_graph_edges twice_ctx_graph) =
    [(LocalNode (FunctionResult (STR ''twice'')) ctx_call1,
      CombineEdge (Statement 2) (Some (STR ''x'')) (Some (STR ''#ret'')), LocalNode (Statement 3) []),
     (LocalNode (FunctionResult (STR ''twice'')) ctx_call2,
      CombineEdge (Statement 3) (Some (STR ''y'')) (Some (STR ''#ret'')), LocalNode (Statement 4) [])]"
  by eval

lemma twice_ctx_dot_has_context_clusters:
  "String.explode twice_ctx_dot \<noteq> []" by eval


end

