theory Example_Interval_DG_Ctx_Flagship
  imports
    Example_Interval_DG_IP_Flagship
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_Core.Routed_Context"
begin

section \<open>Context-sensitive interval analysis of \<open>twice\<close> (executable)\<close>

text \<open>
  The generalized D/G generator is instantiated with routed context hooks.  Each call
  to \<open>twice\<close> receives the abstract entry value of formal \<open>p\<close> as its context:

  \<^item> \<open>twice(3)\<close> uses context \<open>[3,3]\<close> and computes \<open>#ret = [6,6]\<close> and \<open>x = [6,6]\<close>;
  \<^item> \<open>twice(10)\<close> uses context \<open>[10,10]\<close> and computes \<open>#ret = [20,20]\<close> and \<open>y = [20,20]\<close>.

  The two repeated calls remain separate, whereas unit context joins their formal and
  return values.  This entry-value key is finite for the two constant call sites.  A
  general interval analysis needs a finite canonical context representation because
  arbitrary interval states may grow under recursion and widening.
\<close>

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>

text \<open>The global-key type separates shared analysis globals from
  context-sensitive callee-entry seeds. \<open>Global\<close> denotes the single
  flow-insensitive slot; \<open>Seed\<close> keys an entry seed by program point and context.
  Distinct constructors prevent the two roles from sharing a solver unknown.\<close>

datatype gk = Global | Seed (seed_pp: pp) (seed_ivl: "ivl")

subsection \<open>The storage classifier\<close>

text \<open>Storage here is decided from \<open>twice_program\<close>'s own
  declarations (\<^const>\<open>declared_global\<close>) rather than a name-based naming
  convention. \<open>twice_program\<close> declares no globals, so \<^term>\<open>twice_gs\<close> classifies
  every variable this chain touches as local --- unlike a G-prefix convention, which
  would still treat any \<open>G\<close>-prefixed name as global by naming convention alone.\<close>

abbreviation twice_gs :: "vname \<Rightarrow> bool" where
  "twice_gs \<equiv> declared_global twice_program"

abbreviation twice_lookup_exec_dg_st :: "('a::bot) exec_dg_st \<Rightarrow> vname \<Rightarrow> 'a" where
  "twice_lookup_exec_dg_st s x \<equiv> lookup_resolved_st_q s (location_of twice_gs x)"

subsection \<open>The routed context hooks\<close>

definition Spoly :: "(ivl exec_dg_st, ivl exec_dg_st) dg_spec" where
  "Spoly = unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)"

text \<open>Outgoing call edges of a node, as callee entry / call action / continuation.  The
  procedure-aware \<^const>\<open>calls\<close> relation records all three on the edge, so no separate
  matching relation is consulted.\<close>
definition call_successor_list :: "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> call_action \<times> pp) list" where
  "call_successor_list g v =
     map (\<lambda>(c, ca, ce, k). (ce, ca, k)) (filter (\<lambda>(c, ca, ce, k). c = v) (cfg_calls_list g))"

text \<open>A frame entry is a \<^const>\<open>FunctionEntry\<close> node: the seed slot lives there.\<close>
fun is_function_entry :: "cfg_node \<Rightarrow> bool" where
  "is_function_entry (FunctionEntry _) = True"
| "is_function_entry _ = False"

text \<open>The callee-entry local store produced by a \<^const>\<open>CallEdge\<close> from a caller-local
  state (globals defaulted to \<open>bot\<close>: \<open>twice\<close> has none).\<close>
definition entered_ivl :: "ivl exec_dg_st \<Rightarrow> call_action \<Rightarrow> ivl exec_dg_st" where
  "entered_ivl d ca =
     (case ca of CallEdge dst fs as \<Rightarrow> snd (dgs_enter Spoly fs as d bot))"

text \<open>The routing function: the context a call selects is the entered value of the
  formal \<open>(STR ''p'')\<close>.\<close>
definition route_ivl :: "ivl exec_dg_st \<Rightarrow> call_action \<Rightarrow> ivl" where
  "route_ivl d ca = twice_lookup_exec_dg_st (entered_ivl d ca) (STR ''p'')"

text \<open>The generator's routing hook is generic over call site and caller context; this
  instance needs neither, using only the entered store.\<close>
definition route_ivl_gen :: "pp \<Rightarrow> ivl \<Rightarrow> ivl exec_dg_st \<Rightarrow> call_action \<Rightarrow> ivl" where
  "route_ivl_gen u ctx d ca = route_ivl d ca"

subsection \<open>The routed equation system and its solution\<close>

definition twice_ctx_eqs ::
  "(pp \<times> ivl, gk, (ivl exec_dg_st, ivl exec_dg_st) dg_state) eqsT" where
  "twice_ctx_eqs =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_ivl_gen
       (routed_cmb Spoly Global) (routed_extra twice_cfg Spoly Seed Global)
       twice_cfg Spoly bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st)"

text \<open>The main context is \<open>bot\<close> (\<open>main\<close> is the root activation, no formal binds it).\<close>
definition twice_ctx_sol ::
  "(pp \<times> ivl) set \<times> (pp \<times> ivl + gk \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)" where
  "twice_ctx_sol = TD_side_warrowing_apinis_Interp_solve twice_ctx_eqs (cfg_exit twice_cfg, bot)"

lemma twice_ctx_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c twice_ctx_eqs (cfg_exit twice_cfg, bot) \<noteq> None"
  by eval

subsection \<open>The two calling contexts are distinct\<close>

definition ctx_call1 :: ivl where
  "ctx_call1 = route_ivl (locals (snd twice_ctx_sol (Inl (Statement 2, bot))))
                 (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3])"

definition ctx_call2 :: ivl where
  "ctx_call2 = route_ivl (locals (snd twice_ctx_sol (Inl (Statement 3, bot))))
                 (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10])"

lemma contexts_distinct: "ctx_call1 \<noteq> ctx_call2"
  by eval

lemma ctx_call1_val: "ctx_call1 = Ivl (Fin 3) (Fin 3)" by eval
lemma ctx_call2_val: "ctx_call2 = Ivl (Fin 10) (Fin 10)" by eval

subsection \<open>Per-context exact results\<close>

text \<open>Callee entry parameter, per context.\<close>
lemma call1_p_at_entry:
  "twice_lookup_exec_dg_st (locals (snd twice_ctx_sol (Inl (FunctionEntry (STR ''twice''), ctx_call1)))) (STR ''p'')
     = Ivl (Fin 3) (Fin 3)"
  by eval

lemma call2_p_at_entry:
  "twice_lookup_exec_dg_st (locals (snd twice_ctx_sol (Inl (FunctionEntry (STR ''twice''), ctx_call2)))) (STR ''p'')
     = Ivl (Fin 10) (Fin 10)"
  by eval

text \<open>Callee result return channel, per context --- \<^emph>\<open>not\<close> merged.\<close>
lemma call1_ret_at_exit:
  "twice_lookup_exec_dg_st (locals (snd twice_ctx_sol (Inl (FunctionResult (STR ''twice''), ctx_call1)))) (STR ''#ret'')
     = Ivl (Fin 6) (Fin 6)"
  by eval

lemma call2_ret_at_exit:
  "twice_lookup_exec_dg_st (locals (snd twice_ctx_sol (Inl (FunctionResult (STR ''twice''), ctx_call2)))) (STR ''#ret'')
     = Ivl (Fin 20) (Fin 20)"
  by eval

text \<open>Caller destinations after each return.\<close>
lemma x_computed:
  "twice_lookup_exec_dg_st (locals (snd twice_ctx_sol (Inl (Statement 3, bot)))) (STR ''x'') = Ivl (Fin 6) (Fin 6)"
  by eval

lemma y_computed:
  "twice_lookup_exec_dg_st (locals (snd twice_ctx_sol (Inl (Statement 4, bot)))) (STR ''y'') = Ivl (Fin 20) (Fin 20)"
  by eval

subsection \<open>Seed slots and coverage\<close>

text \<open>Each call publishes the entered store into its own context's seed slot.\<close>
lemma seed_call1:
  "twice_lookup_exec_dg_st (globs (snd twice_ctx_sol (Inr (Seed (FunctionEntry (STR ''twice'')) ctx_call1)))) (STR ''p'')
     = Ivl (Fin 3) (Fin 3)"
  by eval

lemma seed_call2:
  "twice_lookup_exec_dg_st (globs (snd twice_ctx_sol (Inr (Seed (FunctionEntry (STR ''twice'')) ctx_call2)))) (STR ''p'')
     = Ivl (Fin 10) (Fin 10)"
  by eval

text \<open>The callee entry is materialized once per routed context and never under the
  main context: the two calls are analyzed separately.\<close>
lemma callee_covered_call1: "(FunctionEntry (STR ''twice''), ctx_call1) \<in> fst twice_ctx_sol" by eval
lemma callee_covered_call2: "(FunctionEntry (STR ''twice''), ctx_call2) \<in> fst twice_ctx_sol" by eval
lemma callee_not_under_main: "(FunctionEntry (STR ''twice''), bot) \<notin> fst twice_ctx_sol" by eval

subsection \<open>Context-expanded analysis graph\<close>



definition twice_ctx_graph_config ::
  "(ivl, gk, (ivl exec_dg_st, ivl exec_dg_st) dg_state, ivl exec_dg_st) analysis_graph_config" where
  "twice_ctx_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>_ ctx action d. route_ivl d action),
      show_context = string_of_ivl,
      locals_for_pp = (\<lambda>p.
        let sc = compiled_procedure_scope twice_gs twice_pi twice_procs (STR ''main'') twice_main
          twice_cfg p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope twice_gs twice_pi twice_procs (STR ''main'') twice_main
          twice_cfg p)),
      globals_to_show = [],
      show_local = (\<lambda>p ctx vars d. map (\<lambda>x.
        String.explode x @ ''='' @ string_of_ivl (twice_lookup_exec_dg_st d x)) vars),
      format_return = (\<lambda>p ctx ret d.
        if twice_lookup_exec_dg_st d ret = ivl_top then []
        else [''ret='' @ string_of_ivl (twice_lookup_exec_dg_st d ret)]),
      show_global = (\<lambda>k vars s. [''(none)'']),
      show_global_key = (\<lambda>k. case k of Global \<Rightarrow> ''Global'' | Seed p ctx \<Rightarrow> ''Seed''),
      is_shared_global = (\<lambda>k. case k of Global \<Rightarrow> True | Seed _ _ \<Rightarrow> False),
      show_internal_globals = False,
      owner_of = String.explode o compiled_owner_of twice_pi twice_procs (STR ''main'') twice_main,
      cluster_label = (\<lambda>owner ctx.
        if owner = ''main'' \<and> ctx = bot then ''main / root context''
        else owner @ '' / context='' @ string_of_ivl ctx),
      source_text = Some (pretty_string_of_program twice_pi twice_procs twice_main),
      node_annotation = (\<lambda>_. None)
    \<rparr>"

definition twice_ctx_contexts_for_pp :: "pp \<Rightarrow> ivl list" where
  "twice_ctx_contexts_for_pp p =
    (if compiled_owner_of twice_pi twice_procs (STR ''main'') twice_main p = (STR ''main'')
     then [bot] else [ctx_call1, ctx_call2])"

definition twice_ctx_local_graph_domain :: "(pp \<times> ivl + gk) list" where
  "twice_ctx_local_graph_domain =
    contextual_graph_domain twice_cfg twice_ctx_contexts_for_pp"

definition twice_ctx_seed_keys :: "gk list" where
  "twice_ctx_seed_keys =
     map (\<lambda>ctx. Seed (FunctionEntry (STR ''twice'')) ctx) [ctx_call1, ctx_call2]"

definition twice_ctx_graph_domain :: "(pp \<times> ivl + gk) list" where
  "twice_ctx_graph_domain =
    twice_ctx_local_graph_domain @ map Inr twice_ctx_seed_keys"

definition twice_ctx_graph :: "(ivl, gk) analysis_graph" where
  "twice_ctx_graph =
    build_analysis_graph twice_ctx_graph_config twice_cfg twice_ctx_graph_domain
      (snd twice_ctx_sol)"

definition twice_ctx_dot :: String.literal where
  "twice_ctx_dot =
    String.implode
      (analysis_graph_to_dot twice_ctx_graph_config twice_cfg (snd twice_ctx_sol)
        twice_ctx_graph)"

lemma twice_ctx_graph_wf: "analysis_graph_wf twice_ctx_graph" by eval

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
  "LocalNode (FunctionEntry (STR ''twice'')) bot \<notin> set (analysis_graph_nodes twice_ctx_graph)"
  by eval

lemma twice_ctx_graph_omits_empty_globals:
  "filter (\<lambda>n. case n of GlobalNode _ \<Rightarrow> True | _ \<Rightarrow> False)
    (analysis_graph_nodes twice_ctx_graph) = []" by eval

lemma twice_ctx_graph_enter_edges:
  "filter (\<lambda>e. case e of (_, EnterEdge _ _, _) \<Rightarrow> True | _ \<Rightarrow> False)
    (analysis_graph_edges twice_ctx_graph) =
    [(LocalNode (Statement 2) bot,
      EnterEdge ''twice'' (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3]),
      LocalNode (FunctionEntry (STR ''twice'')) ctx_call1),
     (LocalNode (Statement 3) bot,
      EnterEdge ''twice'' (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10]),
      LocalNode (FunctionEntry (STR ''twice'')) ctx_call2)]" by eval

lemma twice_ctx_graph_combine_edges:
  "filter (\<lambda>e. case e of (_, CombineEdge _ _ _, _) \<Rightarrow> True | _ \<Rightarrow> False)
    (analysis_graph_edges twice_ctx_graph) =
    [(LocalNode (FunctionResult (STR ''twice'')) ctx_call1,
      CombineEdge (Statement 2) (Some (STR ''x'')) (Some (STR ''#ret'')), LocalNode (Statement 3) bot),
     (LocalNode (FunctionResult (STR ''twice'')) ctx_call2,
      CombineEdge (Statement 3) (Some (STR ''y'')) (Some (STR ''#ret'')), LocalNode (Statement 4) bot)]"
  by eval

lemma twice_ctx_dot_has_context_clusters:
  "String.explode twice_ctx_dot \<noteq> []" by eval

ML_val \<open>writeln (@{code twice_ctx_dot})\<close>

end


