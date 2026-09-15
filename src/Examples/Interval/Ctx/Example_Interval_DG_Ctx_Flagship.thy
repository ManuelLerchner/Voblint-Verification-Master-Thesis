theory Example_Interval_DG_Ctx_Flagship
  imports
    Example_Interval_DG_IP_Flagship
    "Voblint_Analysis_Interval.Interval_Analyses"
begin

section \<open>Context-sensitive interval analysis of \<open>twice\<close> (executable)\<close>

text \<open>
  The production entry-state analysis
  (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Analyses\<close>) run on
  \<^const>\<open>twice_program\<close>.  Each call to \<open>twice\<close> receives the abstract entry value
  of formal \<open>p\<close> as its context:

  \<^item> \<open>twice(3)\<close> uses context \<open>[3,3]\<close> and computes \<open>#ret = [6,6]\<close> and \<open>x = [6,6]\<close>;
  \<^item> \<open>twice(10)\<close> uses context \<open>[10,10]\<close> and computes \<open>#ret = [20,20]\<close> and \<open>y = [20,20]\<close>.

  The two repeated calls stay separate, whereas the monovariant baseline of
  \<^theory>\<open>Voblint_Examples_Interval.Example_Interval_DG_IP_Flagship\<close> forces one shared entry
  state and reports \<open>p = [3,10]\<close>, \<open>#ret = [6,20]\<close>, and \<open>x = y = [6,20]\<close>.  This
  entry-value key is finite for the two constant call sites.  A general interval
  analysis needs a finite canonical context representation because arbitrary interval
  states may grow under recursion and widening.

  Nothing solver-shaped is owned here: the equation system, its routing hook, the
  solver-global key type \<^type>\<open>routed_gk\<close>, and the solved projection all come from the
  production analysis.  The local unknown carries the whole abstract state on the
  lifted carrier \<^typ>\<open>ivl exec_dg_st lifted\<close>, so a global is read where a local is
  and there is no separate solver-global slot holding program state.
\<close>

subsection \<open>The executable bottom predicate\<close>

text \<open>The equation system reads the program's own declared globals for its bottom
  test. At a concrete program it is \<^const>\<open>resolved_st_q_is_bot_for\<close> on those
  globals, which is exact for \<^const>\<open>is_empty_state\<close>.\<close>

definition twice_empty_pred :: "ivl resolved_st_q \<Rightarrow> bool" where
  "twice_empty_pred = resolved_st_q_is_bot_for (declared_global_vars twice_program)"

lemma twice_exact: "twice_empty_pred s = is_empty_state (fun_of_resolved_st_q_for twice_gs s)"
  unfolding twice_empty_pred_def by (rule resolved_st_q_is_bot_for_iff) simp

text \<open>Reading one variable off a lifted whole-state local unknown: an unreachable
  point (\<^const>\<open>Bot\<close>) reads \<open>bot\<close> at every variable.\<close>
abbreviation twice_ctx_lookup :: "ivl exec_dg_st lifted \<Rightarrow> vname \<Rightarrow> ivl" where
  "twice_ctx_lookup d x \<equiv>
     (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> lookup_resolved_st_q d0 (location_of twice_gs x))"

subsection \<open>The routed equation system and its solution\<close>

text \<open>Every value below is Interval's entry-state registration \<open>interval_es_rule\<close> at
  \<^const>\<open>Globals_Warrow\<close>. The main context is \<open>[]\<close> (\<open>main\<close> is the root
  activation, no formal binds it).\<close>

definition twice_ctx_sol ::
  "(pp \<times> ivl list) set
     \<times> (pp \<times> ivl list + (unit, ivl list) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "twice_ctx_sol = interval_es_rule.solution Globals_Warrow twice_gs twice_program"

lemma twice_ctx_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Warrow
     (interval_es_rule.equations twice_gs twice_program)
     (interval_es_rule.root_query twice_program) \<noteq> None"
  unfolding interval_es_rule.root_query_def by eval

lemma twice_ctx_terminates:
  "interval_es_rule.terminates Globals_Warrow twice_gs twice_program"
  by (rule interval_es_rule.terminates_of_solve_c[OF twice_ctx_terminates_c])

subsection \<open>The two calling contexts are distinct\<close>

text \<open>The routed callee context is \<^const>\<open>routed_dg_pipeline.ctx_succ\<close>, whose type
  omits the domain, so evaluation inlines its body rather than looking for a code
  equation of its own.\<close>

declare routed_dg_pipeline.ctx_succ_def [code_unfold]

definition ctx_call1 :: "ivl list" where
  "ctx_call1 = interval_es_rule.ctx_succ Globals_Warrow twice_gs twice_program
                 (Statement 2) [] (CallEdge (Some (STR ''x'')) [(STR ''p'')] [VIMP_Syntax.N 3])
                 (STR ''twice'')"

definition ctx_call2 :: "ivl list" where
  "ctx_call2 = interval_es_rule.ctx_succ Globals_Warrow twice_gs twice_program
                 (Statement 3) [] (CallEdge (Some (STR ''y'')) [(STR ''p'')] [VIMP_Syntax.N 10])
                 (STR ''twice'')"

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
  heterogeneous seed channel (\<^const>\<open>routed_call_tree\<close> / \<^const>\<open>routed_entry_seed_tree\<close>)
  carries that store in the seed unknown's \<^const>\<open>locals\<close> half, the same carrier the
  callee entry reads it back on.\<close>
lemma seed_call1:
  "twice_ctx_lookup
     (locals (snd twice_ctx_sol
       (Inr (Activation_Seed (FunctionEntry (STR ''twice'')) ctx_call1))))
     (STR ''p'')
     = Ivl (Fin 3) (Fin 3)"
  unfolding twice_ctx_sol_def twice_empty_pred_def ctx_call1_def by eval

lemma seed_call2:
  "twice_ctx_lookup
     (locals (snd twice_ctx_sol
       (Inr (Activation_Seed (FunctionEntry (STR ''twice'')) ctx_call2))))
     (STR ''p'')
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

end
