theory Example_Interval_DG_EntryState_Ctx
  imports
    Example_Interval_DG_EntryState_Base
begin

section \<open>Context-sensitive interval analysis of \<open>rc_program\<close> (executable)\<close>

text \<open>
  The production entry-state analysis is run on \<open>rc_program\<close>.  The one call to \<open>p\<close>
  receives the abstract entry value of formal \<open>a\<close> as its context: since \<open>x\<close> was just
  assigned from \<open>__voblint_nondet_int()\<close>, its interval at the call site is \<open>Top\<close>, so the
  routed context is \<open>Top\<close> itself --- one context, not a family of contexts covering
  the infinitely many concrete arguments \<open>__voblint_nondet_int()\<close> can produce.

  The local unknown carries the whole abstract state, so the routed context is read
  straight off \<^const>\<open>locals\<close>; there is no separate solver-global slot to reassemble
  a program state from.
\<close>

subsection \<open>The executable bottom predicate\<close>

text \<open>The equation system reads the program's own declared globals for its bottom
  test. At a concrete program it is \<^const>\<open>resolved_st_q_is_bot_for\<close> on those
  globals, which is exact for \<^const>\<open>is_empty_state\<close>.\<close>

definition rc_empty_pred :: "ivl resolved_st_q \<Rightarrow> bool" where
  "rc_empty_pred = resolved_st_q_is_bot_for (declared_global_vars rc_program)"

lemma rc_exact: "rc_empty_pred s = is_empty_state (fun_of_resolved_st_q_for rc_gs s)"
  unfolding rc_empty_pred_def by (rule resolved_st_q_is_bot_for_iff) simp

subsection \<open>The routed equation system and its solution\<close>

text \<open>Every value below is Interval's entry-state registration \<open>interval_es_rule\<close> at
  \<^const>\<open>Globals_Warrow\<close>. The main context is \<open>[]\<close> (\<open>main\<close> is the root
  activation, no formal binds it).\<close>

definition rc_ctx_sol ::
  "(pp \<times> ivl list) set
    \<times> (pp \<times> ivl list + (unit, ivl list) routed_gk
      \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "rc_ctx_sol = interval_es_rule.solution Globals_Warrow rc_gs rc_program"

lemma rc_ctx_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Warrow
     (interval_es_rule.equations rc_gs rc_program)
     (interval_es_rule.root_query rc_program) \<noteq> None"
  unfolding interval_es_rule.root_query_def by eval

lemma rc_ctx_terminates:
  "interval_es_rule.terminates Globals_Warrow rc_gs rc_program"
  by (rule interval_es_rule.terminates_of_solve_c[OF rc_ctx_terminates_c])

subsection \<open>The routed context is exactly \<open>Top\<close>\<close>

text \<open>The routed callee context is \<^const>\<open>routed_dg_pipeline.ctx_succ\<close>, whose type
  omits the domain, so evaluation inlines its body rather than looking for a code
  equation of its own.\<close>

declare routed_dg_pipeline.ctx_succ_def [code_unfold]

definition ctx_call :: "ivl list" where
  "ctx_call = interval_es_rule.ctx_succ Globals_Warrow rc_gs rc_program
                (Statement 3) [] (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')])
                (STR ''p'')"

lemma ctx_call_val: "ctx_call = [ivl_top]"
  unfolding ctx_call_def rc_ctx_sol_def by eval

text \<open>The callee entry is materialized once, under the wide context, and never under
  the root context.\<close>
lemma callee_covered_call: "(FunctionEntry (STR ''p''), ctx_call) \<in> fst rc_ctx_sol"
  unfolding ctx_call_def rc_ctx_sol_def rc_empty_pred_def by eval

lemma callee_not_under_main: "(FunctionEntry (STR ''p''), []) \<notin> fst rc_ctx_sol"
  unfolding rc_ctx_sol_def rc_empty_pred_def by eval

end

