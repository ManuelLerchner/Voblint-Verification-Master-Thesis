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

text \<open>\<^const>\<open>entry_state_sol\<close> takes \<open>is_bot_pred\<close> as an explicit parameter.  At a
  concrete program it is \<^const>\<open>resolved_st_q_is_bot_for\<close> on that program's own
  declared globals, which is exact for \<^const>\<open>is_bot_state\<close>.\<close>

definition rc_is_bot_pred :: "ivl resolved_st_q \<Rightarrow> bool" where
  "rc_is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars rc_program)"

lemma rc_exact: "rc_is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for rc_gs s)"
  unfolding rc_is_bot_pred_def by (rule resolved_st_q_is_bot_for_iff) simp

subsection \<open>The routed equation system and its solution\<close>

text \<open>The main context is \<open>[]\<close> (\<open>main\<close> is the root activation, no formal binds it).\<close>

definition rc_ctx_sol ::
  "(pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "rc_ctx_sol = entry_state_sol rc_gs (prog_tyenv rc_program) rc_is_bot_pred rc_pi rc_procs (STR ''main'') rc_main"

lemma rc_ctx_terminates_c:
  "TD_side_warrowing_apinis_Interp_solve_c
     (entry_state_eqs rc_gs (prog_tyenv rc_program) rc_is_bot_pred rc_pi rc_procs (STR ''main'') rc_main)
     (cfg_exit rc_cfg, []) \<noteq> None"
  unfolding rc_cfg_def by eval

lemma rc_ctx_terminates:
  "entry_state_terminates rc_gs (prog_tyenv rc_program) rc_is_bot_pred rc_pi rc_procs (STR ''main'') rc_main"
  using rc_ctx_terminates_c[unfolded rc_cfg_def]
  by (rule entry_state_terminates_via_solve_c)

subsection \<open>The routed context is exactly \<open>Top\<close>\<close>

definition ctx_call :: "ivl list" where
  "ctx_call = entry_state_route rc_gs rc_is_bot_pred
                (entry_state_entered rc_gs rc_is_bot_pred
                   (locals (snd rc_ctx_sol (Inl (Statement 3, []))))
                   (CallEdge (compile_dst (prog_tyenv rc_program) (Some (STR ''y''))) [(STR ''a'')]
                      (compile_actuals (prog_tyenv rc_program) [(STR ''a'')] [V (STR ''x'')])))
                (CallEdge (compile_dst (prog_tyenv rc_program) (Some (STR ''y''))) [(STR ''a'')]
                      (compile_actuals (prog_tyenv rc_program) [(STR ''a'')] [V (STR ''x'')]))"

text \<open>The context the callee is entered under is the formal's own kind range,
  not the unbounded interval: the actual converts to \<^term>\<open>I32\<close> at the call,
  and \<^const>\<open>ivl_cast\<close> answers a conversion it cannot sharpen with that kind's
  range -- Goblint's \<open>top_of ik\<close>.\<close>

lemma ctx_call_val: "ctx_call = [ivl_top_of I32]"
  unfolding ctx_call_def rc_ctx_sol_def rc_is_bot_pred_def by eval

text \<open>The callee entry is materialized once, under the wide context, and never under
  the root context.\<close>
lemma callee_covered_call: "(FunctionEntry (STR ''p''), ctx_call) \<in> fst rc_ctx_sol"
  unfolding ctx_call_def rc_ctx_sol_def rc_is_bot_pred_def by eval

lemma callee_not_under_main: "(FunctionEntry (STR ''p''), []) \<notin> fst rc_ctx_sol"
  unfolding rc_ctx_sol_def rc_is_bot_pred_def by eval

end

