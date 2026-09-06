section \<open>Example: Sign analysis of a single global-increment call\<close>

theory Example_Side_Proc_Global
  imports
    "Voblint_CLI.Sign_Entry"
    "Voblint_VIMP.VIMP_Notation"
    Example_Inc_Proc
begin

text \<open>
  Interprocedural witness: \<^const>\<open>inc_program\<close> with a single call to procedure
  \<open>p\<close>, which increments the global \<open>counter\<close>. The computed result is read from
  the routed D/G solved table the production report also reads, and its
  soundness comes from that table's own node-soundness bridge --- no separate
  analysis pipeline for the example.
\<close>

abbreviation inc_gs :: "vname \<Rightarrow> bool" where
  "inc_gs \<equiv> declared_global inc_program"

lemma inc_reserved: "reserved_ret_var inc_gs"
  unfolding reserved_ret_var_def inc_program_def by (simp add: ret_var_def)

text \<open>The routed-unit solve terminates, and its solved key set is closed under
  the compiled graph --- the four coverage facts the node-soundness bridge
  turns on, each computed rather than argued. Unlike the store-only check
  examples this program really does have a call edge, so the call and combine
  closures are genuine \<open>eval\<close> facts rather than vacuous.\<close>

lemma inc_solver_terminates:
  "sctx_terminates_prog inc_gs inc_program"
  by (rule sctx_terminates_prog_via_solve_c) eval

lemma inc_entry_cov:
  "(cfg_entry (prog_cfg inc_program), ())
     \<in> fst (sctx_sol_prog inc_gs inc_program)"
  by eval

lemma inc_fwd_ok_ball:
  "\<forall>(u, a, w) \<in> intra (prog_cfg inc_program).
     (u, ()) \<in> fst (sctx_sol_prog inc_gs inc_program) \<longrightarrow>
     (w, ()) \<in> fst (sctx_sol_prog inc_gs inc_program)"
  by eval

lemma inc_fwd_ok:
  assumes "(u, ctx) \<in> fst (sctx_sol_prog inc_gs inc_program)"
    and "(u, a, w) \<in> intra (prog_cfg inc_program)"
  shows "(w, ctx) \<in> fst (sctx_sol_prog inc_gs inc_program)"
  using assms inc_fwd_ok_ball by (cases ctx) auto

lemma inc_call_fwd_ok_ball:
  "\<forall>(u, ca, ce, k) \<in> calls (prog_cfg inc_program).
     (case ce of FunctionEntry q \<Rightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog inc_gs inc_program)
      | _ \<Rightarrow> True)
     \<and> ((k, ()) \<in> fst (sctx_sol_prog inc_gs inc_program))"
  by eval

lemma inc_call_fwd_ok:
  assumes "(u, ctx) \<in> fst (sctx_sol_prog inc_gs inc_program)"
    and "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg inc_program)"
  shows "(FunctionEntry q, ()) \<in> fst (sctx_sol_prog inc_gs inc_program)"
  using assms inc_call_fwd_ok_ball by fastforce

lemma inc_comb_fwd_ok:
  assumes "(cl, c1) \<in> fst (sctx_sol_prog inc_gs inc_program)"
    and "(cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg inc_program)"
  shows "(k, c1) \<in> fst (sctx_sol_prog inc_gs inc_program)"
  using assms inc_call_fwd_ok_ball by (cases c1) fastforce

lemma inc_node_sound:
  "ltr_collect inc_gs (prog_cfg inc_program) (cinit_stores inc_gs) v
     \<subseteq> \<lbrakk>case lookup_context (analyse_sign_result_for inc_gs inc_program) v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  by (rule analyse_sign_result_node_sound_for
        [OF inc_reserved inc_solver_terminates inc_entry_cov
            inc_fwd_ok inc_call_fwd_ok inc_comb_fwd_ok])

text \<open>The computed environment at the program exit, read out of the same
  solved table.\<close>

definition inc_exit_env :: "sign abs_state" where
  "inc_exit_env =
     (case lookup_context (analyse_sign_result_for inc_gs inc_program)
             (cfg_exit (prog_cfg inc_program)) () of
        Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st)"

text \<open>The global the callee increments is strictly positive at the exit ---
  computed by the solver, not asserted. \<^const>\<open>cinit_stores\<close> starts every
  global at zero and the single call increments it once, so \<^const>\<open>SPos\<close> is
  the exact answer; the routed table resolves it where a merged whole-state
  environment only reaches \<^const>\<open>SNonNeg\<close>.\<close>

lemma inc_counter_pos: "inc_exit_env (STR ''counter'') = SPos"
  unfolding inc_exit_env_def by eval

corollary inc_certified_sound:
  "ltr_collect inc_gs (prog_cfg inc_program) (cinit_stores inc_gs)
     (cfg_exit (prog_cfg inc_program))
   \<le> \<lbrakk>inc_exit_env\<rbrakk>"
  unfolding inc_exit_env_def
  using inc_node_sound
  by (simp add: gamma_point_def split: lifted.splits)

end
