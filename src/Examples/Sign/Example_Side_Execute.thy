theory Example_Side_Execute
  imports "Voblint_Analysis_Sign.Sign_Analyses"
    "Voblint_Result.Source_Activation_Sound"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Running the certified sign analyzer on \<open>x := 1\<close>\<close>

text \<open>
  The smallest end-to-end witness: compile \<open>x := 1\<close>, run the actual vendored
  solver behind Sign's unit-context registration \<open>sign_rule\<close> at
  \<^const>\<open>Globals_Join\<close>, and read the certified soundness off that registration's
  program-parametric endpoints in @{theory Voblint_Analysis_Sign.Sign_Analyses}.
  The @{command value} / \<open>eval\<close> evaluates at build time, so a green build is the
  execution proof.
\<close>

definition x1_prog :: imp_prog where
  "x1_prog = program { fun main() { x = 1; } }"

text \<open>No \<open>global\<close> declarations, so the classifier this program's own source
  gives is trivially false everywhere -- \<open>x\<close> and \<open>y\<close> are both local.\<close>
abbreviation x1_gs :: "vname \<Rightarrow> bool" where
  "x1_gs \<equiv> declared_global x1_prog"

lemma x1_prog_declared_global_vars [simp]:
  "declared_global_vars x1_prog = []"
  by (simp add: x1_prog_def)

lemma x1_reserved: "reserved_ret_var x1_gs"
  unfolding reserved_ret_var_def x1_prog_def by (simp add: ret_var_def)

lemma x1_calls_eval: "calls (prog_cfg x1_prog) = {}"
  unfolding prog_cfg_def by eval

text \<open>
  Termination is not assumed but proved: the executable routed solver returns a
  result on this program (@{method eval}), so the program lies in the solver's
  domain.  The three closure facts are computed the same way.
\<close>

lemma x1_terminates: "sign_rule.terminates Globals_Join x1_gs x1_prog"
  unfolding sign_rule.terminates_code
  by (rule TD_side_rule_Interp.solve_dom_of_solve_c) eval

lemma x1_entry_cov:
  "(cfg_entry (prog_cfg x1_prog), ()) \<in> sign_rule.sol_vars Globals_Join x1_gs x1_prog"
  by eval

lemma x1_fwd_ok_ball:
  "\<forall>(u, a, w) \<in> intra (prog_cfg x1_prog).
     (u, ()) \<in> sign_rule.sol_vars Globals_Join x1_gs x1_prog \<longrightarrow>
     (w, ()) \<in> sign_rule.sol_vars Globals_Join x1_gs x1_prog"
  by eval

lemma x1_fwd_ok:
  assumes "(u, ctx) \<in> sign_rule.sol_vars Globals_Join x1_gs x1_prog"
    and "(u, a, w) \<in> intra (prog_cfg x1_prog)"
  shows "(w, ctx) \<in> sign_rule.sol_vars Globals_Join x1_gs x1_prog"
  using assms x1_fwd_ok_ball by (cases ctx) auto

lemma x1_call_fwd_ok:
  assumes "(u, ctx) \<in> sign_rule.sol_vars Globals_Join x1_gs x1_prog"
    and "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg x1_prog)"
  shows "(FunctionEntry q, ()) \<in> sign_rule.sol_vars Globals_Join x1_gs x1_prog"
  using assms by (simp add: x1_calls_eval)

lemma x1_comb_fwd_ok:
  assumes "(cl, c1) \<in> sign_rule.sol_vars Globals_Join x1_gs x1_prog"
    and "(cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg x1_prog)"
  shows "(k, c1) \<in> sign_rule.sol_vars Globals_Join x1_gs x1_prog"
  using assms by (simp add: x1_calls_eval)

lemma x1_node_sound:
  "\<C>\<^bsub>x1_gs,prog_cfg x1_prog,cinit_stores x1_gs\<^esub> v
     \<subseteq> \<lbrakk>case lookup_context (sign_rule.result Globals_Join x1_gs x1_prog) v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  using sign_rule.result_node_sound_closure
          [OF x1_terminates x1_fwd_ok x1_call_fwd_ok x1_comb_fwd_ok x1_entry_cov]
  unfolding sign_rule.state_at_unfold .

definition x1_exit_env :: "sign abs_state" where
  "x1_exit_env =
     (case lookup_context (sign_rule.result Globals_Join x1_gs x1_prog)
             (cfg_exit (prog_cfg x1_prog)) () of
        Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st)"

text \<open>The solver computes the abstract state at the exit, captured as theorems
  by code reflection: \<open>x\<close> is \<open>SPos\<close>, an untouched \<open>y\<close> stays \<open>STop\<close>.\<close>

lemma x1_computes_x_pos: "x1_exit_env (STR ''x'') = SPos"
  unfolding x1_exit_env_def by eval

lemma x1_y_top: "x1_exit_env (STR ''y'') = STop"
  unfolding x1_exit_env_def by eval

text \<open>
  Certified sound, unconditionally: the computed result over-approximates the
  interprocedural collecting semantics at the exit from any input store -- so
  after \<open>x := 1\<close>, \<open>x\<close> is positive.
\<close>

corollary x1_certified_sound:
  "\<C>\<^bsub>x1_gs,prog_cfg x1_prog,cinit_stores x1_gs\<^esub> (cfg_exit (prog_cfg x1_prog))
   \<le> \<lbrakk>x1_exit_env\<rbrakk>"
  unfolding x1_exit_env_def
  using x1_node_sound
  by (simp add: prog_main_name_def gamma_point_def split: lifted.splits)

definition x1_s0 :: store where
  "x1_s0 = (\<lambda>_. 0)"

lemma x1_completed:
  "pcompletes x1_gs (prog_table x1_prog) (prog_main x1_prog) x1_s0
     (x1_s0((STR ''x'') := 1))"
  apply (simp only: x1_prog_def x1_s0_def mk_program_simps)
  apply (rule star.step)
   apply (rule pstep.Assign)
  by simp

lemma x1_completed_run_collect:
  "x1_s0((STR ''x'') := 1)
     \<in> \<C>\<^bsub>x1_gs,prog_cfg x1_prog,cinit_stores x1_gs\<^esub> (cfg_exit (prog_cfg x1_prog))"
proof -
  have init: "x1_s0 \<in> cinit_stores x1_gs"
    by (simp add: x1_s0_def cinit_stores_def)
  have wf: "wf_compile_input x1_gs (prog_table x1_prog) (prog_procs x1_prog)"
    unfolding x1_prog_def
    by (auto simp: wf_compile_input_simps split: if_splits)

  have run:
    "x1_gs, prog_table x1_prog \<turnstile> (main_body (prog_table x1_prog), x1_s0, [])
      \<rightarrow>\<^sub>p\<^sup>* (VIMP_Proc.com.SKIP, x1_s0((STR ''x'') := 1), [])"
    using x1_completed by simp
  from source_completes_ltr_collect_exit[OF wf init run]
  show ?thesis unfolding prog_cfg_def .
qed

theorem x1_explicit_completed_run_covered:
  "pcompletes x1_gs (prog_table x1_prog) (prog_main x1_prog) x1_s0
      (x1_s0((STR ''x'') := 1))
   \<and> x1_s0((STR ''x'') := 1) \<in> \<lbrakk>x1_exit_env\<rbrakk>"
proof (rule conjI)
  show "pcompletes x1_gs (prog_table x1_prog) (prog_main x1_prog) x1_s0
      (x1_s0((STR ''x'') := 1))"
    by (rule x1_completed)
next
  have collect:
    "x1_s0((STR ''x'') := 1) \<in>
      \<C>\<^bsub>x1_gs,prog_cfg x1_prog,cinit_stores x1_gs\<^esub> (cfg_exit (prog_cfg x1_prog))"
    using x1_completed_run_collect
    by (simp add: prog_cfg_def)
  show "x1_s0((STR ''x'') := 1) \<in> \<lbrakk>x1_exit_env\<rbrakk>"
    using x1_certified_sound collect by blast
qed

end



