theory Example_Side_Execute
  imports "Voblint_CLI.Sign_Entry"
    "Voblint_Soundness.Source_Activation_Sound"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Running the certified sign analyzer on \<open>x := 1\<close>\<close>

text \<open>
  The smallest end-to-end witness: compile \<open>x := 1\<close>, run the actual vendored
  solver behind \<^const>\<open>analyse_sign_result_for\<close>, and read the certified
  soundness off the program-parametric bridge in
  @{theory Voblint_CLI.Sign_Entry}.  The @{command value} / \<open>eval\<close> evaluates
  at build time, so a green build is the execution proof.
\<close>

definition x1_prog :: imp_prog where
  "x1_prog = program { void main() { x := 1 } }"

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

lemma x1_terminates: "sctx_terminates_prog x1_gs x1_prog"
  by (rule sctx_terminates_prog_via_solve_c) eval

lemma x1_entry_cov:
  "(cfg_entry (prog_cfg x1_prog), ())
     \<in> fst (sctx_sol_prog x1_gs x1_prog)"
  by eval

lemma x1_fwd_ok_ball:
  "\<forall>(u, a, w) \<in> intra (prog_cfg x1_prog).
     (u, ()) \<in> fst (sctx_sol_prog x1_gs x1_prog) \<longrightarrow>
     (w, ()) \<in> fst (sctx_sol_prog x1_gs x1_prog)"
  by eval

lemma x1_fwd_ok:
  assumes "(u, ctx) \<in> fst (sctx_sol_prog x1_gs x1_prog)"
    and "(u, a, w) \<in> intra (prog_cfg x1_prog)"
  shows "(w, ctx) \<in> fst (sctx_sol_prog x1_gs x1_prog)"
  using assms x1_fwd_ok_ball by (cases ctx) auto

lemma x1_call_fwd_ok:
  assumes "(u, ctx) \<in> fst (sctx_sol_prog x1_gs x1_prog)"
    and "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg x1_prog)"
  shows "(FunctionEntry q, ()) \<in> fst (sctx_sol_prog x1_gs x1_prog)"
  using assms by (simp add: x1_calls_eval)

lemma x1_comb_fwd_ok:
  assumes "(cl, c1) \<in> fst (sctx_sol_prog x1_gs x1_prog)"
    and "(cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg x1_prog)"
  shows "(k, c1) \<in> fst (sctx_sol_prog x1_gs x1_prog)"
  using assms by (simp add: x1_calls_eval)

lemma x1_node_sound:
  "ltr_collect x1_gs (prog_cfg x1_prog) (cinit_stores x1_gs) v
     \<subseteq> \<lbrakk>case lookup_context (analyse_sign_result_for x1_gs x1_prog) v () of
            Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st\<rbrakk>"
  by (rule analyse_sign_result_node_sound_for
        [OF x1_reserved x1_terminates x1_entry_cov
            x1_fwd_ok x1_call_fwd_ok x1_comb_fwd_ok])

definition x1_exit_env :: "sign abs_state" where
  "x1_exit_env =
     (case lookup_context (analyse_sign_result_for x1_gs x1_prog)
             (cfg_exit (prog_cfg x1_prog)) () of
        Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"

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
  "ltr_collect x1_gs (prog_cfg x1_prog) (cinit_stores x1_gs) (cfg_exit (prog_cfg x1_prog))
   \<le> \<lbrakk>x1_exit_env\<rbrakk>"
  unfolding x1_exit_env_def
  using x1_node_sound
  by (simp add: prog_main_name_def gamma_point_def split: point_state.splits)

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
     \<in> ltr_collect x1_gs (prog_cfg x1_prog) (cinit_stores x1_gs) (cfg_exit (prog_cfg x1_prog))"
proof -
  have init: "x1_s0 \<in> cinit_stores x1_gs"
    by (simp add: x1_s0_def cinit_stores_def)
  have wf: "wf_compile_input x1_gs (prog_table x1_prog) (prog_procs x1_prog)"
    unfolding x1_prog_def
    by (auto simp: wf_compile_input_simps wf_source_program_def wf_proc_decl_def
          declared_global_def
          split: if_splits)

  have run:
    "star (pstep x1_gs (prog_table x1_prog)) (main_body (prog_table x1_prog), x1_s0, [])
      (VIMP_Proc.com.SKIP, x1_s0((STR ''x'') := 1), [])"
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
      ltr_collect x1_gs (prog_cfg x1_prog) (cinit_stores x1_gs) (cfg_exit (prog_cfg x1_prog))"
    using x1_completed_run_collect
    by (simp add: prog_cfg_def)
  show "x1_s0((STR ''x'') := 1) \<in> \<lbrakk>x1_exit_env\<rbrakk>"
    using x1_certified_sound collect by blast
qed

end



