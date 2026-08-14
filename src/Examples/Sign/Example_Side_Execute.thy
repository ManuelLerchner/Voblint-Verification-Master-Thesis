theory Example_Side_Execute
  imports "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_Formalization.Source_Activation_Sound"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Running the certified sign analyzer on \<open>x := 1\<close>\<close>

text \<open>
  The smallest end-to-end witness: compile \<open>x := 1\<close>, run the actual vendored
  solver via @{const sign_exec_raw}, and read the certified soundness off the
  program-parametric theorems in @{theory Voblint_Analysis.Sign_Exec_Sound}.  The
  @{command value} / \<open>eval\<close> evaluates at build time, so a green build is the
  execution proof.
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

text \<open>
  Querying the computed abstract state at the exit (these @{command value} calls
  evaluate at build time): \<open>x\<close> is \<open>SPos\<close>, an untouched \<open>y\<close> stays \<open>STop\<close>.
\<close>

value "case_lifted bot (\<lambda>\<sigma>. \<sigma>) (sign_exec_prog x1_gs (STR ''main'') x1_prog) (STR ''x'')"
value "case_lifted bot (\<lambda>\<sigma>. \<sigma>) (sign_exec_prog x1_gs (STR ''main'') x1_prog) (STR ''y'')"

text \<open>The solver computes \<open>x \<mapsto> SPos\<close> at the exit, captured as a theorem
  by code reflection.\<close>

lemma x1_computes_x_pos:
  "case_lifted bot (\<lambda>\<sigma>. \<sigma>) (sign_exec_prog x1_gs (STR ''main'') x1_prog) (STR ''x'') = SPos"
  by eval

lemma x1_y_top:
  "case_lifted bot (\<lambda>\<sigma>. \<sigma>) (sign_exec_prog x1_gs (STR ''main'') x1_prog) (STR ''y'') = STop"
  by eval

text \<open>
  Termination is not assumed but proved: the executable side solver returns a
  result on this program (@{method eval}), so by
  @{thm sign_terminates_prog_via_solve_c} the program lies in the solver's domain.
\<close>

lemma x1_terminates: "sign_terminates_prog x1_gs (STR ''main'') x1_prog"
  by (rule sign_terminates_prog_via_solve_c) eval

text \<open>
  Certified sound, unconditionally: the computed result over-approximates the
  interprocedural collecting semantics at the exit from any input store -- so
  after \<open>x := 1\<close>, \<open>x\<close> is positive.  An instance of the program-parametric
  @{thm sign_exec_prog_sound_collecting}, with termination discharged by execution.
\<close>

corollary x1_certified_sound:
  "ltr_collect x1_gs (prog_cfg (STR ''main'') x1_prog) (cinit_stores x1_gs) (cfg_exit (prog_cfg (STR ''main'') x1_prog))
   \<le> gamma_state_lift (sign_exec_prog x1_gs (STR ''main'') x1_prog)"
  by (rule sign_exec_prog_sound_collecting[OF refl x1_terminates])

definition x1_s0 :: store where
  "x1_s0 = (\<lambda>_. 0)"

lemma x1_completed:
  "pcompletes x1_gs (prog_table x1_prog) (prog_main x1_prog) x1_s0
     (x1_s0((STR ''x'') := 1))"
  unfolding pcompletes_def
  apply (simp only: x1_prog_def x1_s0_def prog_table_make prog_main_make)
  apply (rule star.step)
   apply (rule pstep.Assign)
  by simp

lemma x1_completed_run_collect:
  "x1_s0((STR ''x'') := 1)
     \<in> ltr_collect x1_gs (prog_cfg (STR ''main'') x1_prog) (cinit_stores x1_gs) (cfg_exit (prog_cfg (STR ''main'') x1_prog))"
proof -
  have init: "x1_s0 \<in> cinit_stores x1_gs"
    by (simp add: x1_s0_def cinit_stores_def)
  have wf: "wf_compile_input x1_gs (prog_table x1_prog) (prog_procs x1_prog) (STR ''main'') (prog_main x1_prog)"
    unfolding wf_compile_input_def x1_prog_def
    by (auto simp: wf_source_program_def wf_proc_decl_def source_aexp_def
          proc_decl_of_def prog_main_name_def ret_var_def reserved_ret_var_def
          declared_global_def special_table_def special_pname_nondet_int_def
          split: if_splits)

  have run:
    "star (pstep x1_gs (prog_table x1_prog)) (prog_main x1_prog, x1_s0, [])
      (VIMP_Proc.com.SKIP, x1_s0((STR ''x'') := 1), [])"
    using x1_completed unfolding pcompletes_def .
  from source_completes_ltr_collect_exit[OF wf init run]
  show ?thesis unfolding prog_cfg_def .
qed

theorem x1_explicit_completed_run_covered:
  "pcompletes x1_gs (prog_table x1_prog) (prog_main x1_prog) x1_s0
      (x1_s0((STR ''x'') := 1))
   \<and> x1_s0((STR ''x'') := 1) \<in> gamma_state_lift (sign_exec_prog x1_gs (STR ''main'') x1_prog)"
proof (rule conjI)
  show "pcompletes x1_gs (prog_table x1_prog) (prog_main x1_prog) x1_s0
      (x1_s0((STR ''x'') := 1))"
    by (rule x1_completed)
next
  have collect:
    "x1_s0((STR ''x'') := 1) \<in>
      ltr_collect x1_gs (prog_cfg (STR ''main'') x1_prog) (cinit_stores x1_gs) (cfg_exit (prog_cfg (STR ''main'') x1_prog))"
    using x1_completed_run_collect
    by (simp add: prog_cfg_def)
  show "x1_s0((STR ''x'') := 1) \<in> gamma_state_lift (sign_exec_prog x1_gs (STR ''main'') x1_prog)"
    using x1_certified_sound collect by blast
qed

subsection \<open>Annotated CFG visualisation\<close>

text \<open>
  One-command DOT export via @{const sign_annotated_dot_prog_lit}: the CFG
  with per-program-point sign abstract states on each node label.
\<close>

definition x1_mnm :: pname where "x1_mnm = (STR ''main'')"

ML_val \<open>
  writeln (@{code sign_annotated_dot_prog_lit} (@{code declared_global} @{code x1_prog}) @{code x1_mnm} @{code x1_prog})
\<close>

end



