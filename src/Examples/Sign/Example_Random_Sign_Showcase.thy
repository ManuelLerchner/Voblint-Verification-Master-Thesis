section \<open>Example: nondeterministic input recovers precision through branching\<close>

theory Example_Random_Sign_Showcase
  imports "Voblint_Analysis.Sign_Exec_Sound" "Voblint_VIMP.VIMP_Notation"
begin

hide_const phase.N

text \<open>
  \<open>x := random()\<close> is nondeterministic. \<^const>\<open>random_sign\<close>
  answers it by forgetting \<open>x\<close> entirely -- setting it to \<^term>\<open>STop\<close>,
  the sign abstraction of the infinite concrete successor set
  \<open>{s(x := v) | v. True}\<close> -- regardless of what was known about \<open>x\<close>
  beforehand.

  A subsequent guard still recovers precision. For
  \<open>x := 0; x := random(); if (x > 0) y := x else y := 0 - x\<close>, the leading
  \<open>x := 0\<close> is overwritten by \<open>random()\<close> -- whatever was known about \<open>x\<close>
  beforehand is gone -- yet each branch narrows \<open>x\<close> before assigning \<open>y\<close>,
  and the two branches join to a single tight sign at the merge point: the
  branch guards recover enough information to derive \<open>y = SNonNeg\<close>, rather
  than losing all useful information after propagating the arbitrary value
  of \<open>x\<close> into \<open>y\<close>. The equation-system generator and the vendored TD solver
  compute this directly; no hand-derived abstract state is asserted here.
\<close>

subsection \<open>The source program\<close>

definition random_guard_program :: imp_prog where
  "random_guard_program = program {
     void main() {
       x := 0;
       x := random();
       if (0 < x) { y := x } else { y := 0 - x }
     }
   }"

subsection \<open>Non-vacuity: a concrete run where \<open>random()\<close> returns 42\<close>

text \<open>
  \<open>random_guard_exit_y_nonneg\<close> bounds every reachable exit state, but says
  nothing about whether any exist. This witness closes that gap at the
  source semantics: fixing the random draw at \<open>v = 42\<close>, \<^const>\<open>pcompletes\<close>
  (the small-step relation's terminating-run predicate) derives a concrete
  run of \<^const>\<open>prog_main\<close> \<open>random_guard_program\<close> reaching \<open>y = 42\<close> -- an
  actual state, not merely one permitted in principle, and \<open>42 \<ge> 0\<close>
  confirms the bound on it directly.
\<close>

lemma random_guard_run_42:
  fixes s :: store and gs :: "vname \<Rightarrow> bool" and \<Pi> :: proc_table
  shows "pcompletes gs \<Pi> (prog_main random_guard_program) s
           (s(''x'' := 0, ''x'' := 42, ''y'' := 42))"
proof -
  have step1: "pcompletes gs \<Pi> (Assign ''x'' (N 0)) s (s(''x'' := 0))"
    by (metis aval.simps(1) pcompletes_assign)
  have step2: "pcompletes gs \<Pi> (Random ''x'') (s(''x'' := 0)) ((s(''x'' := 0))(''x'' := 42))"
    by (rule pcompletes_random)
  have step12: "pcompletes gs \<Pi> (Seq (Assign ''x'' (N 0)) (Random ''x'')) s
                  ((s(''x'' := 0))(''x'' := 42))"
    using pcompletes_Seq[OF step1 step2] .
  have guard_true: "bval (Less (N 0) (V ''x'')) ((s(''x'' := 0))(''x'' := 42))"
    by simp
  have step3: "pcompletes gs \<Pi> (Assign ''y'' (V ''x'')) ((s(''x'' := 0))(''x'' := 42))
                 (((s(''x'' := 0))(''x'' := 42))(''y'' := 42))"
    by (metis aval.simps(2) fun_upd_def pcompletes_assign)
  have step3if: "pcompletes gs \<Pi>
      (If (Less (N 0) (V ''x'')) (Assign ''y'' (V ''x'')) (Assign ''y'' (Minus (N 0) (V ''x''))))
      ((s(''x'' := 0))(''x'' := 42)) (((s(''x'' := 0))(''x'' := 42))(''y'' := 42))"
    using pcompletes_IfTrue[OF guard_true step3] .
  have "pcompletes gs \<Pi>
      (Seq (Seq (Assign ''x'' (N 0)) (Random ''x''))
        (If (Less (N 0) (V ''x'')) (Assign ''y'' (V ''x'')) (Assign ''y'' (Minus (N 0) (V ''x'')))))
      s (((s(''x'' := 0))(''x'' := 42))(''y'' := 42))"
    using pcompletes_Seq[OF step12 step3if] .
  then show ?thesis unfolding random_guard_program_def by simp
qed

lemma random_guard_run_42_y_nonneg:
  fixes s :: store
  shows "(s(''x'' := 0, ''x'' := 42, ''y'' := 42)) ''y'' \<ge> 0"
  by simp

subsection \<open>Through the equation system generator and the TD solver\<close>

text \<open>
  \<^const>\<open>sign_exec_prog\<close> is not a black box: it is exactly three named steps.
  \<^item> \<^const>\<open>prog_cfg\<close> compiles the source program to a CFG (\<^const>\<open>compile_prog\<close>).
  \<^item> \<^const>\<open>sign_exec_eqs\<close> is \<^emph>\<open>the equation system generator\<close>: it applies
    \<^const>\<open>side_cfg_T_eff_st\<close> to that CFG and the executable sign transfer
    \<^const>\<open>sign_etf_st\<close>, producing one equation per CFG node.
  \<^item> \<^const>\<open>TD_side_always_join_Interp_solve\<close> is \<^emph>\<open>the vendored TD solver\<close>: it
    takes that equation system and a query node and computes a fixpoint,
    \<^const>\<open>sign_exec_raw\<close> being exactly this call.
  \<^const>\<open>sign_exec_prog\<close> then reads the exit node's local state back out of
  \<^const>\<open>sign_exec_raw\<close>'s result -- the same three steps \<open>sign_exec_sound_collecting\<close>'s
  proof unfolds to establish soundness.
\<close>

value "sign_exec_eqs (prog_table random_guard_program) (prog_procs random_guard_program)
         ''main'' (prog_main random_guard_program)"

value "sign_exec_raw (prog_table random_guard_program) (prog_procs random_guard_program)
         ''main'' (prog_main random_guard_program)"

value "sign_exec_prog ''main'' random_guard_program"

lemma random_guard_exec_y: "sign_exec_prog ''main'' random_guard_program ''y'' = SNonNeg"
  by eval

lemma random_guard_solver_terminates: "sign_terminates_prog ''main'' random_guard_program"
  by (rule sign_terminates_prog_via_solve_c) eval

corollary random_guard_exit_sound:
  "ltr_collect is_global (prog_cfg ''main'' random_guard_program) (cinit_stores is_global)
     (cfg_exit (prog_cfg ''main'' random_guard_program))
   \<le> \<lbrakk>sign_exec_prog ''main'' random_guard_program\<rbrakk>"
  by (rule sign_exec_prog_sound_collecting[OF random_guard_solver_terminates])

text \<open>
  Closing issue #43: for every concrete execution state that reaches the
  exit of \<open>random_guard_program\<close>, regardless of the value chosen by
  \<open>random()\<close>, \<open>y\<close> is nonnegative. \<open>random_guard_exit_sound\<close>
  over-approximates every such exit state by the computed
  \<^const>\<open>sign_exec_prog\<close> result; \<open>random_guard_exec_y\<close> pins that result's
  \<open>y\<close> to \<^term>\<open>SNonNeg\<close>, whose concretization is exactly the nonnegative
  integers.
\<close>

corollary random_guard_exit_y_nonneg:
  assumes "t \<in> ltr_collect is_global (prog_cfg ''main'' random_guard_program) (cinit_stores is_global)
             (cfg_exit (prog_cfg ''main'' random_guard_program))"
  shows "t ''y'' \<ge> 0"
proof -
  have t_in: "t \<in> \<lbrakk>sign_exec_prog ''main'' random_guard_program\<rbrakk>"
    using assms random_guard_exit_sound by blast
  have "t ''y'' \<in> gamma_sign (sign_exec_prog ''main'' random_guard_program ''y'')"
    using gamma_stateD[OF t_in] by simp
  then show ?thesis using random_guard_exec_y by simp
qed

subsection \<open>Annotated CFG\<close>

text \<open>
  \<^const>\<open>sign_annotated_dot_prog_lit\<close> renders the compiled CFG with every node
  labelled by its computed sign abstract state, confirming visually that
  \<open>x\<close> shows \<open>STop\<close> right after \<open>random()\<close>, narrows to \<open>SPos\<close>/\<open>SNonPos\<close> on
  each branch, and that \<open>y\<close> is \<open>SNonNeg\<close> at the exit.
\<close>

definition random_guard_mnm :: pname where "random_guard_mnm = ''main''"

ML_val \<open>
  writeln (@{code sign_annotated_dot_prog_lit} @{code random_guard_mnm} @{code random_guard_program})
\<close>

end
