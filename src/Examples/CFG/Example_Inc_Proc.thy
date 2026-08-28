section \<open>Example support: global increment procedure\<close>

theory Example_Inc_Proc
  imports "Voblint_CFG.CFG_Transfer" "Voblint_CFG.CFG_Prune" "Voblint_VIMP.VIMP_Notation"
    "Voblint_CFG.Located_Exec"
begin

text \<open>
  Shared witness program: a single procedure p increments the declared global
  counter, and main sets a same-named-convention local before calling p once.
  \<open>counter\<close> carries no naming hint of its storage class, and \<open>Glocal\<close> carries
  the classic hint for the opposite class, so every classifier call below is
  driven by \<^const>\<open>declared_global\<close> alone -- see
  \<open>inc_program_counter_global\<close>/\<open>inc_program_glocal_not_global\<close>. Examples
  reuse this theory when they need a small interprocedural program with a
  concrete run-to-collecting witness.
\<close>

definition inc_program :: imp_prog where
  "inc_program = program {
     global int32 counter;
     void p() { counter := counter + 1 }
     void main() { Glocal := 1; p() }
   }"

definition inc_pi :: proc_table where
  "inc_pi = prog_table inc_program"

lemma inc_program_parts:
  shows "prog_procs inc_program = [(STR ''p'')]"
    and "prog_table inc_program =
           [(STR ''p'') \<mapsto> proc_decl_of [] (imp \<lbrakk> counter := counter + 1 \<rbrakk>),
            prog_main_name \<mapsto> proc_decl_of [] (imp \<lbrakk> Glocal := 1 ; p() \<rbrakk>)]"
    and "prog_main inc_program = imp \<lbrakk> Glocal := 1 ; p() \<rbrakk>"
  by (simp_all add: inc_program_def prog_main_name_def)

text \<open>\<open>declared_global_vars\<close> for the concrete program: the entry point where the
  declaration-driven classifier meets a real declared list. \<open>Glocal\<close> is
  undeclared and therefore local despite its spelling; \<open>counter\<close> is declared
  global despite carrying no naming hint at all.\<close>
lemma inc_program_declared_global_vars [simp]:
  "declared_global_vars inc_program = [(STR ''counter'')]"
  by (simp add: inc_program_def)

lemma inc_program_counter_global [simp]: "declared_global inc_program (STR ''counter'')"
  by simp

lemma inc_program_glocal_not_global [simp]: "\<not> declared_global inc_program (STR ''Glocal'')"
  by simp

text \<open>\<open>inc_ty\<close> is the program's own typing environment: the compiler elaborates
  every edge payload against it, so the edge shapes below name it too.\<close>
abbreviation inc_ty :: tyenv where
  "inc_ty \<equiv> prog_tyenv inc_program"

definition inc_g :: cfg where
  "inc_g = compile_prog (prog_tyenv inc_program) (prog_table inc_program) (prog_procs inc_program)
     (STR ''main'') (prog_main inc_program)"

lemma inc_g_eq_compile:
  "inc_g = compile_prog (prog_tyenv inc_program) inc_pi [(STR ''p'')] (STR ''main'')
     (imp \<lbrakk> Glocal := 1 ; p() \<rbrakk>)"
  by (simp add: inc_g_def inc_pi_def inc_program_parts)

lemma edge_collect_assign_enter_state:
  fixes s :: store and x :: vname and a :: texp and gs :: "vname \<Rightarrow> bool"
  assumes "enter_state gs s \<in> S"
  shows "(enter_state gs s)(x := teval a (enter_state gs s))
           \<in> edge_collect (EA_Assign x a) S"
  using assms by auto

lemma one_in_ik_range_I32 [simp]: "(1::int) \<in> ik_range I32"
  by eval

text \<open>The increment reads its operand kinds off the elaborated tree and wraps at
  each of them. The two range premises say the stored counter and its successor
  are both representable at \<^const>\<open>I32\<close>, which is exactly when the machine
  increment agrees with the unbounded one.\<close>
lemma inc_ty_is_default [simp]: "inc_ty = default_tyenv"
  by (simp add: prog_tyenv_def inc_program_def default_tyenv_def fun_eq_iff)

lemma taval_plus_counter_on_enter_declared:
  assumes ty: "s (STR ''counter'') \<in> ik_range I32"
      and nov: "s (STR ''counter'') + 1 \<in> ik_range I32"
  shows "ik_norm (inc_ty (STR ''counter''))
           (taval_syn inc_ty (Plus (V (STR ''counter'')) (N 1))
              (enter_state (declared_global inc_program) s))
         = s (STR ''counter'') + 1"
  by (simp add: enter_state_def taval_syn_def opk_def default_tyenv_def
                Let_def ik_of_lit_def ik_norm_idem
                ik_norm_id[OF ty] ik_norm_id[OF nov])

lemma combine_after_enter_global_assign_declared:
  assumes "declared_global inc_program x"
  shows "combine_env (declared_global inc_program) s
           ((enter_state (declared_global inc_program) s)(x := v)) = s(x := v)"
  using assms by (auto simp: combine_env_def enter_state_def)

text \<open>
  The call completion fact for \<^const>\<open>inc_program\<close>, at the declaration-driven
  classifier \<^term>\<open>declared_global inc_program\<close>.  The two range premises are
  what make the machine increment agree with \<open>+ 1\<close>: without them the
  assignment writes the wrapped successor instead.
\<close>
lemma pcompletes_inc_pcall_declared:
  fixes s :: store
  assumes ty: "s (STR ''counter'') \<in> ik_range I32"
      and nov: "s (STR ''counter'') + 1 \<in> ik_range I32"
  shows "pcompletes inc_ty (declared_global inc_program) inc_pi (imp \<lbrakk> p() \<rbrakk>) s
           (s((STR ''counter'') := s (STR ''counter'') + 1)) rk"
proof -
  let ?body = "imp \<lbrakk> counter := counter + 1 \<rbrakk>"
  have g: "declared_global inc_program (STR ''counter'')" by simp
  have run: "pcompletes inc_ty (declared_global inc_program) inc_pi (imp \<lbrakk> p() \<rbrakk>) s
                (combine_env (declared_global inc_program) s
                  ((enter_state (declared_global inc_program) s)((STR ''counter'') := s (STR ''counter'') + 1))) rk"
  proof (rule pcompletes_Call_parameterless[where c = ?body])
    show "inc_pi (STR ''p'') = Some (proc_decl_of [] ?body)"
      by (simp add: inc_pi_def inc_program_parts prog_main_name_def)
    show "pcompletes inc_ty (declared_global inc_program) inc_pi ?body
             (enter_state (declared_global inc_program) s)
             ((enter_state (declared_global inc_program) s)((STR ''counter'') := s (STR ''counter'') + 1)) I32"
    proof -
      show ?thesis
        by (subst taval_plus_counter_on_enter_declared
                    [where s = s, OF ty nov, symmetric])
           (rule pcompletes_assign)
    qed
  qed
  moreover have
    "combine_env (declared_global inc_program) s
       ((enter_state (declared_global inc_program) s)((STR ''counter'') := s (STR ''counter'') + 1))
       = s((STR ''counter'') := s (STR ''counter'') + 1)"
    using combine_after_enter_global_assign_declared[OF g] by simp
  ultimately show ?thesis by simp
qed

lemma prog_pcompletes_inc_pcall:
  fixes s :: store
  assumes ty: "s (STR ''counter'') \<in> ik_range I32"
      and nov: "s (STR ''counter'') + 1 \<in> ik_range I32"
  shows "prog_pcompletes inc_program (imp \<lbrakk> p() \<rbrakk>) s
          (s((STR ''counter'') := s (STR ''counter'') + 1)) rk"
proof -
  have storage:
    "storage_global inc_program prog_main_name = declared_global inc_program"
    by (rule ext) simp
  show ?thesis
    using pcompletes_inc_pcall_declared[where s = s, OF ty nov]
    unfolding prog_pcompletes_def inc_pi_def storage by simp
qed

text \<open>
  The same regression one layer down, at the compiled CFG.  The eight
  \<^const>\<open>cstep\<close> transitions retrace \<open>inc_g\<close>'s edges: \<open>main\<close>'s entry \<open>Nop\<close>,
  the \<open>Glocal\<close> assignment, the call into \<open>p\<close>, \<open>p\<close>'s entry \<open>Nop\<close>, the increment
  assignment, \<open>p\<close>'s return, the call's resume, and \<open>main\<close>'s return. \<open>Glocal\<close>'s
  value survives untouched through the call, since it plays no role in \<open>p\<close>'s
  classification-driven local/global split.  Each edge payload is the
  elaborated \<^typ>\<open>texp\<close> the compiler emitted, so \<^const>\<open>edge_step\<close> reproduces
  the source writes with \<^const>\<open>teval\<close> alone; the range premises are the ones
  the source-level counterpart above needs, for the same reason.
\<close>
lemma cstep_inc_pcall_declared:
  fixes s :: store
  assumes ty: "s (STR ''counter'') \<in> ik_range I32"
      and nov: "s (STR ''counter'') + 1 \<in> ik_range I32"
  shows "star (cstep (declared_global inc_program) inc_g) (FunctionEntry (STR ''main''), s, [])
           (FunctionResult (STR ''main''), s((STR ''Glocal'') := 1, (STR ''counter'') := s (STR ''counter'') + 1), [])"
proof -
  let ?gs = "declared_global inc_program"
  have e1: "(FunctionEntry (STR ''main''), EA_Nop, Statement 2) \<in> intra inc_g"
    and e2: "(Statement 2, EA_Assign (STR ''Glocal'')
                (elaborate_to inc_ty (inc_ty (STR ''Glocal'')) (N 1)), Statement 3) \<in> intra inc_g"
    and e3: "(Statement 3, CallEdge None [] [], FunctionEntry (STR ''p''), Statement 4) \<in> calls inc_g"
    and e4: "(FunctionEntry (STR ''p''), EA_Nop, Statement 0) \<in> intra inc_g"
    and e5: "(Statement 0, EA_Assign (STR ''counter'')
                (elaborate_to inc_ty (inc_ty (STR ''counter'')) (Plus (V (STR ''counter'')) (N 1))),
              Statement 1) \<in> intra inc_g"
    and e6: "(Statement 1, EA_Ret None (STR ''p'') I32, FunctionResult (STR ''p'')) \<in> intra inc_g"
    and e7: "(Statement 4, EA_Ret None (STR ''main'') I32, FunctionResult (STR ''main'')) \<in> intra inc_g"
    by eval+
  have g: "?gs (STR ''counter'')" by simp
  have s1: "cstep ?gs inc_g (FunctionEntry (STR ''main''), s, []) (Statement 2, s, [])"
    by (rule cstep.Intra[OF e1]) simp
  have s2: "cstep ?gs inc_g (Statement 2, s, []) (Statement 3, s((STR ''Glocal'') := 1), [])"
    by (rule cstep.Intra[OF e2])
       (simp add: elaborate_to_def elaborate_syn_def opk_def default_tyenv_def)
  have s3: "cstep ?gs inc_g (Statement 3, s((STR ''Glocal'') := 1), [])
              (FunctionEntry (STR ''p''), enter_state ?gs (s((STR ''Glocal'') := 1)),
               [(Statement 4, None, s((STR ''Glocal'') := 1))])"
    using cstep.Call[OF e3] by simp
  have s4: "cstep ?gs inc_g
              (FunctionEntry (STR ''p''), enter_state ?gs (s((STR ''Glocal'') := 1)), [(Statement 4, None, s((STR ''Glocal'') := 1))])
              (Statement 0, enter_state ?gs (s((STR ''Glocal'') := 1)), [(Statement 4, None, s((STR ''Glocal'') := 1))])"
    by (rule cstep.Intra[OF e4]) simp
  \<comment> \<open>The edge carries the elaborated tree, so the step needs \<open>teval\<close> of it --
      not the \<open>taval_syn\<close> form above. Writing \<open>Glocal\<close> first leaves \<open>counter\<close>
      untouched, so the two range premises still apply.\<close>
  have inc_at_glocal:
    "teval (elaborate_to inc_ty (inc_ty (STR ''counter''))
              (Plus (V (STR ''counter'')) (N 1)))
       (enter_state (declared_global inc_program) (s((STR ''Glocal'') := 1)))
     = s (STR ''counter'') + 1"
    by (simp add: elaborate_to_def elaborate_syn_def enter_state_def opk_def
                  default_tyenv_def Let_def ik_of_lit_def ik_norm_idem
                  ik_norm_id[OF ty] ik_norm_id[OF nov])

  have s5: "cstep ?gs inc_g
              (Statement 0, enter_state ?gs (s((STR ''Glocal'') := 1)), [(Statement 4, None, s((STR ''Glocal'') := 1))])
              (Statement 1, (enter_state ?gs (s((STR ''Glocal'') := 1)))((STR ''counter'') := s (STR ''counter'') + 1),
               [(Statement 4, None, s((STR ''Glocal'') := 1))])"
    by (rule cstep.Intra[OF e5]) (simp add: inc_at_glocal del: inc_ty_is_default)
  have s6: "cstep ?gs inc_g
              (Statement 1, (enter_state ?gs (s((STR ''Glocal'') := 1)))((STR ''counter'') := s (STR ''counter'') + 1),
               [(Statement 4, None, s((STR ''Glocal'') := 1))])
              (FunctionResult (STR ''p''), (enter_state ?gs (s((STR ''Glocal'') := 1)))((STR ''counter'') := s (STR ''counter'') + 1),
               [(Statement 4, None, s((STR ''Glocal'') := 1))])"
    by (rule cstep.Intra[OF e6]) (auto simp: ret_var_def)
  have s7: "cstep ?gs inc_g
              (FunctionResult (STR ''p''), (enter_state ?gs (s((STR ''Glocal'') := 1)))((STR ''counter'') := s (STR ''counter'') + 1),
               [(Statement 4, None, s((STR ''Glocal'') := 1))])
              (Statement 4, s((STR ''Glocal'') := 1, (STR ''counter'') := s (STR ''counter'') + 1), [])"
  proof -
    have ret: "cstep ?gs inc_g
                 (FunctionResult (STR ''p''),
                  (enter_state ?gs (s((STR ''Glocal'') := 1)))((STR ''counter'') := s (STR ''counter'') + 1),
                  [(Statement 4, None, s((STR ''Glocal'') := 1))])
                 (Statement 4,
                  combine_collect ?gs None (s((STR ''Glocal'') := 1))
                    ((enter_state ?gs (s((STR ''Glocal'') := 1)))((STR ''counter'') := s (STR ''counter'') + 1)), [])"
      by (rule cstep.Return)
    have eq: "combine_collect ?gs None (s((STR ''Glocal'') := 1))
                ((enter_state ?gs (s((STR ''Glocal'') := 1)))((STR ''counter'') := s (STR ''counter'') + 1))
              = s((STR ''Glocal'') := 1, (STR ''counter'') := s (STR ''counter'') + 1)"
      by (simp add: combine_collect_None combine_after_enter_global_assign_declared[OF g] fun_upd_twist)
    show ?thesis using ret eq by simp
  qed
  have s8: "cstep ?gs inc_g (Statement 4, s((STR ''Glocal'') := 1, (STR ''counter'') := s (STR ''counter'') + 1), [])
              (FunctionResult (STR ''main''), s((STR ''Glocal'') := 1, (STR ''counter'') := s (STR ''counter'') + 1), [])"
    by (rule cstep.Intra[OF e7]) (auto simp: ret_var_def)
  from s1 s2 s3 s4 s5 s6 s7 s8 show ?thesis
    by (meson star.step star_step1)
qed

end
