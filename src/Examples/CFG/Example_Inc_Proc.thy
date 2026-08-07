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
     global counter;
     void p() { counter := counter + 1 }
     void main() { Glocal := 1; p() }
   }"

definition inc_pi :: proc_table where
  "inc_pi = prog_table inc_program"

lemma inc_program_parts:
  shows "prog_procs inc_program = [''p'']"
    and "prog_table inc_program =
           [''p'' \<mapsto> proc_decl_of [] (imp \<lbrakk> counter := counter + 1 \<rbrakk>),
            prog_main_name \<mapsto> proc_decl_of [] (imp \<lbrakk> Glocal := 1 ; p() \<rbrakk>)]"
    and "prog_main inc_program = imp \<lbrakk> Glocal := 1 ; p() \<rbrakk>"
  by (simp_all add: inc_program_def)

text \<open>\<open>declared_global_vars\<close> for the concrete program: the entry point where the
  declaration-driven classifier meets a real declared list. \<open>Glocal\<close> is
  undeclared and therefore local despite its spelling; \<open>counter\<close> is declared
  global despite carrying no naming hint at all.\<close>
lemma inc_program_declared_global_vars [simp]:
  "declared_global_vars inc_program = [''counter'']"
  by (simp add: inc_program_def)

lemma inc_program_counter_global [simp]: "declared_global inc_program ''counter''"
  by simp

lemma inc_program_glocal_not_global [simp]: "\<not> declared_global inc_program ''Glocal''"
  by simp

definition inc_g :: cfg where
  "inc_g = compile_prog (prog_table inc_program) (prog_procs inc_program) ''main'' (prog_main inc_program)"

lemma inc_g_eq_compile:
  "inc_g = compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> Glocal := 1 ; p() \<rbrakk>)"
  by (simp add: inc_g_def inc_pi_def inc_program_parts)

lemma edge_collect_assign_enter_state:
  fixes s :: store and x :: vname and a :: aexp and gs :: "vname \<Rightarrow> bool"
  assumes "enter_state gs s \<in> S"
  shows "(enter_state gs s)(x := aval a (enter_state gs s))
           \<in> edge_collect (EA_Assign x a) S"
  using assms by auto

lemma aval_plus_counter_on_enter_declared:
  "aval (Plus (V ''counter'') (N 1)) (enter_state (declared_global inc_program) s) = s ''counter'' + 1"
  by (simp add: enter_state_def)

lemma combine_after_enter_global_assign_declared:
  assumes "declared_global inc_program x"
  shows "combine_states (declared_global inc_program) s
           ((enter_state (declared_global inc_program) s)(x := v)) = s(x := v)"
  using assms by (auto simp: combine_states_def enter_state_def)

text \<open>
  The call completion fact for \<^const>\<open>inc_program\<close>, restated with the declaration-driven
  classifier \<^term>\<open>declared_global inc_program\<close> as the concrete instance of the generic
  classifier argument.  The instantiation is the only thing that changed:
  \<^const>\<open>pstep\<close>/\<^const>\<open>pcompletes\<close> take \<^term>\<open>gs\<close> as an explicit argument, so this proof
  needed no change to \<open>pcompletes_Call_parameterless\<close> or \<open>pcompletes_assign\<close>
  themselves, only to which classifier each is applied at.
\<close>
lemma pcompletes_inc_pcall_declared:
  fixes s :: store
  shows "pcompletes (declared_global inc_program) inc_pi (imp \<lbrakk> p() \<rbrakk>) s
           (s(''counter'' := s ''counter'' + 1))"
proof -
  let ?body = "imp \<lbrakk> counter := counter + 1 \<rbrakk>"
  have g: "declared_global inc_program ''counter''" by simp
  have run: "pcompletes (declared_global inc_program) inc_pi (imp \<lbrakk> p() \<rbrakk>) s
                (combine_states (declared_global inc_program) s
                  ((enter_state (declared_global inc_program) s)(''counter'' := s ''counter'' + 1)))"
  proof (rule pcompletes_Call_parameterless[where c = ?body])
    show "inc_pi ''p'' = Some (proc_decl_of [] ?body)"
      by (simp add: inc_pi_def inc_program_parts prog_main_name_def)
    show "pcompletes (declared_global inc_program) inc_pi ?body
             (enter_state (declared_global inc_program) s)
             ((enter_state (declared_global inc_program) s)(''counter'' := s ''counter'' + 1))"
    proof -
      have "pcompletes (declared_global inc_program) inc_pi ?body
               (enter_state (declared_global inc_program) s)
               ((enter_state (declared_global inc_program) s)
                 (''counter'' := aval (Plus (V ''counter'') (N 1)) (enter_state (declared_global inc_program) s)))"
        by (rule pcompletes_assign)
      thus ?thesis using aval_plus_counter_on_enter_declared by simp
    qed
  qed
  moreover have
    "combine_states (declared_global inc_program) s
       ((enter_state (declared_global inc_program) s)(''counter'' := s ''counter'' + 1))
       = s(''counter'' := s ''counter'' + 1)"
    using combine_after_enter_global_assign_declared[OF g] by simp
  ultimately show ?thesis by simp
qed

lemma prog_pcompletes_inc_pcall:
  fixes s :: store
  shows "prog_pcompletes inc_program (imp \<lbrakk> p() \<rbrakk>) s
          (s(''counter'' := s ''counter'' + 1))"
proof -
  have storage:
    "storage_global inc_program prog_main_name = declared_global inc_program"
    by (rule ext) simp
  show ?thesis
    using pcompletes_inc_pcall_declared
    unfolding prog_pcompletes_def inc_pi_def storage by simp
qed

text \<open>
  The same regression one layer down, at the compiled CFG: \<^const>\<open>cstep\<close> takes
  \<^term>\<open>gs\<close> explicitly (the compiler-layer counterpart of \<^const>\<open>pstep\<close>'s classifier
  parameter above), so \<^const>\<open>inc_g\<close> --- unchanged since it is compiled once from \<^term>\<open>inc_program\<close>
  and carries no classifier of its own --- executes identically under
  \<^term>\<open>declared_global inc_program\<close>.  The eight \<^const>\<open>cstep\<close> transitions retrace
  \<open>inc_g\<close>'s edges: \<open>main\<close>'s entry \<open>Nop\<close>, the \<open>Glocal\<close> assignment, the call into
  \<open>p\<close>, \<open>p\<close>'s entry \<open>Nop\<close>, the increment assignment, \<open>p\<close>'s return, the call's
  resume, and \<open>main\<close>'s return. \<open>Glocal\<close>'s value survives untouched through the
  call, since it plays no role in \<open>p\<close>'s classification-driven local/global
  split.
\<close>
lemma cstep_inc_pcall_declared:
  fixes s :: store
  shows "star (cstep (declared_global inc_program) inc_g) (FunctionEntry ''main'', s, [])
           (FunctionResult ''main'', s(''Glocal'' := 1, ''counter'' := s ''counter'' + 1), [])"
proof -
  let ?gs = "declared_global inc_program"
  have e1: "(FunctionEntry ''main'', EA_Nop, Statement 2) \<in> intra inc_g"
    and e2: "(Statement 2, EA_Assign ''Glocal'' (N 1), Statement 3) \<in> intra inc_g"
    and e3: "(Statement 3, CallEdge None [] [], FunctionEntry ''p'', Statement 4) \<in> calls inc_g"
    and e4: "(FunctionEntry ''p'', EA_Nop, Statement 0) \<in> intra inc_g"
    and e5: "(Statement 0, EA_Assign ''counter'' (Plus (V ''counter'') (N 1)), Statement 1) \<in> intra inc_g"
    and e6: "(Statement 1, EA_Ret None ''p'', FunctionResult ''p'') \<in> intra inc_g"
    and e7: "(Statement 4, EA_Ret None ''main'', FunctionResult ''main'') \<in> intra inc_g"
    by eval+
  have g: "?gs ''counter''" by simp
  have s1: "cstep ?gs inc_g (FunctionEntry ''main'', s, []) (Statement 2, s, [])"
    by (rule cstep.Intra[OF e1]) simp
  have s2: "cstep ?gs inc_g (Statement 2, s, []) (Statement 3, s(''Glocal'' := 1), [])"
    by (rule cstep.Intra[OF e2]) simp
  have s3: "cstep ?gs inc_g (Statement 3, s(''Glocal'' := 1), [])
              (FunctionEntry ''p'', enter_state ?gs (s(''Glocal'' := 1)),
               [(Statement 4, None, s(''Glocal'' := 1))])"
    using cstep.Call[OF e3] by simp
  have s4: "cstep ?gs inc_g
              (FunctionEntry ''p'', enter_state ?gs (s(''Glocal'' := 1)), [(Statement 4, None, s(''Glocal'' := 1))])
              (Statement 0, enter_state ?gs (s(''Glocal'' := 1)), [(Statement 4, None, s(''Glocal'' := 1))])"
    by (rule cstep.Intra[OF e4]) simp
  have s5: "cstep ?gs inc_g
              (Statement 0, enter_state ?gs (s(''Glocal'' := 1)), [(Statement 4, None, s(''Glocal'' := 1))])
              (Statement 1, (enter_state ?gs (s(''Glocal'' := 1)))(''counter'' := s ''counter'' + 1),
               [(Statement 4, None, s(''Glocal'' := 1))])"
    by (rule cstep.Intra[OF e5]) (simp add: enter_state_def)
  have s6: "cstep ?gs inc_g
              (Statement 1, (enter_state ?gs (s(''Glocal'' := 1)))(''counter'' := s ''counter'' + 1),
               [(Statement 4, None, s(''Glocal'' := 1))])
              (FunctionResult ''p'', (enter_state ?gs (s(''Glocal'' := 1)))(''counter'' := s ''counter'' + 1),
               [(Statement 4, None, s(''Glocal'' := 1))])"
    by (rule cstep.Intra[OF e6]) (auto simp: ret_var_def)
  have s7: "cstep ?gs inc_g
              (FunctionResult ''p'', (enter_state ?gs (s(''Glocal'' := 1)))(''counter'' := s ''counter'' + 1),
               [(Statement 4, None, s(''Glocal'' := 1))])
              (Statement 4, s(''Glocal'' := 1, ''counter'' := s ''counter'' + 1), [])"
  proof -
    have ret: "cstep ?gs inc_g
                 (FunctionResult ''p'',
                  (enter_state ?gs (s(''Glocal'' := 1)))(''counter'' := s ''counter'' + 1),
                  [(Statement 4, None, s(''Glocal'' := 1))])
                 (Statement 4,
                  combine_collect ?gs None (s(''Glocal'' := 1))
                    ((enter_state ?gs (s(''Glocal'' := 1)))(''counter'' := s ''counter'' + 1)), [])"
      by (rule cstep.Return)
    have eq: "combine_collect ?gs None (s(''Glocal'' := 1))
                ((enter_state ?gs (s(''Glocal'' := 1)))(''counter'' := s ''counter'' + 1))
              = s(''Glocal'' := 1, ''counter'' := s ''counter'' + 1)"
      by (simp add: combine_collect_None combine_after_enter_global_assign_declared[OF g] fun_upd_twist)
    show ?thesis using ret eq by simp
  qed
  have s8: "cstep ?gs inc_g (Statement 4, s(''Glocal'' := 1, ''counter'' := s ''counter'' + 1), [])
              (FunctionResult ''main'', s(''Glocal'' := 1, ''counter'' := s ''counter'' + 1), [])"
    by (rule cstep.Intra[OF e7]) (auto simp: ret_var_def)
  from s1 s2 s3 s4 s5 s6 s7 s8 show ?thesis
    by (meson star.step star_step1)
qed

end
