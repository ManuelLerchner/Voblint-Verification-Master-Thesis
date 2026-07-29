section \<open>Example support: global increment procedure\<close>

theory Example_Inc_Proc
  imports "Voblint_CFG.CFG_Transfer" "Voblint_CFG.CFG_Prune" "Voblint_VIMP.VIMP_Notation"
    "Voblint_CFG.Located_Exec"
begin

text \<open>
  Shared witness program: a single procedure p increments the global Gx, and
  the main command calls p once.  Examples reuse this theory when they need a
  small interprocedural program with a concrete run-to-collecting witness.
\<close>

definition inc_program :: imp_prog where
  "inc_program = program {
     global Gx;
     void p() { Gx := Gx + 1 }
     void main() { p() }
   }"

definition inc_pi :: proc_table where
  "inc_pi = prog_table inc_program"

lemma inc_program_parts:
  shows "prog_procs inc_program = [''p'']"
    and "prog_table inc_program =
           [''p'' \<mapsto> proc_decl_of [] (imp \<lbrakk> Gx := Gx + 1 \<rbrakk>),
            prog_main_name \<mapsto> proc_decl_of [] (imp \<lbrakk> p() \<rbrakk>)]"
    and "prog_main inc_program = imp \<lbrakk> p() \<rbrakk>"
  by (simp_all add: inc_program_def)

text \<open>\<open>declared_global_vars\<close> for the concrete program: the entry point where the
  migration's declaration-driven classifier meets a real declared list.\<close>
lemma inc_program_declared_global_vars [simp]:
  "declared_global_vars inc_program = [''Gx'']"
  by (simp add: inc_program_def)

definition inc_g :: cfg where
  "inc_g = compile_prog (prog_table inc_program) (prog_procs inc_program) ''main'' (prog_main inc_program)"

lemma inc_g_eq_compile:
  "inc_g = compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)"
  by (simp add: inc_g_def inc_pi_def inc_program_parts)

lemma inc_g_full:
  "inc_g =
     \<lparr> intra =
         {(FunctionEntry ''p'', EA_Nop, Statement 0),
          (Statement 0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), Statement 1),
          (Statement 1, EA_Ret None ''p'', FunctionResult ''p''),
          (FunctionEntry ''main'', EA_Nop, Statement 2),
          (Statement 3, EA_Ret None ''main'', FunctionResult ''main'')},
       calls = {(Statement 2, CallEdge None [] [], FunctionEntry ''p'', Statement 3)},
       cfg_entry = FunctionEntry ''main'' \<rparr>"
  by eval

lemma inc_g_structure:
  shows "cfg_entry inc_g = FunctionEntry ''main''"
    and "cfg_exit inc_g = FunctionResult ''main''"
    and "intra inc_g =
       {(FunctionEntry ''p'', EA_Nop, Statement 0),
        (Statement 0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), Statement 1),
        (Statement 1, EA_Ret None ''p'', FunctionResult ''p''),
        (FunctionEntry ''main'', EA_Nop, Statement 2),
        (Statement 3, EA_Ret None ''main'', FunctionResult ''main'')}"
    and "calls inc_g = {(Statement 2, CallEdge None [] [], FunctionEntry ''p'', Statement 3)}"
  by (simp_all add: inc_g_full cfg_exit_def)

lemma edge_collect_assign_enter_state:
  fixes s :: store and x :: vname and a :: aexp
  assumes "enter_state is_global s \<in> S"
  shows "(enter_state is_global s)(x := aval a (enter_state is_global s))
           \<in> edge_collect (EA_Assign x a) S"
  using assms by auto

lemma aval_plus_gx_on_enter_declared:
  "aval (Plus (V ''Gx'') (N 1)) (enter_state (declared_global inc_program) s) = s ''Gx'' + 1"
  by (simp add: enter_state_def)

lemma combine_after_enter_global_assign_declared:
  assumes "declared_global inc_program x"
  shows "combine_states (declared_global inc_program) s
           ((enter_state (declared_global inc_program) s)(x := v)) = s(x := v)"
  using assms by (auto simp: combine_states_def enter_state_def)

text \<open>
  The call completion fact for \<^const>\<open>inc_program\<close>, restated with the declaration-driven
  classifier \<^term>\<open>declared_global inc_program\<close> in place of the prefix-based
  \<^const>\<open>is_global\<close>.  The instantiation is the only thing that changed:
  \<^const>\<open>pstep\<close>/\<^const>\<open>pcompletes\<close> take \<^term>\<open>gs\<close> as an explicit argument, so this proof
  needed no change to \<open>pcompletes_Call_parameterless\<close> or \<open>pcompletes_assign\<close>
  themselves, only to which classifier each is applied at.
\<close>
lemma pcompletes_inc_pcall_declared:
  fixes s :: store
  shows "pcompletes (declared_global inc_program) inc_pi (imp \<lbrakk> p() \<rbrakk>) s
           (s(''Gx'' := s ''Gx'' + 1))"
proof -
  let ?body = "imp \<lbrakk> Gx := Gx + 1 \<rbrakk>"
  have g: "declared_global inc_program ''Gx''" by simp
  have run: "pcompletes (declared_global inc_program) inc_pi (imp \<lbrakk> p() \<rbrakk>) s
                (combine_states (declared_global inc_program) s
                  ((enter_state (declared_global inc_program) s)(''Gx'' := s ''Gx'' + 1)))"
  proof (rule pcompletes_Call_parameterless[where c = ?body])
    show "inc_pi ''p'' = Some (proc_decl_of [] ?body)"
      by (simp add: inc_pi_def inc_program_parts prog_main_name_def)
    show "pcompletes (declared_global inc_program) inc_pi ?body
             (enter_state (declared_global inc_program) s)
             ((enter_state (declared_global inc_program) s)(''Gx'' := s ''Gx'' + 1))"
    proof -
      have "pcompletes (declared_global inc_program) inc_pi ?body
               (enter_state (declared_global inc_program) s)
               ((enter_state (declared_global inc_program) s)
                 (''Gx'' := aval (Plus (V ''Gx'') (N 1)) (enter_state (declared_global inc_program) s)))"
        by (rule pcompletes_assign)
      thus ?thesis using aval_plus_gx_on_enter_declared by simp
    qed
  qed
  moreover have
    "combine_states (declared_global inc_program) s
       ((enter_state (declared_global inc_program) s)(''Gx'' := s ''Gx'' + 1))
       = s(''Gx'' := s ''Gx'' + 1)"
    using combine_after_enter_global_assign_declared[OF g] by simp
  ultimately show ?thesis by simp
qed

text \<open>
  The same regression one layer down, at the compiled CFG: \<^const>\<open>cstep\<close> now takes
  \<^term>\<open>gs\<close> explicitly (the compiler-layer counterpart of the \<^const>\<open>pstep\<close> migration
  above), so \<^const>\<open>inc_g\<close> --- unchanged since it is compiled once from \<^term>\<open>inc_program\<close>
  and carries no classifier of its own --- executes identically under
  \<^term>\<open>declared_global inc_program\<close>.  The six \<^const>\<open>cstep\<close> transitions retrace
  \<open>inc_g_structure\<close>'s edges: \<open>main\<close>'s entry \<open>Nop\<close>, the call into \<open>p\<close>, \<open>p\<close>'s entry
  \<open>Nop\<close>, the increment assignment, \<open>p\<close>'s return, the call's resume, and \<open>main\<close>'s return.
\<close>
lemma cstep_inc_pcall_declared:
  fixes s :: store
  shows "star (cstep (declared_global inc_program) inc_g) (FunctionEntry ''main'', s, [])
           (FunctionResult ''main'', s(''Gx'' := s ''Gx'' + 1), [])"
proof -
  let ?gs = "declared_global inc_program"
  have e1: "(FunctionEntry ''main'', EA_Nop, Statement 2) \<in> intra inc_g"
    and e2: "(Statement 2, CallEdge None [] [], FunctionEntry ''p'', Statement 3) \<in> calls inc_g"
    and e3: "(FunctionEntry ''p'', EA_Nop, Statement 0) \<in> intra inc_g"
    and e4: "(Statement 0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), Statement 1) \<in> intra inc_g"
    and e5: "(Statement 1, EA_Ret None ''p'', FunctionResult ''p'') \<in> intra inc_g"
    and e6: "(Statement 3, EA_Ret None ''main'', FunctionResult ''main'') \<in> intra inc_g"
    by (simp_all add: inc_g_structure)
  have g: "?gs ''Gx''" by simp
  have s1: "cstep ?gs inc_g (FunctionEntry ''main'', s, []) (Statement 2, s, [])"
    by (rule cstep.Intra[OF e1]) simp
  have s2: "cstep ?gs inc_g (Statement 2, s, [])
              (FunctionEntry ''p'', enter_state ?gs s, [(Statement 3, None, s)])"
    using cstep.Call[OF e2] by simp
  have s3: "cstep ?gs inc_g (FunctionEntry ''p'', enter_state ?gs s, [(Statement 3, None, s)])
              (Statement 0, enter_state ?gs s, [(Statement 3, None, s)])"
    by (rule cstep.Intra[OF e3]) simp
  have s4: "cstep ?gs inc_g (Statement 0, enter_state ?gs s, [(Statement 3, None, s)])
              (Statement 1, (enter_state ?gs s)(''Gx'' := s ''Gx'' + 1), [(Statement 3, None, s)])"
    by (rule cstep.Intra[OF e4]) (simp add: enter_state_def)
  have s5: "cstep ?gs inc_g
              (Statement 1, (enter_state ?gs s)(''Gx'' := s ''Gx'' + 1), [(Statement 3, None, s)])
              (FunctionResult ''p'', (enter_state ?gs s)(''Gx'' := s ''Gx'' + 1), [(Statement 3, None, s)])"
    by (rule cstep.Intra[OF e5]) (auto simp: ret_var_def)
  have s6: "cstep ?gs inc_g
              (FunctionResult ''p'', (enter_state ?gs s)(''Gx'' := s ''Gx'' + 1), [(Statement 3, None, s)])
              (Statement 3, s(''Gx'' := s ''Gx'' + 1), [])"
  proof -
    have ret: "cstep ?gs inc_g
                 (FunctionResult ''p'', (enter_state ?gs s)(''Gx'' := s ''Gx'' + 1), [(Statement 3, None, s)])
                 (Statement 3, combine_collect ?gs None s ((enter_state ?gs s)(''Gx'' := s ''Gx'' + 1)), [])"
      by (rule cstep.Return)
    have eq: "combine_collect ?gs None s ((enter_state ?gs s)(''Gx'' := s ''Gx'' + 1)) = s(''Gx'' := s ''Gx'' + 1)"
      by (simp add: combine_collect_None combine_after_enter_global_assign_declared[OF g])
    show ?thesis using ret eq by simp
  qed
  have s7: "cstep ?gs inc_g (Statement 3, s(''Gx'' := s ''Gx'' + 1), [])
              (FunctionResult ''main'', s(''Gx'' := s ''Gx'' + 1), [])"
    by (rule cstep.Intra[OF e6]) (auto simp: ret_var_def)
  from s1 s2 s3 s4 s5 s6 s7 show ?thesis
    by (meson star.step star_step1)
qed

end
