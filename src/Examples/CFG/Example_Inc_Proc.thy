section \<open>Example support: global increment procedure\<close>

theory Example_Inc_Proc
  imports "Voblint_CFG.CFG_Transfer" "Voblint_CFG.CFG_Prune" "Voblint_VIMP.VIMP_Notation"
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

lemma aval_plus_gx_on_enter:
  "aval (Plus (V ''Gx'') (N 1)) (enter_state is_global s) = s ''Gx'' + 1"
  by (simp add: enter_state_def is_global_def)

lemma combine_after_enter_global_assign:
  assumes "is_global x"
  shows "combine_states is_global s ((enter_state is_global s)(x := v)) = s(x := v)"
  using assms by (auto simp: combine_states_def enter_state_def)



lemma pcompletes_inc_pcall:
  fixes s :: store
  shows "pcompletes is_global inc_pi (imp \<lbrakk> p() \<rbrakk>) s (s(''Gx'' := s ''Gx'' + 1))"
proof -
  let ?body = "imp \<lbrakk> Gx := Gx + 1 \<rbrakk>"
  have g: "is_global ''Gx''" by (simp add: is_global_def)
  have run: "pcompletes is_global inc_pi (imp \<lbrakk> p() \<rbrakk>) s
                (combine_states is_global s ((enter_state is_global s)(''Gx'' := s ''Gx'' + 1)))"
  proof (rule pcompletes_Call_parameterless[where c = ?body])
    show "inc_pi ''p'' = Some (proc_decl_of [] ?body)"
      by (simp add: inc_pi_def inc_program_parts prog_main_name_def)
    show "pcompletes is_global inc_pi ?body (enter_state is_global s)
             ((enter_state is_global s)(''Gx'' := s ''Gx'' + 1))"
    proof -
      have "pcompletes is_global inc_pi ?body (enter_state is_global s)
               ((enter_state is_global s)
                 (''Gx'' := aval (Plus (V ''Gx'') (N 1)) (enter_state is_global s)))"
        by (rule pcompletes_assign)
      thus ?thesis using aval_plus_gx_on_enter by simp
    qed
  qed
  moreover have
    "combine_states is_global s ((enter_state is_global s)(''Gx'' := s ''Gx'' + 1))
       = s(''Gx'' := s ''Gx'' + 1)"
    using combine_after_enter_global_assign[OF g] by simp
  ultimately show ?thesis by simp
qed

end
