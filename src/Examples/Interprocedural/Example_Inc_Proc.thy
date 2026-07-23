section \<open>Example support: global increment procedure\<close>

theory Example_Inc_Proc
  imports "Voblint_CFG.CFG_Transfer" "Voblint_IMP2.IMP2_Notation"
begin

text \<open>
  Shared witness program: a single procedure p increments the global Gx, and
  the main command calls p once.  Examples reuse this theory when they need a
  small interprocedural program with a concrete run-to-collecting witness.
\<close>

definition inc_program :: imp_prog where
  "inc_program = program {
     int Gx;
     void p() { Gx := Gx + 1 }
     void main() { p() }
   }"

definition inc_pi :: proc_table where
  "inc_pi = prog_table inc_program"

lemma inc_program_parts:
  shows "prog_procs inc_program = [''p'']"
    and "prog_table inc_program = map_of [(''p'', proc_decl_of [] (imp \<lbrakk> Gx := Gx + 1 \<rbrakk>))]"
    and "prog_main inc_program = imp \<lbrakk> p() \<rbrakk>"
  by (simp_all add: inc_program_def)

definition inc_g :: cfg where
  "inc_g = compile_prog (prog_table inc_program) (prog_procs inc_program) ''main'' (prog_main inc_program)"

lemma inc_g_eq_compile:
  "inc_g = compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)"
  by (simp add: inc_g_def inc_pi_def inc_program_parts)

lemma inc_g_full:
  "inc_g = mk_cfg 2 3
     {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1),
      (2, EA_Enter [] [], 0)}
     {(2, 1, 3, None)}"
  by eval

lemma inc_g_structure:
  shows "cfg_entry inc_g = 2"
    and "cfg_exit inc_g = 3"
    and "edges inc_g =
       {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1),
        (2, EA_Enter [] [], 0)}"
    and "combines inc_g = {(2, 1, 3, None)}"
  by (simp_all add: inc_g_full)

lemma edge_collect_assign_enter_state:
  fixes s :: store and x :: vname and a :: aexp
  assumes "enter_state s \<in> S"
  shows "(enter_state s)(x := aval a (enter_state s)) \<in> edge_collect (EA_Assign x a) S"
  using assms by auto

lemma aval_plus_gx_on_enter:
  "aval (Plus (V ''Gx'') (N 1)) (enter_state s) = s ''Gx'' + 1"
  by (simp add: enter_state_def is_global_def)

lemma combine_after_enter_global_assign:
  assumes "is_global x"
  shows "<s | (enter_state s)(x := v)> = s(x := v)"
  using assms by (auto simp: combine_states_def enter_state_def)



lemma pcompletes_inc_pcall:
  fixes s :: store
  shows "pcompletes inc_pi (imp \<lbrakk> p() \<rbrakk>) s (s(''Gx'' := s ''Gx'' + 1))"
proof -
  let ?body = "imp \<lbrakk> Gx := Gx + 1 \<rbrakk>"
  have g: "is_global ''Gx''" by (simp add: is_global_def)
  have run: "pcompletes inc_pi (imp \<lbrakk> p() \<rbrakk>) s
                (<s | (enter_state s)(''Gx'' := s ''Gx'' + 1)>)"
  proof (rule pcompletes_Call_parameterless[where c = ?body])
    show "inc_pi ''p'' = Some (proc_decl_of [] ?body)"
      by (simp add: inc_pi_def inc_program_parts)
    show "pcompletes inc_pi ?body (enter_state s)
             ((enter_state s)(''Gx'' := s ''Gx'' + 1))"
    proof -
      have "pcompletes inc_pi ?body (enter_state s)
               ((enter_state s)(''Gx'' := aval (Plus (V ''Gx'') (N 1)) (enter_state s)))"
        by (rule pcompletes_assign)
      thus ?thesis using aval_plus_gx_on_enter by simp
    qed
  qed
  moreover have "<s | (enter_state s)(''Gx'' := s ''Gx'' + 1)> = s(''Gx'' := s ''Gx'' + 1)"
    using combine_after_enter_global_assign[OF g] by simp
  ultimately show ?thesis by simp
qed

end
