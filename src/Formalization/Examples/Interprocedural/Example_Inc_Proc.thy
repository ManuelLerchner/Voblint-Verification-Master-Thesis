section \<open>Example support: global increment procedure\<close>

theory Example_Inc_Proc
  imports "Voblint_CFG.CFG_Collect_Runs" "Voblint_IMP2.IMP2_Notation"
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
    and "prog_table inc_program = (\<lambda>_. None)(''p'' := Some (proc_decl_legacy (Assign ''Gx'' (Plus (V ''Gx'') (N 1)))))"
    and "prog_main inc_program = Call None ''p'' []"
  by (simp_all add: inc_program_def)

definition inc_g :: cfg where
  "inc_g = compile_prog (prog_table inc_program) (prog_procs inc_program) (prog_main inc_program)"

lemma inc_g_eq_compile:
  "inc_g = compile_prog inc_pi [''p''] (Call None ''p'' [])"
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

lemma pcall_global_increment_cfg_collect:
  fixes s :: store
  shows "s(''Gx'' := s ''Gx'' + 1) \<in> cfg_collect inc_g {s} (cfg_exit inc_g)"
proof -
  let ?g = inc_g and ?S = "{s}"
    and ?t = "s(''Gx'' := s ''Gx'' + 1)"
  have entry: "{s} \<subseteq> cfg_collect ?g ?S (cfg_entry ?g)"
    using cfg_collect_entry by simp
  have s_at_call: "s \<in> cfg_collect ?g ?S 2"
    using entry inc_g_structure(1) by auto
  have en: "(2, EA_Enter [] [], 0) \<in> edges ?g"
    using inc_g_structure by simp
  have enter: "enter_state s \<in> cfg_collect ?g ?S 0"
  proof (rule cfg_collect_edge[OF en])
    show "enter_state s \<in> edge_collect (EA_Enter [] []) (cfg_collect ?g ?S 2)"
      using s_at_call by (auto simp: bind_formals_def)
  qed
  have asg: "(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1) \<in> edges ?g"
    using inc_g_structure by simp
  let ?body_store = "(enter_state s)(''Gx'' := s ''Gx'' + 1)"
  have edge_asg: "?body_store \<in> edge_collect (EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)))
                  (cfg_collect ?g ?S 0)"
  proof -
    have mem: "(enter_state s)(''Gx'' := aval (Plus (V ''Gx'') (N 1)) (enter_state s))
      \<in> edge_collect (EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1))) (cfg_collect ?g ?S 0)"
      using enter edge_collect_assign_enter_state by blast
    show ?thesis using mem aval_plus_gx_on_enter by simp
  qed
  have body_store: "?body_store \<in> cfg_collect ?g ?S 1"
    using cfg_collect_edge[OF asg edge_asg] by simp
  have comb: "(2, 1, 3, None) \<in> combines ?g"
    using inc_g_structure by simp
  have g: "is_global ''Gx''"
    by (simp add: is_global_def)
  have "?t = <s|?body_store>"
    using combine_after_enter_global_assign[OF g] by (simp add: enter_state_def)
  have combined0: "combine_collect None s ?body_store \<in> cfg_collect ?g ?S 3"
    using cfg_collect_combine[OF comb refl s_at_call body_store] by simp
  have combined: "<s|?body_store> \<in> cfg_collect ?g ?S 3"
    using combined0 by (simp add: combine_collect_def)
  show ?thesis
    using combined `?t = <s|?body_store>`
    by (simp add: inc_g_structure(2))
qed

lemma cfg_runs_to_pcall_global_increment:
  fixes s :: store
  shows "cfg_runs_to inc_pi [''p''] (Call None ''p'' []) s (s(''Gx'' := s ''Gx'' + 1))"
proof -
  have "s(''Gx'' := s ''Gx'' + 1)
      \<in> cfg_collect inc_g {s} (cfg_exit inc_g)"
    using pcall_global_increment_cfg_collect by simp
  thus ?thesis
    unfolding cfg_runs_to_def
    by (auto simp: inc_g_eq_compile Let_def)
qed

lemma pcompletes_inc_pcall:
  fixes s :: store
  shows "pcompletes inc_pi (Call None ''p'' []) s (s(''Gx'' := s ''Gx'' + 1))"
proof -
  let ?body = "Assign ''Gx'' (Plus (V ''Gx'') (N 1))"
  have g: "is_global ''Gx''" by (simp add: is_global_def)
  have run: "pcompletes inc_pi (Call None ''p'' []) s
                (<s | (enter_state s)(''Gx'' := s ''Gx'' + 1)>)"
  proof (rule pcompletes_Legacy_Call[where c = ?body])
    show "inc_pi ''p'' = Some (proc_decl_legacy ?body)"
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
