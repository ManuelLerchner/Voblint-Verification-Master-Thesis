theory Example_VIMP_Proc_Regression
  imports "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Examples: native activation semantics\<close>

theorem caller_local_isolated:
  assumes p: "\<Pi> pf = Some (proc_decl_of [] (imp \<lbrakk> x := 9 \<rbrakk>))"
  shows "\<exists>t. pcompletes is_global \<Pi> (Seq (Assign ''x'' (N 5)) (Call None pf [])) s0 t
             \<and> t ''x'' = 5"
proof -
  let ?s1 = "s0(''x'' := 5)"
  have a: "pcompletes is_global \<Pi> (imp \<lbrakk> x := 5 \<rbrakk>) s0 ?s1"
  proof -
    have "pcompletes is_global \<Pi> (imp \<lbrakk> x := 5 \<rbrakk>) s0
            (s0(''x'' := aval (N 5) s0))" by (rule pcompletes_assign)
    thus ?thesis by simp
  qed
  have body: "pcompletes is_global \<Pi> (imp \<lbrakk> x := 9 \<rbrakk>)
               (enter_state is_global ?s1) ((enter_state is_global ?s1)(''x'' := 9))"
  proof -
    have "pcompletes is_global \<Pi> (imp \<lbrakk> x := 9 \<rbrakk>) (enter_state is_global ?s1)
            ((enter_state is_global ?s1)(''x'' := aval (N 9) (enter_state is_global ?s1)))"
      by (rule pcompletes_assign)
    thus ?thesis by simp
  qed
  have call: "pcompletes is_global \<Pi> (Call None pf []) ?s1
                (combine_states is_global ?s1 ((enter_state is_global ?s1)(''x'' := 9)))"
    by (rule pcompletes_Call_parameterless[OF p body])
  have seq: "pcompletes is_global \<Pi> (Seq (imp \<lbrakk> x := 5 \<rbrakk>) (Call None pf [])) s0
               (combine_states is_global ?s1 ((enter_state is_global ?s1)(''x'' := 9)))"
    using pcompletes_Seq[OF a call] .
  have "(combine_states is_global ?s1 ((enter_state is_global ?s1)(''x'' := 9))) ''x'' = 5"
    by (simp add: is_global_def)
  with seq show ?thesis by blast
qed

theorem global_propagated:
  assumes p: "\<Pi> pf = Some (proc_decl_of [] (imp \<lbrakk> Gg := 9 \<rbrakk>))"
  shows "\<exists>t. pcompletes is_global \<Pi> (Call None pf []) s0 t \<and> t ''Gg'' = 9"
proof -
  have body: "pcompletes is_global \<Pi> (imp \<lbrakk> Gg := 9 \<rbrakk>)
               (enter_state is_global s0) ((enter_state is_global s0)(''Gg'' := 9))"
  proof -
    have "pcompletes is_global \<Pi> (imp \<lbrakk> Gg := 9 \<rbrakk>) (enter_state is_global s0)
            ((enter_state is_global s0)(''Gg'' := aval (N 9) (enter_state is_global s0)))"
      by (rule pcompletes_assign)
    thus ?thesis by simp
  qed
  have call: "pcompletes is_global \<Pi> (Call None pf []) s0
                (combine_states is_global s0 ((enter_state is_global s0)(''Gg'' := 9)))"
    by (rule pcompletes_Call_parameterless[OF p body])
  have "(combine_states is_global s0 ((enter_state is_global s0)(''Gg'' := 9))) ''Gg'' = 9"
    by (simp add: is_global_def)
  with call show ?thesis by blast
qed

theorem return_value_propagated:
  assumes p: "\<Pi> pf = Some (proc_decl_of [] (imp \<lbrakk> return 7 \<rbrakk>))"
  shows "\<exists>t. pcompletes is_global \<Pi> (Call (Some ''x'') pf []) s0 t \<and> t ''x'' = 7"
proof -
  let ?e = "N 7"
  let ?t = "(combine_states is_global s0
              ((enter_state is_global s0)(ret_var := aval ?e (enter_state is_global s0))))
              (''x'' := aval ?e (enter_state is_global s0))"
  have call: "psteps is_global \<Pi> (Call (Some ''x'') pf [], s0, []) (imp \<lbrakk> skip \<rbrakk>, ?t, [])"
    using p by (rule call_return_completes[where x = "''x''" and s = s0 and frs = "[]"])
  have "?t ''x'' = 7" by simp
  with call show ?thesis unfolding pcompletes_def by blast
qed

lemmas early_return_skips_dead = call_return_completes
lemmas normal_fallthrough = call_return_none_completes
lemmas nested_calls_resume_caller = nested_call_return_trace

definition rec_body :: com where
  "rec_body = imp \<lbrakk>
     if (0 < Gx) {
       Gx := Gx - 1;
       r()
     } else {
       skip
     }
   \<rbrakk>"

theorem bounded_recursion_completes:
  assumes p: "\<Pi> ''r'' = Some (proc_decl_of [] rec_body)"
  shows "\<exists>t. pcompletes is_global \<Pi> (imp \<lbrakk> r() \<rbrakk>) ((\<lambda>_. 0)(''Gx'' := 1)) t \<and> t ''Gx'' = 0"
proof -
  let ?s0 = "(\<lambda>_. 0)(''Gx'' := 1)"
  let ?e0 = "enter_state is_global ?s0"
  let ?e1 = "?e0(''Gx'' := 0)"
  let ?ei = "enter_state is_global ?e1"
  have inner_guard: "\<not> bval (Less (N 0) (V ''Gx'')) ?ei"
    by (simp add: enter_state_def is_global_def)
  have inner_body: "pcompletes is_global \<Pi> rec_body ?ei ?ei"
    unfolding rec_body_def by (rule pcompletes_IfFalse[OF inner_guard pcompletes_skip])
  have inner_call: "pcompletes is_global \<Pi> (imp \<lbrakk> r() \<rbrakk>) ?e1 (combine_states is_global ?e1 ?ei)"
    by (rule pcompletes_Call_parameterless[OF p inner_body])
  have outer_guard: "bval (Less (N 0) (V ''Gx'')) ?e0"
    by (simp add: enter_state_def is_global_def)
  have dec: "pcompletes is_global \<Pi> (imp \<lbrakk> Gx := Gx - 1 \<rbrakk>) ?e0 ?e1"
  proof -
    have "pcompletes is_global \<Pi> (imp \<lbrakk> Gx := Gx - 1 \<rbrakk>) ?e0
            (?e0(''Gx'' := aval (Minus (V ''Gx'') (N 1)) ?e0))"
      by (rule pcompletes_assign)
    thus ?thesis by (simp add: enter_state_def is_global_def)
  qed
  have outer_body: "pcompletes is_global \<Pi> rec_body ?e0 (combine_states is_global ?e1 ?ei)"
    unfolding rec_body_def
    by (rule pcompletes_IfTrue[OF outer_guard pcompletes_Seq[OF dec inner_call]])
  have outer_call: "pcompletes is_global \<Pi> (imp \<lbrakk> r() \<rbrakk>) ?s0
                       (combine_states is_global ?s0 (combine_states is_global ?e1 ?ei))"
    by (rule pcompletes_Call_parameterless[OF p outer_body])
  have "(combine_states is_global ?s0 (combine_states is_global ?e1 ?ei)) ''Gx'' = 0"
    by (simp add: is_global_def enter_state_def)
  with outer_call show ?thesis by blast
qed

lemma recursion_locals_independent:
  "enter_state is_global
     ((enter_state is_global ((\<lambda>_. 0)(''Gx'' := 1)))(''Gx'' := 0)) ''y'' = 0"
  by (simp add: enter_state_def is_global_def)

end
