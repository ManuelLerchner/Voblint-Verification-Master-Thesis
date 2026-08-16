theory Example_VIMP_Proc_Regression
  imports "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Examples: native activation semantics\<close>

text \<open>These witnesses build small hand-written commands rather than compiling a source
  program, so there is no \<^const>\<open>declared_global\<close> table to read a classifier off; they
  reuse the G-prefix convention directly as a fixed classifier.\<close>
abbreviation vpr_gs :: "vname \<Rightarrow> bool" where
  "vpr_gs \<equiv> (\<lambda>x. x \<noteq> STR '''' \<and> hd (String.explode x) = CHR ''G'')"

text \<open>Ground facts bridging \<^const>\<open>String.explode\<close> on this file's concrete
  variable names, for the \<open>simp\<close> steps below that unfold \<open>vpr_gs\<close> under
  an otherwise-open store.\<close>
lemma explode_x_hd [simp]: "hd (String.explode (STR ''x'')) \<noteq> CHR ''G''" by eval
lemma explode_y_hd [simp]: "hd (String.explode (STR ''y'')) \<noteq> CHR ''G''" by eval
lemma explode_Gg_hd [simp]: "hd (String.explode (STR ''Gg'')) = CHR ''G''" by eval
lemma explode_Gx_hd [simp]: "hd (String.explode (STR ''Gx'')) = CHR ''G''" by eval

theorem caller_local_isolated:
  assumes p: "\<Pi> pf = Some (proc_decl_of [] (imp \<lbrakk> x := 9 \<rbrakk>))"
  shows "\<exists>t. pcompletes vpr_gs \<Pi> (Seq (Assign (STR ''x'') (N 5)) (Call None pf [])) s0 t
             \<and> t (STR ''x'') = 5"
proof -
  let ?s1 = "s0((STR ''x'') := 5)"
  have a: "pcompletes vpr_gs \<Pi> (imp \<lbrakk> x := 5 \<rbrakk>) s0 ?s1"
  proof -
    have "pcompletes vpr_gs \<Pi> (imp \<lbrakk> x := 5 \<rbrakk>) s0
            (s0((STR ''x'') := aval (N 5) s0))" by (rule pcompletes_assign)
    thus ?thesis by simp
  qed
  have body: "pcompletes vpr_gs \<Pi> (imp \<lbrakk> x := 9 \<rbrakk>)
               (enter_state vpr_gs ?s1) ((enter_state vpr_gs ?s1)((STR ''x'') := 9))"
  proof -
    have "pcompletes vpr_gs \<Pi> (imp \<lbrakk> x := 9 \<rbrakk>) (enter_state vpr_gs ?s1)
            ((enter_state vpr_gs ?s1)((STR ''x'') := aval (N 9) (enter_state vpr_gs ?s1)))"
      by (rule pcompletes_assign)
    thus ?thesis by simp
  qed
  have call: "pcompletes vpr_gs \<Pi> (Call None pf []) ?s1
                (combine_env vpr_gs ?s1 ((enter_state vpr_gs ?s1)((STR ''x'') := 9)))"
    by (rule pcompletes_Call_parameterless[OF p body])
  have seq: "pcompletes vpr_gs \<Pi> (Seq (imp \<lbrakk> x := 5 \<rbrakk>) (Call None pf [])) s0
               (combine_env vpr_gs ?s1 ((enter_state vpr_gs ?s1)((STR ''x'') := 9)))"
    using pcompletes_Seq[OF a call] .
  have "(combine_env vpr_gs ?s1 ((enter_state vpr_gs ?s1)((STR ''x'') := 9))) (STR ''x'') = 5"
    by simp
  with seq show ?thesis by blast
qed

theorem global_propagated:
  assumes p: "\<Pi> pf = Some (proc_decl_of [] (imp \<lbrakk> Gg := 9 \<rbrakk>))"
  shows "\<exists>t. pcompletes vpr_gs \<Pi> (Call None pf []) s0 t \<and> t (STR ''Gg'') = 9"
proof -
  have body: "pcompletes vpr_gs \<Pi> (imp \<lbrakk> Gg := 9 \<rbrakk>)
               (enter_state vpr_gs s0) ((enter_state vpr_gs s0)((STR ''Gg'') := 9))"
  proof -
    have "pcompletes vpr_gs \<Pi> (imp \<lbrakk> Gg := 9 \<rbrakk>) (enter_state vpr_gs s0)
            ((enter_state vpr_gs s0)((STR ''Gg'') := aval (N 9) (enter_state vpr_gs s0)))"
      by (rule pcompletes_assign)
    thus ?thesis by simp
  qed
  have call: "pcompletes vpr_gs \<Pi> (Call None pf []) s0
                (combine_env vpr_gs s0 ((enter_state vpr_gs s0)((STR ''Gg'') := 9)))"
    by (rule pcompletes_Call_parameterless[OF p body])
  have "(combine_env vpr_gs s0 ((enter_state vpr_gs s0)((STR ''Gg'') := 9))) (STR ''Gg'') = 9"
    by simp
  with call show ?thesis by blast
qed

theorem return_value_propagated:
  assumes p: "\<Pi> pf = Some (proc_decl_of [] (imp \<lbrakk> return 7 \<rbrakk>))"
  shows "\<exists>t. pcompletes vpr_gs \<Pi> (Call (Some (STR ''x'')) pf []) s0 t \<and> t (STR ''x'') = 7"
proof -
  let ?e = "N 7"
  let ?t = "(combine_env vpr_gs s0
              ((enter_state vpr_gs s0)(ret_var := aval ?e (enter_state vpr_gs s0))))
              ((STR ''x'') := aval ?e (enter_state vpr_gs s0))"
  have call: "psteps vpr_gs \<Pi> (Call (Some (STR ''x'')) pf [], s0, []) (imp \<lbrakk> skip \<rbrakk>, ?t, [])"
    using p by (rule call_return_completes[where x = "(STR ''x'')" and s = s0 and frs = "[]"])
  have "?t (STR ''x'') = 7" by simp
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
  assumes p: "\<Pi> (STR ''r'') = Some (proc_decl_of [] rec_body)"
  shows "\<exists>t. pcompletes vpr_gs \<Pi> (imp \<lbrakk> r() \<rbrakk>) ((\<lambda>_. 0)((STR ''Gx'') := 1)) t \<and> t (STR ''Gx'') = 0"
proof -
  let ?s0 = "(\<lambda>_. 0)((STR ''Gx'') := 1)"
  let ?e0 = "enter_state vpr_gs ?s0"
  let ?e1 = "?e0((STR ''Gx'') := 0)"
  let ?ei = "enter_state vpr_gs ?e1"
  have inner_guard: "\<not> truthy (aval (Less (N 0) (V (STR ''Gx''))) ?ei)"
    by (simp add: enter_state_def)
  have inner_body: "pcompletes vpr_gs \<Pi> rec_body ?ei ?ei"
    unfolding rec_body_def by (rule pcompletes_IfFalse[OF inner_guard pcompletes_skip])
  have inner_call: "pcompletes vpr_gs \<Pi> (imp \<lbrakk> r() \<rbrakk>) ?e1 (combine_env vpr_gs ?e1 ?ei)"
    by (rule pcompletes_Call_parameterless[OF p inner_body])
  have outer_guard: "truthy (aval (Less (N 0) (V (STR ''Gx''))) ?e0)"
    by (simp add: enter_state_def)
  have dec: "pcompletes vpr_gs \<Pi> (imp \<lbrakk> Gx := Gx - 1 \<rbrakk>) ?e0 ?e1"
  proof -
    have "pcompletes vpr_gs \<Pi> (imp \<lbrakk> Gx := Gx - 1 \<rbrakk>) ?e0
            (?e0((STR ''Gx'') := aval (Minus (V (STR ''Gx'')) (N 1)) ?e0))"
      by (rule pcompletes_assign)
    thus ?thesis by (simp add: enter_state_def)
  qed
  have outer_body: "pcompletes vpr_gs \<Pi> rec_body ?e0 (combine_env vpr_gs ?e1 ?ei)"
    unfolding rec_body_def
    by (rule pcompletes_IfTrue[OF outer_guard pcompletes_Seq[OF dec inner_call]])
  have outer_call: "pcompletes vpr_gs \<Pi> (imp \<lbrakk> r() \<rbrakk>) ?s0
                       (combine_env vpr_gs ?s0 (combine_env vpr_gs ?e1 ?ei))"
    by (rule pcompletes_Call_parameterless[OF p outer_body])
  have "(combine_env vpr_gs ?s0 (combine_env vpr_gs ?e1 ?ei)) (STR ''Gx'') = 0"
    by (simp add: enter_state_def)
  with outer_call show ?thesis by blast
qed

lemma recursion_locals_independent:
  "enter_state vpr_gs
     ((enter_state vpr_gs ((\<lambda>_. 0)((STR ''Gx'') := 1)))((STR ''Gx'') := 0)) (STR ''y'') = 0"
  by (simp add: enter_state_def)

end
