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
  assumes p: "\<Pi> pf = Some (\<lparr>formals = [], body = imp \<lbrakk> x := 9 \<rbrakk>\<rparr>)"
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
  assumes p: "\<Pi> pf = Some (\<lparr>formals = [], body = imp \<lbrakk> Gg := 9 \<rbrakk>\<rparr>)"
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

text \<open>A parameterless call whose body returns a value completes with the value at
  the destination and the surrounding stack untouched: a return unwinds only to
  its own activation.\<close>
lemma call_return_completes:
  assumes q: "\<Pi> p = Some (\<lparr>formals = [], body = Return (Some e)\<rparr>)"
  shows "psteps gs \<Pi> (Call (Some x) p [], s, frs)
           (SKIP,
            (combine_env gs s
              ((enter_state gs s)(ret_var := aval e (enter_state gs s))))
              (x := aval e (enter_state gs s)),
            frs)"
proof -
  let ?s' = "(enter_state gs s)(ret_var := aval e (enter_state gs s))"
  have "pstep gs \<Pi> (Call (Some x) p [], s, frs)
          (Seq (Return (Some e)) Restore, enter_state gs s, Frame s (Some x) # frs)"
    using q by (rule pstep_Call_parameterless)
  moreover have "pstep gs \<Pi> (Seq (Return (Some e)) Restore, enter_state gs s, Frame s (Some x) # frs)
                   (Seq Unwind Restore, ?s', Frame s (Some x) # frs)"
    by (intro Seq2 ReturnSome)
  moreover have "pstep gs \<Pi> (Seq Unwind Restore, ?s', Frame s (Some x) # frs)
                   (SKIP, (combine_env gs s ?s')(x := aval e (enter_state gs s)), frs)"
    using UnwindAct[of gs \<Pi> ?s' s "Some x" frs] by simp
  ultimately show ?thesis by (meson star.refl star.step)
qed

lemma call_return_none_completes:
  assumes q: "\<Pi> p = Some (\<lparr>formals = [], body = Return None\<rparr>)"
  shows "psteps gs \<Pi> (Call None p [], s, frs)
           (SKIP, combine_env gs s (enter_state gs s), frs)"
proof -
  have "pstep gs \<Pi> (Call None p [], s, frs)
          (Seq (Return None) Restore, enter_state gs s, Frame s None # frs)"
    using q by (rule pstep_Call_parameterless)
  moreover have "pstep gs \<Pi> (Seq (Return None) Restore, enter_state gs s, Frame s None # frs)
                   (Seq Unwind Restore, enter_state gs s, Frame s None # frs)"
    by (intro Seq2 ReturnNone)
  moreover have "pstep gs \<Pi> (Seq Unwind Restore, enter_state gs s, Frame s None # frs)
                   (SKIP, combine_env gs s (enter_state gs s), frs)"
    using UnwindAct[of gs \<Pi> "enter_state gs s" s None frs] by simp
  ultimately show ?thesis by (meson star.refl star.step)
qed

text \<open>The inner return is caught by the inner activation, so the outer frame
  survives and execution resumes at the outer continuation.\<close>
theorem nested_call_return_trace:
  assumes qin: "\<Pi> pin = Some (\<lparr>formals = [], body = Return (Some e)\<rparr>)"
      and qout: "\<Pi> pout = Some (\<lparr>formals = [], body = Seq (Call (Some rin) pin []) after\<rparr>)"
  shows "psteps gs \<Pi> (Call (Some rout) pout [], s0, [])
           (Seq after Restore,
            (combine_env gs (enter_state gs s0)
              ((enter_state gs (enter_state gs s0))
                (ret_var := aval e (enter_state gs (enter_state gs s0)))))
                (rin := aval e (enter_state gs (enter_state gs s0))),
            [Frame s0 (Some rout)])"
proof -
  let ?s1 = "enter_state gs s0"
  let ?Fout = "Frame s0 (Some rout)"
  let ?inner = "(combine_env gs ?s1
                    ((enter_state gs ?s1)(ret_var := aval e (enter_state gs ?s1))))
                  (rin := aval e (enter_state gs ?s1))"
  have outer: "pstep gs \<Pi> (Call (Some rout) pout [], s0, [])
      (Seq (Seq (Call (Some rin) pin []) after) Restore, ?s1, [?Fout])"
    using qout by (rule pstep_Call_parameterless)
  have inner: "psteps gs \<Pi>
      (Seq (Seq (Call (Some rin) pin []) after) Restore, ?s1, [?Fout])
      (Seq (Seq SKIP after) Restore, ?inner, [?Fout])"
    by (intro psteps_Seq2 call_return_completes[where \<Pi> = \<Pi> and p = pin, OF qin])
  have resume: "pstep gs \<Pi>
      (Seq (Seq SKIP after) Restore, ?inner, [?Fout])
      (Seq after Restore, ?inner, [?Fout])"
    by (intro Seq2 Seq1)
  from outer inner resume show ?thesis by (meson star.refl star.step star_trans)
qed

theorem return_value_propagated:
  assumes p: "\<Pi> pf = Some (\<lparr>formals = [], body = imp \<lbrakk> return 7 \<rbrakk>\<rparr>)"
  shows "\<exists>t. pcompletes vpr_gs \<Pi> (Call (Some (STR ''x'')) pf []) s0 t \<and> t (STR ''x'') = 7"
proof -
  let ?e = "N 7"
  let ?t = "(combine_env vpr_gs s0
              ((enter_state vpr_gs s0)(ret_var := aval ?e (enter_state vpr_gs s0))))
              ((STR ''x'') := aval ?e (enter_state vpr_gs s0))"
  have call: "psteps vpr_gs \<Pi> (Call (Some (STR ''x'')) pf [], s0, []) (imp \<lbrakk> skip \<rbrakk>, ?t, [])"
    using p by (rule call_return_completes[where x = "(STR ''x'')" and s = s0 and frs = "[]"])
  have "?t (STR ''x'') = 7" by simp
  with call show ?thesis by blast
qed

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
  assumes p: "\<Pi> (STR ''r'') = Some (\<lparr>formals = [], body = rec_body\<rparr>)"
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
