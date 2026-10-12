(* src/Program_Model/VIMP/VIMP_Proc.thy *)
inductive
  pstep :: "(vname \<Rightarrow> bool) \<Rightarrow> 'a ptable \<Rightarrow> 'a acom \<times> store \<times> frame list
                       \<Rightarrow> 'a acom \<times> store \<times> frame list \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>p/ _)" [51, 51, 51, 51] 50)
  for \<G> :: "vname \<Rightarrow> bool" and \<Pi> :: "'a ptable"
where
  Assign:  "\<G>, \<Pi> \<turnstile> (Assign i x a, s, frs) \<rightarrow>\<^sub>p (SKIP i, s(x := \<lbrakk>a\<rbrakk>\<^sub>e s), frs)"
| Check:   "\<G>, \<Pi> \<turnstile> (Check i l c, s, frs) \<rightarrow>\<^sub>p (SKIP i, s, frs)"
| Seq1:    "\<G>, \<Pi> \<turnstile> (Seq (SKIP i) c2, s, frs) \<rightarrow>\<^sub>p (c2, s, frs)"
| Seq2:    "\<G>, \<Pi> \<turnstile> (c1, s, frs) \<rightarrow>\<^sub>p (c1', s', frs')
             \<Longrightarrow> \<G>, \<Pi> \<turnstile> (Seq c1 c2, s, frs) \<rightarrow>\<^sub>p (Seq c1' c2, s', frs')"
| IfTrue:  "truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) \<Longrightarrow> \<G>, \<Pi> \<turnstile> (If i b c1 c2, s, frs) \<rightarrow>\<^sub>p (c1, s, frs)"
| IfFalse: "\<not> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) \<Longrightarrow> \<G>, \<Pi> \<turnstile> (If i b c1 c2, s, frs) \<rightarrow>\<^sub>p (c2, s, frs)"
| While:   "\<G>, \<Pi> \<turnstile> (While i b c, s, frs)
                      \<rightarrow>\<^sub>p (If i b (Seq c (While i b c)) (SKIP i), s, frs)"
| Call:    "\<Pi> p = Some decl
             \<Longrightarrow> length actuals = length (formals decl)
             \<Longrightarrow> distinct (formals decl)
             \<Longrightarrow> vals = map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) actuals
             \<Longrightarrow> callee = bind_formals (formals decl) vals (enter_state \<G> s)
             \<Longrightarrow> \<G>, \<Pi> \<turnstile> (Call i dst p actuals, s, frs)
                 \<rightarrow>\<^sub>p (Seq (body decl) (Restore i),
                  callee,
                  Frame s dst # frs)"
| Special: "special_table p = Some desc
             \<Longrightarrow> classify_special desc actuals = Some sc
             \<Longrightarrow> special_result sc s v
             \<Longrightarrow> \<G>, \<Pi> \<turnstile> (Call i (Some x) p actuals, s, frs) \<rightarrow>\<^sub>p (SKIP i, s(x := v), frs)"
| RestoreStep:
    "\<G>, \<Pi> \<turnstile> (Restore i, s, Frame fr dst # frs)
       \<rightarrow>\<^sub>p (SKIP i, combine_assign dst (s ret_var) (combine_env \<G> fr s), frs)"
| ReturnSome:
    "\<G>, \<Pi> \<turnstile> (Return i (Some e), s, frs)
       \<rightarrow>\<^sub>p (Unwind i, s(ret_var := \<lbrakk>e\<rbrakk>\<^sub>e s), frs)"
| ReturnNone:
    "\<G>, \<Pi> \<turnstile> (Return i None, s, frs) \<rightarrow>\<^sub>p (Unwind i, s, frs)"
| UnwindDead:
    "\<not> is_Restore c2
     \<Longrightarrow> \<G>, \<Pi> \<turnstile> (Seq (Unwind i) c2, s, frs) \<rightarrow>\<^sub>p (Unwind i, s, frs)"
| UnwindAct:
    "\<G>, \<Pi> \<turnstile> (Seq (Unwind j) (Restore i), s, Frame fr dst # frs)
       \<rightarrow>\<^sub>p (SKIP i, combine_assign dst (s ret_var) (combine_env \<G> fr s), frs)"
