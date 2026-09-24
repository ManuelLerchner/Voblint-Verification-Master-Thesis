(* src/Program_Model/VIMP/VIMP_Proc.thy *)
inductive
  pstep :: "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> com \<times> store \<times> frame list
                       \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>p/ _)" [51, 51, 51, 51] 50)
  for \<G> :: "vname \<Rightarrow> bool" and \<Pi> :: proc_table
where
  Assign:  "\<G>, \<Pi> \<turnstile> (Assign x a, s, frs) \<rightarrow>\<^sub>p (SKIP, s(x := \<lbrakk>a\<rbrakk>\<^sub>e s), frs)"
| Check:   "\<G>, \<Pi> \<turnstile> (Check l c, s, frs) \<rightarrow>\<^sub>p (SKIP, s, frs)"
| Seq1:    "\<G>, \<Pi> \<turnstile> (Seq SKIP c2, s, frs) \<rightarrow>\<^sub>p (c2, s, frs)"
| Seq2:    "\<G>, \<Pi> \<turnstile> (c1, s, frs) \<rightarrow>\<^sub>p (c1', s', frs')
             \<Longrightarrow> \<G>, \<Pi> \<turnstile> (Seq c1 c2, s, frs) \<rightarrow>\<^sub>p (Seq c1' c2, s', frs')"
| IfTrue:  "truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) \<Longrightarrow> \<G>, \<Pi> \<turnstile> (If b c1 c2, s, frs) \<rightarrow>\<^sub>p (c1, s, frs)"
| IfFalse: "\<not> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) \<Longrightarrow> \<G>, \<Pi> \<turnstile> (If b c1 c2, s, frs) \<rightarrow>\<^sub>p (c2, s, frs)"
| While:   "\<G>, \<Pi> \<turnstile> (While b c, s, frs)
                      \<rightarrow>\<^sub>p (If b (Seq c (While b c)) SKIP, s, frs)"
| Call:    "\<Pi> p = Some decl
             \<Longrightarrow> length actuals = length (formals decl)
             \<Longrightarrow> distinct (formals decl)
             \<Longrightarrow> vals = map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) actuals
             \<Longrightarrow> callee = bind_formals (formals decl) vals (enter_state \<G> s)
             \<Longrightarrow> \<G>, \<Pi> \<turnstile> (Call dst p actuals, s, frs)
                 \<rightarrow>\<^sub>p (Seq (body decl) Restore,
                  callee,
                  Frame s dst # frs)"
| Special: "special_table p = Some desc
             \<Longrightarrow> classify_special desc actuals = Some sc
             \<Longrightarrow> special_result sc s v
             \<Longrightarrow> \<G>, \<Pi> \<turnstile> (Call (Some x) p actuals, s, frs) \<rightarrow>\<^sub>p (SKIP, s(x := v), frs)"
| RestoreStep:
    "\<G>, \<Pi> \<turnstile> (Restore, s, Frame fr dst # frs)
       \<rightarrow>\<^sub>p (SKIP, combine_assign dst (s ret_var) (combine_env \<G> fr s), frs)"
| ReturnSome:
    "\<G>, \<Pi> \<turnstile> (Return (Some e), s, frs)
       \<rightarrow>\<^sub>p (Unwind, s(ret_var := \<lbrakk>e\<rbrakk>\<^sub>e s), frs)"
| ReturnNone:
    "\<G>, \<Pi> \<turnstile> (Return None, s, frs) \<rightarrow>\<^sub>p (Unwind, s, frs)"
| UnwindDead:
    "c2 \<noteq> Restore
     \<Longrightarrow> \<G>, \<Pi> \<turnstile> (Seq Unwind c2, s, frs) \<rightarrow>\<^sub>p (Unwind, s, frs)"
| UnwindAct:
    "\<G>, \<Pi> \<turnstile> (Seq Unwind Restore, s, Frame fr dst # frs)
       \<rightarrow>\<^sub>p (SKIP, combine_assign dst (s ret_var) (combine_env \<G> fr s), frs)"
