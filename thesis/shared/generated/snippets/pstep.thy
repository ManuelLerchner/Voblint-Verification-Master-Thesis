(* src/Program_Model/VIMP/VIMP_Semantics.thy *)
inductive pstep :: "kenv \<Rightarrow> ('a, var_id, exp) gptable
    \<Rightarrow> 'a com \<times> store \<times> frame list \<Rightarrow> 'a com \<times> store \<times> frame list \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>p/ _)" [51, 51, 51, 51] 50)
  for \<kappa> :: kenv and \<Pi> :: "('a, var_id, exp) gptable"
where
  Assign:  "\<kappa>,\<Pi> \<turnstile> (Assign i x a, s, frs) \<rightarrow>\<^sub>p (SKIP i, s(x := kind_conv \<kappa> (Some x) (eval a s)), frs)"
| Check:   "\<kappa>,\<Pi> \<turnstile> (Check i l c, s, frs) \<rightarrow>\<^sub>p (SKIP i, s, frs)"
| Seq1:    "\<kappa>,\<Pi> \<turnstile> (Seq (SKIP i) c2, s, frs) \<rightarrow>\<^sub>p (c2, s, frs)"
| Seq2:    "\<kappa>,\<Pi> \<turnstile> (c1, s, frs) \<rightarrow>\<^sub>p (c1', s', frs')
             \<Longrightarrow> \<kappa>,\<Pi> \<turnstile> (Seq c1 c2, s, frs) \<rightarrow>\<^sub>p (Seq c1' c2, s', frs')"
| IfTrue:  "truthy (eval b s) \<Longrightarrow> \<kappa>,\<Pi> \<turnstile> (If i b c1 c2, s, frs) \<rightarrow>\<^sub>p (c1, s, frs)"
| IfFalse: "\<not> truthy (eval b s) \<Longrightarrow> \<kappa>,\<Pi> \<turnstile> (If i b c1 c2, s, frs) \<rightarrow>\<^sub>p (c2, s, frs)"
| While:   "\<kappa>,\<Pi> \<turnstile> (While i b c, s, frs) \<rightarrow>\<^sub>p (If i b (Seq c (While i b c)) (SKIP i), s, frs)"
| Call:    "\<Pi> p = Some decl
             \<Longrightarrow> length actuals = length (formals decl)
             \<Longrightarrow> distinct (formals decl)
             \<Longrightarrow> vals = map (\<lambda>e. eval e s) actuals
             \<Longrightarrow> callee = bind_formals (formals decl)
                           (map2 (\<lambda>x. kind_conv \<kappa> (Some x)) (formals decl) vals)
                           (enter_state is_global s)
             \<Longrightarrow> \<kappa>,\<Pi> \<turnstile> (Call i dst p actuals, s, frs)
                   \<rightarrow>\<^sub>p (Seq (body decl) (Restore i), callee, Frame s dst # frs)"
| Special: "special_table p = Some desc
             \<Longrightarrow> classify_special desc actuals = Some sc
             \<Longrightarrow> special_result eval sc s v
             \<Longrightarrow> \<kappa>,\<Pi> \<turnstile> (Call i (Some x) p actuals, s, frs) \<rightarrow>\<^sub>p (SKIP i, s(x := kind_conv \<kappa> (Some x) v), frs)"
| RestoreStep:
    "\<kappa>,\<Pi> \<turnstile> (Restore i, s, Frame fr dst # frs)
       \<rightarrow>\<^sub>p (SKIP i, combine_assign dst (kind_conv \<kappa> dst (s ReturnVar)) (combine_env is_global fr s), frs)"
| ReturnSome:
    "\<kappa>,\<Pi> \<turnstile> (Return i (Some e), s, frs) \<rightarrow>\<^sub>p (Unwind i, s(ReturnVar := eval e s), frs)"
| ReturnNone:
    "\<kappa>,\<Pi> \<turnstile> (Return i None, s, frs) \<rightarrow>\<^sub>p (Unwind i, s, frs)"
| UnwindDead:
    "\<not> is_Restore c2 \<Longrightarrow> \<kappa>,\<Pi> \<turnstile> (Seq (Unwind i) c2, s, frs) \<rightarrow>\<^sub>p (Unwind i, s, frs)"
| UnwindAct:
    "\<kappa>,\<Pi> \<turnstile> (Seq (Unwind j) (Restore i), s, Frame fr dst # frs)
       \<rightarrow>\<^sub>p (SKIP i, combine_assign dst (kind_conv \<kappa> dst (s ReturnVar)) (combine_env is_global fr s), frs)"
