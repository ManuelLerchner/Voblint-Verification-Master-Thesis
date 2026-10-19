(* src/Program_Model/VIMP/VIMP_Proc.thy *)
inductive gpstep :: "('a, 'v, 'e) gptable
    \<Rightarrow> ('a, 'v, 'e) gcom \<times> ('v \<Rightarrow> int) \<times> 'v gframe list
    \<Rightarrow> ('a, 'v, 'e) gcom \<times> ('v \<Rightarrow> int) \<times> 'v gframe list \<Rightarrow> bool"
    ("(_ \<turnstile>/ _ \<rightarrow>\<^sub>p/ _)" [51, 51, 51] 50)
  for \<Pi> :: "('a, 'v, 'e) gptable"
where
  Assign:  "\<Pi> \<turnstile> (Assign i x a, s, frs) \<rightarrow>\<^sub>p (SKIP i, s(x := conv (Some x) (ev a s)), frs)"
| Check:   "\<Pi> \<turnstile> (Check i l c, s, frs) \<rightarrow>\<^sub>p (SKIP i, s, frs)"
| Seq1:    "\<Pi> \<turnstile> (Seq (SKIP i) c2, s, frs) \<rightarrow>\<^sub>p (c2, s, frs)"
| Seq2:    "\<Pi> \<turnstile> (c1, s, frs) \<rightarrow>\<^sub>p (c1', s', frs')
             \<Longrightarrow> \<Pi> \<turnstile> (Seq c1 c2, s, frs) \<rightarrow>\<^sub>p (Seq c1' c2, s', frs')"
| IfTrue:  "truthy (ev b s) \<Longrightarrow> \<Pi> \<turnstile> (If i b c1 c2, s, frs) \<rightarrow>\<^sub>p (c1, s, frs)"
| IfFalse: "\<not> truthy (ev b s) \<Longrightarrow> \<Pi> \<turnstile> (If i b c1 c2, s, frs) \<rightarrow>\<^sub>p (c2, s, frs)"
| While:   "\<Pi> \<turnstile> (While i b c, s, frs) \<rightarrow>\<^sub>p (If i b (Seq c (While i b c)) (SKIP i), s, frs)"
| Call:    "\<Pi> p = Some decl
             \<Longrightarrow> length actuals = length (formals decl)
             \<Longrightarrow> distinct (formals decl)
             \<Longrightarrow> vals = map (\<lambda>e. ev e s) actuals
             \<Longrightarrow> callee = bind_formals (formals decl) (map2 (\<lambda>x. conv (Some x)) (formals decl) vals)
                           (enter_state glob s)
             \<Longrightarrow> \<Pi> \<turnstile> (Call i dst p actuals, s, frs)
                   \<rightarrow>\<^sub>p (Seq (body decl) (Restore i), callee, Frame s dst # frs)"
| Special: "special_table p = Some desc
             \<Longrightarrow> classify_special desc actuals = Some sc
             \<Longrightarrow> special_result ev sc s v
             \<Longrightarrow> \<Pi> \<turnstile> (Call i (Some x) p actuals, s, frs) \<rightarrow>\<^sub>p (SKIP i, s(x := conv (Some x) v), frs)"
| RestoreStep:
    "\<Pi> \<turnstile> (Restore i, s, Frame fr dst # frs)
       \<rightarrow>\<^sub>p (SKIP i, combine_assign dst (conv dst (s rv)) (combine_env glob fr s), frs)"
| ReturnSome:
    "\<Pi> \<turnstile> (Return i (Some e), s, frs) \<rightarrow>\<^sub>p (Unwind i, s(rv := ev e s), frs)"
| ReturnNone:
    "\<Pi> \<turnstile> (Return i None, s, frs) \<rightarrow>\<^sub>p (Unwind i, s, frs)"
| UnwindDead:
    "\<not> is_Restore c2 \<Longrightarrow> \<Pi> \<turnstile> (Seq (Unwind i) c2, s, frs) \<rightarrow>\<^sub>p (Unwind i, s, frs)"
| UnwindAct:
    "\<Pi> \<turnstile> (Seq (Unwind j) (Restore i), s, Frame fr dst # frs)
       \<rightarrow>\<^sub>p (SKIP i, combine_assign dst (conv dst (s rv)) (combine_env glob fr s), frs)"
