(* src/Program_Model/VIMP/VIMP_Proc.thy *)
inductive gpstep :: "('a, 'v, 'e) gptable
    \<Rightarrow> ('a, 'v, 'e) gcom \<times> ('v \<Rightarrow> int) \<times> 'v gframe list
    \<Rightarrow> ('a, 'v, 'e) gcom \<times> ('v \<Rightarrow> int) \<times> 'v gframe list \<Rightarrow> bool"
  for \<Pi> :: "('a, 'v, 'e) gptable"
where
  Assign:  "gpstep \<Pi> (Assign i x a, s, frs) (SKIP i, s(x := conv (Some x) (ev a s)), frs)"
| Check:   "gpstep \<Pi> (Check i l c, s, frs) (SKIP i, s, frs)"
| Seq1:    "gpstep \<Pi> (Seq (SKIP i) c2, s, frs) (c2, s, frs)"
| Seq2:    "gpstep \<Pi> (c1, s, frs) (c1', s', frs')
             \<Longrightarrow> gpstep \<Pi> (Seq c1 c2, s, frs) (Seq c1' c2, s', frs')"
| IfTrue:  "truthy (ev b s) \<Longrightarrow> gpstep \<Pi> (If i b c1 c2, s, frs) (c1, s, frs)"
| IfFalse: "\<not> truthy (ev b s) \<Longrightarrow> gpstep \<Pi> (If i b c1 c2, s, frs) (c2, s, frs)"
| While:   "gpstep \<Pi> (While i b c, s, frs) (If i b (Seq c (While i b c)) (SKIP i), s, frs)"
| Call:    "\<Pi> p = Some decl
             \<Longrightarrow> length actuals = length (formals decl)
             \<Longrightarrow> distinct (formals decl)
             \<Longrightarrow> vals = map (\<lambda>e. ev e s) actuals
             \<Longrightarrow> callee = bind_formals (formals decl) vals (enter_state glob s)
             \<Longrightarrow> gpstep \<Pi> (Call i dst p actuals, s, frs)
                   (Seq (body decl) (Restore i), callee, Frame s dst # frs)"
| Special: "special_table p = Some desc
             \<Longrightarrow> classify_special desc actuals = Some sc
             \<Longrightarrow> special_result ev sc s v
             \<Longrightarrow> gpstep \<Pi> (Call i (Some x) p actuals, s, frs) (SKIP i, s(x := conv (Some x) v), frs)"
| RestoreStep:
    "gpstep \<Pi> (Restore i, s, Frame fr dst # frs)
       (SKIP i, combine_assign dst (conv dst (s rv)) (combine_env glob fr s), frs)"
| ReturnSome:
    "gpstep \<Pi> (Return i (Some e), s, frs) (Unwind i, s(rv := ev e s), frs)"
| ReturnNone:
    "gpstep \<Pi> (Return i None, s, frs) (Unwind i, s, frs)"
| UnwindDead:
    "\<not> is_Restore c2 \<Longrightarrow> gpstep \<Pi> (Seq (Unwind i) c2, s, frs) (Unwind i, s, frs)"
| UnwindAct:
    "gpstep \<Pi> (Seq (Unwind j) (Restore i), s, Frame fr dst # frs)
       (SKIP i, combine_assign dst (conv dst (s rv)) (combine_env glob fr s), frs)"
