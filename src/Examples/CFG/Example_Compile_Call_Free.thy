section \<open>Call-free sources compile to a flat graph\<close>

theory Example_Compile_Call_Free
  imports "Voblint_Compile.Compile_Wellformed"
begin

text \<open>
  A \<^const>\<open>Call\<close> naming a \<^const>\<open>special_table\<close> entry compiles to an intra edge, not a
  \<^const>\<open>CallEdge\<close>, so the syntactic condition under which a compiled graph carries no
  call edges is not \<open>no Call node\<close> but \<open>no call to a compiled procedure\<close>.
  \<open>no_proc_call\<close> below is that condition: it is what a whole-program \<^const>\<open>calls\<close>-emptiness
  claim rests on, in place of evaluating the compiled set.
\<close>

primrec no_proc_call :: "com \<Rightarrow> bool" where
  "no_proc_call SKIP = True"
| "no_proc_call (Assign x a) = True"
| "no_proc_call (Check c) = True"
| "no_proc_call (Seq c1 c2) = (no_proc_call c1 \<and> no_proc_call c2)"
| "no_proc_call (If b c1 c2) = (no_proc_call c1 \<and> no_proc_call c2)"
| "no_proc_call (While b c) = no_proc_call c"
| "no_proc_call (Call dst q actuals) = (special_table q \<noteq> None)"
| "no_proc_call (Return e) = True"
| "no_proc_call Restore = True"
| "no_proc_call Unwind = True"

lemma compile_no_proc_call_K_empty:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> no_proc_call c \<Longrightarrow> K = {}"
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and K: "K = K1 \<union> K2"
    by (auto simp: Let_def split: prod.splits)
  show ?case using Seq.IH(1)[OF c1] Seq.IH(2)[OF c2] Seq.prems(2) K by simp
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and K: "K = K1 \<union> K2"
    by (auto simp: Let_def split: prod.splits)
  show ?case using If.IH(1)[OF c1] If.IH(2)[OF c2] If.prems(2) K by simp
next
  case (While b c)
  from While.prems(1) obtain n1 en1 E1 K1 where
      c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and K: "K = K1"
    by (auto simp: Let_def split: prod.splits)
  show ?case using While.IH[OF c1] While.prems(2) K by simp
next
  case (Call dst q actuals)
  then show ?case by (auto split: option.splits)
qed auto

lemma compile_proc_no_proc_call_K_empty:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> no_proc_call (body decl) \<Longrightarrow> K = {}"
  unfolding compile_proc_def
  by (auto simp: Let_def split: prod.splits dest: compile_no_proc_call_K_empty)

lemma compile_procs_no_proc_call_K_empty:
  assumes "compile_procs \<Pi> ps n = (n', E, K)"
    and "\<And>q decl. q \<in> set ps \<Longrightarrow> \<Pi> q = Some decl \<Longrightarrow> no_proc_call (body decl)"
  shows "K = {}"
  using compile_procs_calls_origin[OF assms(1)] assms(2) compile_proc_no_proc_call_K_empty
  by blast

theorem compile_prog_calls_empty:
  assumes main_free: "no_proc_call (main_body \<Pi>)"
      and procs_free: "\<And>q decl. q \<in> set ps \<Longrightarrow> \<Pi> q = Some decl \<Longrightarrow> no_proc_call (body decl)"
  shows "calls (compile_prog \<Pi> ps) = {}"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = main_body \<Pi>\<rparr> n1 = (n2, Emain, Kmain)"
    and g: "calls (compile_prog \<Pi> ps) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  show ?thesis unfolding g
    using compile_procs_no_proc_call_K_empty[OF procs procs_free]
      compile_proc_no_proc_call_K_empty[OF mainc] main_free by simp
qed

end
