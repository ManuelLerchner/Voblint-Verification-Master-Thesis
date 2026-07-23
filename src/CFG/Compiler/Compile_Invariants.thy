theory Compile_Invariants
  imports IMP2_Proc_to_CFG
begin

section \<open>Structural invariants of the procedure-aware compiler\<close>

text \<open>
  The sixteen structural obligations of Stage 5A, plus the parameter-binding exhibit.
  Everything here is about node/edge shape --- the full source-to-\<open>valid_ltr\<close>
  simulation is Stage 5B.
\<close>

subsection \<open>Compiler input well-formedness\<close>

text \<open>\<open>mnm\<close> names the distinguished entry procedure, declared in \<open>\<Pi>\<close> with an empty
  formal list and body \<open>main\<close>.  The callee list \<open>ps\<close> enumerates the other declared
  procedures (\<open>dom \<Pi>\<close> minus \<open>mnm\<close>), so \<open>FunctionEntry mnm\<close> / \<open>FunctionResult mnm\<close>
  never collide with a callee's nodes, yet \<open>FunctionEntry mnm\<close> is an ordinary
  \<open>proc_activation \<Pi> mnm main\<close> activation.\<close>
definition wf_compile_input ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "wf_compile_input \<Pi> ps mnm main \<longleftrightarrow>
     distinct ps \<and> set ps = {p. \<Pi> p \<noteq> None} - {mnm} \<and> mnm \<notin> set ps
   \<and> \<Pi> mnm = Some (proc_decl_of [] main)
   \<and> source_pi \<Pi> \<and> source_com main"

subsection \<open>Syntactic occurrence predicates\<close>

fun has_call :: "com \<Rightarrow> bool" where
  "has_call (Call _ _ _) = True"
| "has_call (Seq c1 c2) = (has_call c1 \<or> has_call c2)"
| "has_call (If _ c1 c2) = (has_call c1 \<or> has_call c2)"
| "has_call (While _ c) = has_call c"
| "has_call _ = False"

fun returns_in :: "aexp option \<Rightarrow> com \<Rightarrow> bool" where
  "returns_in e (Return e') = (e = e')"
| "returns_in e (Seq c1 c2) = (returns_in e c1 \<or> returns_in e c2)"
| "returns_in e (If _ c1 c2) = (returns_in e c1 \<or> returns_in e c2)"
| "returns_in e (While _ c) = returns_in e c"
| "returns_in e _ = False"

subsection \<open>Return edges and call-freeness\<close>

text \<open>(10) Every source \<open>Return e\<close> in a procedure body \<open>p\<close> compiles to an intra edge
  reaching \<open>FunctionResult p\<close> through \<open>EA_Ret e p\<close>.\<close>
lemma compile_return_edge:
  "compile \<Pi> p c n = (n', en, ex, E, K) \<Longrightarrow> returns_in e c
   \<Longrightarrow> \<exists>k. (Statement k, EA_Ret e p, FunctionResult p) \<in> E"
proof (induction c arbitrary: n n' en ex E K rule: com.induct)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 en1 ex1 E1 K1 n2 en2 ex2 E2 K2 where
    c1: "compile \<Pi> p c1 n = (n1, en1, ex1, E1, K1)"
    and c2: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    and E: "E = E1 \<union> (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)}) \<union> E2"
    by (auto split: prod.splits)
  from Seq.prems(2) have "returns_in e c1 \<or> returns_in e c2" by simp
  then show ?case using Seq.IH(1)[OF c1] Seq.IH(2)[OF c2] E by auto
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 en1 ex1 E1 K1 n2 en2 ex2 E2 K2 where
    c1: "compile \<Pi> p c1 (Suc n) = (n1, en1, ex1, E1, K1)"
    and c2: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                  \<union> E1 \<union> E2 \<union> {(ex1, EA_Nop, Statement n2), (ex2, EA_Nop, Statement n2)}"
    by (auto split: prod.splits)
  from If.prems(2) have "returns_in e c1 \<or> returns_in e c2" by simp
  then show ?case using If.IH(1)[OF c1] If.IH(2)[OF c2] E by auto
next
  case (While b c)
  from While.prems(1) obtain n1 en1 ex1 E1 K1 where
    c1: "compile \<Pi> p c (Suc n) = (n1, en1, ex1, E1, K1)"
    and E: "E = {(Statement n, EA_Assume b, en1),
                 (Statement n, EA_AssumeNot b, Statement n1),
                 (ex1, EA_Nop, Statement n)} \<union> E1"
    by (auto split: prod.splits)
  from While.prems(2) have "returns_in e c" by simp
  then show ?case using While.IH[OF c1] E by auto
next
  case (Return e') then show ?case by (auto split: if_splits)
qed auto

text \<open>(15) A call-free command compiles to an empty \<open>calls\<close> set.\<close>
lemma compile_no_call:
  "compile \<Pi> p c n = (n', en, ex, E, K) \<Longrightarrow> \<not> has_call c \<Longrightarrow> K = {}"
  by (induction c arbitrary: n n' en ex E K rule: com.induct)
     (auto split: prod.splits if_splits)

lemma compile_proc_no_call:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> \<not> has_call (body decl) \<Longrightarrow> K = {}"
  by (auto simp: compile_proc_def Let_def split: prod.splits dest: compile_no_call)

text \<open>(15) A program whose procedure bodies and main are all call-free compiles to
  \<open>calls = {}\<close> --- the flat-CFG fragment.\<close>
lemma compile_procs_no_call:
  "compile_procs \<Pi> ps n = (n', E, K)
   \<Longrightarrow> (\<forall>p decl. \<Pi> p = Some decl \<longrightarrow> \<not> has_call (body decl)) \<Longrightarrow> K = {}"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None with Cons show ?thesis by simp
  next
    case (Some decl)
    with Cons.prems(1) obtain n1 E0 K0 n2 E' K' where
      cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')" and K: "K = K0 \<union> K'"
      by (auto split: prod.splits)
    have "K0 = {}" using compile_proc_no_call[OF cp] Cons.prems(2) Some by auto
    moreover have "K' = {}" using Cons.IH[OF rest] Cons.prems(2) by auto
    ultimately show ?thesis using K by simp
  qed
qed

theorem compile_prog_flat:
  assumes "\<forall>p decl. \<Pi> p = Some decl \<longrightarrow> \<not> has_call (body decl)"
    and "\<not> has_call main"
  shows "flat_cfg (compile_prog \<Pi> ps mnm main)"
proof -
  obtain n1 Eprocs Kprocs where
    procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)" by (metis prod_cases3)
  obtain n2 Emain Kmain where
    mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    by (metis prod_cases3)
  have "Kprocs = {}" using compile_procs_no_call[OF procs] assms(1) by simp
  moreover have "Kmain = {}"
    using compile_proc_no_call[OF mainc] assms(2) by (simp add: proc_decl_of_def)
  ultimately show ?thesis
    unfolding flat_cfg_def compile_prog_def by (simp add: procs mainc Let_def)
qed

subsection \<open>Statement-range disjointness of distinct procedures\<close>

lemma compile_proc_frag_range:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> frag_stmts E K \<subseteq> {n..<n'}"
proof -
  assume "compile_proc \<Pi> p decl n = (n', E, K)"
  then obtain ben bex Eb where
    cb: "compile \<Pi> p (body decl) n = (n', ben, bex, Eb, K)"
    and E: "E = insert (FunctionEntry p, EA_Nop, ben)
                  (insert (bex, EA_Ret None p, FunctionResult p) Eb)"
    by (auto simp: compile_proc_def Let_def split: prod.splits)
  obtain kb where ben: "ben = Statement kb" "n \<le> kb" "kb < n'"
    using compile_entry_exit_stmt[OF cb] by blast
  obtain kc where bex: "bex = Statement kc" "n \<le> kc" "kc < n'"
    using compile_entry_exit_stmt[OF cb] by blast
  have body: "frag_stmts Eb K \<subseteq> {n..<n'}" using compile_frag_stmts_range[OF cb] .
  have Eunfold: "E = {(FunctionEntry p, EA_Nop, ben),
                      (bex, EA_Ret None p, FunctionResult p)} \<union> Eb"
    using E by auto
  have lit: "frag_stmts {(FunctionEntry p, EA_Nop, ben),
                (bex, EA_Ret None p, FunctionResult p)} {} \<subseteq> {n..<n'}"
    using ben bex by (auto simp: frag_stmts_def)
  have "frag_stmts E K
          = frag_stmts ({(FunctionEntry p, EA_Nop, ben),
              (bex, EA_Ret None p, FunctionResult p)} \<union> Eb) ({} \<union> K)"
    using Eunfold by simp
  also have "... = frag_stmts {(FunctionEntry p, EA_Nop, ben),
                (bex, EA_Ret None p, FunctionResult p)} {} \<union> frag_stmts Eb K"
    by (rule frag_stmts_Un)
  also have "... \<subseteq> {n..<n'}" using lit body by fastforce
  finally show ?thesis .
qed

lemma compile_procs_counter_mono:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> n \<le> n'"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None with Cons show ?thesis by simp
  next
    case (Some decl)
    with Cons.prems obtain n1 E0 K0 n2 E' K' where
      cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')" and n': "n' = n2"
      by (auto split: prod.splits)
    have "n \<le> n1"
      using cp by (auto simp: compile_proc_def Let_def split: prod.splits
                        dest: compile_counter_mono)
    with Cons.IH[OF rest] n' show ?thesis by simp
  qed
qed

lemma compile_procs_frag_range:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> frag_stmts E K \<subseteq> {n..<n'}"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by (simp add: frag_stmts_def)
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None with Cons show ?thesis by simp
  next
    case (Some decl)
    with Cons.prems obtain n1 E0 K0 n2 E' K' where
      cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')"
      and n': "n' = n2" and E: "E = E0 \<union> E'" and K: "K = K0 \<union> K'"
      by (auto split: prod.splits)
    have m1: "n \<le> n1"
      using cp by (auto simp: compile_proc_def Let_def split: prod.splits
                        dest: compile_counter_mono)
    have m2: "n1 \<le> n2" using compile_procs_counter_mono[OF rest] .
    have r0: "frag_stmts E0 K0 \<subseteq> {n..<n1}" using compile_proc_frag_range[OF cp] .
    have r': "frag_stmts E' K' \<subseteq> {n1..<n2}" using Cons.IH[OF rest] .
    have "frag_stmts E K = frag_stmts E0 K0 \<union> frag_stmts E' K'"
      unfolding E K by (rule frag_stmts_Un)
    also have "... \<subseteq> {n..<n2}" using r0 r' m1 m2 by fastforce
    finally show ?thesis unfolding n' .
  qed
qed

text \<open>(7) Statement ranges of distinct procedures are disjoint: the first procedure's
  statements precede the counter at which the rest begins, and the rest's follow it.\<close>
theorem compile_procs_head_disjoint:
  assumes "compile_proc \<Pi> p decl n = (n1, E0, K0)"
    and "compile_procs \<Pi> ps n1 = (n2, E', K')"
  shows "frag_stmts E0 K0 \<inter> frag_stmts E' K' = {}"
proof -
  have "frag_stmts E0 K0 \<subseteq> {n..<n1}" using compile_proc_frag_range[OF assms(1)] .
  moreover have "frag_stmts E' K' \<subseteq> {n1..<n2}" using compile_procs_frag_range[OF assms(2)] .
  ultimately show ?thesis by fastforce
qed

subsection \<open>The sixteen structural obligations, assembled\<close>

text \<open>(1) The compiled CFG is well-formed.\<close>
lemmas inv1_wf = compile_prog_wf

text \<open>(2) Every call edge targets a \<open>FunctionEntry\<close>.\<close>
theorem inv2_calls_to_entry:
  "(u, act, ce, af) \<in> calls (compile_prog \<Pi> ps mnm main) \<Longrightarrow> \<exists>p. ce = FunctionEntry p"
  using wf_call_targets_entry[OF compile_prog_wf] .

text \<open>(3) No intra edge enters a \<open>FunctionEntry\<close>.\<close>
theorem inv3_no_intra_into_entry:
  "(u, a, v) \<in> intra (compile_prog \<Pi> ps mnm main) \<Longrightarrow> v \<noteq> FunctionEntry q"
  using wf_intra_not_into_entry[OF compile_prog_wf] .

text \<open>(4) Every \<open>EA_Ret e p\<close> edge targets \<open>FunctionResult p\<close>.\<close>
theorem inv4_ret_to_result:
  "(u, EA_Ret e p, v) \<in> intra (compile_prog \<Pi> ps mnm main) \<Longrightarrow> v = FunctionResult p"
  using edge_step_ret_target[OF compile_prog_wf] .

text \<open>(5) / (6) Each compiled procedure has a single entry node \<open>FunctionEntry p\<close> and a
  single result node \<open>FunctionResult p\<close>: the entry edge and the fall-through result edge
  are emitted by \<open>compile_proc\<close>, and both nodes are keyed by the procedure name (distinct
  procedures get distinct nodes).\<close>
theorem inv5_6_proc_entry_result_edges:
  assumes "compile_proc \<Pi> p decl n = (n', E, K)"
  shows "(\<exists>ben. (FunctionEntry p, EA_Nop, ben) \<in> E)
       \<and> (\<exists>bex. (bex, EA_Ret None p, FunctionResult p) \<in> E)"
  using assms by (auto simp: compile_proc_def Let_def split: prod.splits)

theorem inv5_6_entry_result_distinct:
  "p \<noteq> q \<Longrightarrow> FunctionEntry p \<noteq> FunctionEntry q \<and> FunctionResult p \<noteq> FunctionResult q"
  by simp

text \<open>(8) Every call continuation is a CFG node.\<close>
theorem inv8_continuation_in_nodes:
  "(u, act, ce, af) \<in> calls (compile_prog \<Pi> ps mnm main)
   \<Longrightarrow> af \<in> cfg_nodes (compile_prog \<Pi> ps mnm main)"
  using call_endpoints_in_nodes(3) .

text \<open>(9) Calls appear only in \<open>calls\<close>, never in \<open>intra\<close>: by typing an intra edge cannot
  carry a call, so no \<open>FunctionEntry\<close> is an intra successor.\<close>
theorem inv9_no_intra_call:
  "FunctionEntry p \<notin> intra_successors (compile_prog \<Pi> ps mnm main) u"
  using wf_no_intra_call[OF compile_prog_wf] .

text \<open>(10) is \<open>compile_return_edge\<close> above.  (11) dead code after a return is unreachable:
  the return fragment's normal-exit node has no incoming intra edge, so a following
  command wired from it is off every return-to-result path.\<close>
theorem inv11_return_exit_unreached:
  "(u, a, Statement (Suc n)) \<notin> fst (snd (snd (snd (compile \<Pi> p (Return e) n))))"
  by simp

text \<open>(12) Normal fall-through reaches the procedure result --- the \<open>compile_proc\<close>
  fall-through edge of \<open>inv5_6_proc_entry_result_edges\<close>.\<close>
lemmas inv12_fallthrough = inv5_6_proc_entry_result_edges

text \<open>(13) Multiple returns converge: two \<open>Return\<close> branches both reach \<open>FunctionResult p\<close>.\<close>
theorem inv13_multi_return_converge:
  assumes "compile \<Pi> p (If b (Return e1) (Return e2)) n = (n', en, ex, E, K)"
  shows "(\<exists>k. (Statement k, EA_Ret e1 p, FunctionResult p) \<in> E)
       \<and> (\<exists>k. (Statement k, EA_Ret e2 p, FunctionResult p) \<in> E)"
  using compile_return_edge[OF assms, of e1] compile_return_edge[OF assms, of e2] by simp

text \<open>(14) A recursive call targets the caller procedure's own \<open>FunctionEntry\<close>, while its
  call site and continuation stay ordinary statement nodes.\<close>
theorem inv14_recursion_edge:
  "(Statement n, CallEdge None (case \<Pi> p of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) [], FunctionEntry p, Statement (Suc n))
     \<in> snd (snd (snd (snd (compile \<Pi> p (Call None p []) n))))"
  by simp

text \<open>(15) is \<open>compile_prog_flat\<close> above.  (16) the program entry is the main entry node.\<close>
theorem inv16_entry_is_main:
  "cfg_entry (compile_prog \<Pi> ps mnm main) = FunctionEntry mnm"
  unfolding compile_prog_def by (simp add: Let_def split: prod.splits)

subsection \<open>Parameter-binding exhibit: naive entry assignments are wrong\<close>

text \<open>
  The trace kernel enters a callee at \<^const>\<open>enter_state\<close> (locals reset to zero, globals
  kept), and the true parameter binding is \<^const>\<open>bind_formals\<close> with the actuals evaluated
  in the CALLER store.  A naive scheme that instead emits the formal-binding assignments at
  the callee entry --- evaluating each actual in the already-entered callee store --- is
  incorrect: an actual that reads a caller local sees the reset value \<open>0\<close>, not the caller's.

  Concretely, for the single formal \<open>x\<close> bound to the actual \<open>V ''y''\<close> where \<open>y\<close> is a caller
  local holding \<open>5\<close>: the correct binding gives \<open>x = 5\<close>, the naive callee-entry assignment
  gives \<open>x = 0\<close>.  This is why the compiler keeps the actuals on the \<open>CallEdge\<close> (evaluated in
  the caller store by the entry transfer) rather than compiling them into callee-entry
  assignments.
\<close>
text \<open>The root cause, at the store level: \<^const>\<open>enter_state\<close> resets a caller local to
  \<open>0\<close>.  So an actual argument that reads a caller local, if evaluated in the entered callee
  store (the naive scheme), yields \<open>0\<close> instead of the caller value --- the correct binding
  evaluates the actual in the caller store (\<^const>\<open>bind_formals\<close> over
  \<open>map (\<lambda>e. aval e caller) actuals\<close>).  This is why the compiler carries the actuals on the
  \<open>CallEdge\<close> for the caller-side entry transfer, rather than compiling them into callee-entry
  assignments.\<close>
lemma naive_entry_binding_wrong:
  "\<exists>s :: store. \<exists>x. \<not> is_global x \<and> enter_state s x \<noteq> s x"
proof (intro exI conjI)
  show "\<not> is_global ''y''" by (simp add: is_global_def)
  show "enter_state ((\<lambda>_. 0)(''y'' := (5 :: int))) ''y'' \<noteq> ((\<lambda>_. 0)(''y'' := (5 :: int))) ''y''"
    by (simp add: enter_state_def is_global_def)
qed


end

