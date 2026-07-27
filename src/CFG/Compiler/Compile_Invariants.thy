theory Compile_Invariants
  imports IMP2_Proc_to_CFG
begin

section \<open>Structural invariants of the procedure-aware compiler\<close>

text \<open>
  The compiler preserves procedure boundaries, separates call edges from ordinary
  control flow, and allocates disjoint statement ranges. These properties connect
  source commands to activation-local traces without exposing compiler counters to
  semantic clients.
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
     distinct ps \<and>
     set ps = {p. \<Pi> p \<noteq> None} - {mnm} \<and>
     mnm \<notin> set ps \<and>
     wf_source_program \<Pi> mnm main"

lemma wf_compile_input_source_program:
  "wf_compile_input \<Pi> ps mnm main \<Longrightarrow> wf_source_program \<Pi> mnm main"
  by (simp add: wf_compile_input_def)

lemma wf_compile_input_main_exists:
  "wf_compile_input \<Pi> ps mnm main \<Longrightarrow> \<Pi> mnm = Some (proc_decl_of [] main)"
  using wf_compile_input_source_program wf_source_program_main_exists by blast

lemma wf_compile_input_source_pi:
  "wf_compile_input \<Pi> ps mnm main \<Longrightarrow> source_pi \<Pi>"
  using wf_compile_input_source_program wf_source_program_source_pi by blast

lemma wf_compile_input_source_com:
  "wf_compile_input \<Pi> ps mnm main \<Longrightarrow> source_com main"
  using wf_compile_input_source_program wf_source_program_source_com by blast

lemma wf_compile_input_no_return:
  "wf_compile_input \<Pi> ps mnm main \<Longrightarrow> no_return main"
  using wf_compile_input_source_program wf_source_program_no_return by blast

lemma wf_compile_input_decl:
  "wf_compile_input \<Pi> ps mnm main \<Longrightarrow> \<Pi> p = Some decl
   \<Longrightarrow> wf_proc_decl \<Pi> decl"
  using wf_compile_input_source_program wf_source_program_decl by blast

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

text \<open>Every source \<open>Return e\<close> in procedure \<open>p\<close> compiles to an intra edge that
  reaches \<open>FunctionResult p\<close> through \<open>EA_Ret e p\<close>.\<close>
lemma compile_return_edge:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> returns_in e c
   \<Longrightarrow> \<exists>j. (Statement j, EA_Ret e p, FunctionResult p) \<in> E"
proof (induction c arbitrary: k n n' en E K rule: com.induct)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and E: "E = E1 \<union> E2"
    by (auto simp: Let_def split: prod.splits)
  from Seq.prems(2) have "returns_in e c1 \<or> returns_in e c2" by simp
  then show ?case using Seq.IH(1)[OF c1] Seq.IH(2)[OF c2] E by auto
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                  \<union> E1 \<union> E2"
    by (auto split: prod.splits)
  from If.prems(2) have "returns_in e c1 \<or> returns_in e c2" by simp
  then show ?case using If.IH(1)[OF c1] If.IH(2)[OF c2] E by auto
next
  case (While b c)
  from While.prems(1) obtain n1 en1 E1 K1 where
    c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)} \<union> E1"
    by (auto split: prod.splits)
  from While.prems(2) have "returns_in e c" by simp
  then show ?case using While.IH[OF c1] E by auto
next
  case (Return e') then show ?case by (auto split: if_splits)
qed auto

text \<open>A call-free command compiles to an empty \<open>calls\<close> set.\<close>
lemma compile_no_call:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> \<not> has_call c \<Longrightarrow> K = {}"
  by (induction c arbitrary: k n n' en E K rule: com.induct)
     (auto simp: Let_def split: prod.splits if_splits)
lemma compile_proc_no_call:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> \<not> has_call (body decl) \<Longrightarrow> K = {}"
  by (auto simp: compile_proc_def Let_def split: prod.splits dest: compile_no_call)

text \<open>A program whose procedure bodies and main are call-free compiles to the flat
  fragment characterized by \<open>calls = {}\<close>.\<close>
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
  assume A: "compile_proc \<Pi> p decl n = (n', E, K)"
  define r where "r = n + csize (body decl)"
  from A obtain Eb where
    cb: "compile \<Pi> p (body decl) (Statement r) n = (r, Statement n, Eb, K)"
    and E: "E = insert (FunctionEntry p, EA_Nop, Statement n)
                  (if falls_through (body decl)
                   then insert (Statement r, EA_Ret None p, FunctionResult p) Eb
                   else Eb)"
    and n': "n' = Suc r"
    unfolding r_def by (rule compile_procE)
  have body: "frag_stmts Eb K \<subseteq> {n..<n'}"
    using compile_frag_stmts_range[OF cb] n' compile_counter_mono[OF cb] by auto
  have lit: "frag_stmts {(FunctionEntry p, EA_Nop, Statement n),
                (Statement r, EA_Ret None p, FunctionResult p)} {} \<subseteq> {n..<n'}"
    using n' r_def compile_counter_mono[OF cb] by (auto simp: frag_stmts_def)
  \<comment> \<open>the epilogue edge may be absent, so bound \<open>E\<close> by the set that always contains it\<close>
  have Esub: "E \<subseteq> {(FunctionEntry p, EA_Nop, Statement n),
                      (Statement r, EA_Ret None p, FunctionResult p)} \<union> Eb"
    using E by (auto split: if_splits)
  have "frag_stmts E K
          \<subseteq> frag_stmts ({(FunctionEntry p, EA_Nop, Statement n),
              (Statement r, EA_Ret None p, FunctionResult p)} \<union> Eb) ({} \<union> K)"
    by (rule frag_stmts_mono[OF Esub]) simp
  also have "... = frag_stmts {(FunctionEntry p, EA_Nop, Statement n),
                (Statement r, EA_Ret None p, FunctionResult p)} {} \<union> frag_stmts Eb K"
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

text \<open>Statement ranges of distinct procedures are disjoint: one fragment ends at the
  counter from which the next fragment allocates its statements.\<close>
theorem compile_procs_head_disjoint:
  assumes "compile_proc \<Pi> p decl n = (n1, E0, K0)"
    and "compile_procs \<Pi> ps n1 = (n2, E', K')"
  shows "frag_stmts E0 K0 \<inter> frag_stmts E' K' = {}"
proof -
  have "frag_stmts E0 K0 \<subseteq> {n..<n1}" using compile_proc_frag_range[OF assms(1)] .
  moreover have "frag_stmts E' K' \<subseteq> {n1..<n2}" using compile_procs_frag_range[OF assms(2)] .
  ultimately show ?thesis by fastforce
qed

subsection \<open>Public compiler invariants\<close>

text \<open>Every compiled program satisfies the generic CFG well-formedness conditions.\<close>
lemmas inv1_wf = compile_prog_wf

text \<open>Every call edge targets a procedure entry node.\<close>
theorem inv2_calls_to_entry:
  "(u, act, ce, af) \<in> calls (compile_prog \<Pi> ps mnm main) \<Longrightarrow> \<exists>p. ce = FunctionEntry p"
  using wf_call_targets_entry[OF compile_prog_wf] .

text \<open>Procedure entry nodes are reached only through call edges.\<close>
theorem inv3_no_intra_into_entry:
  "(u, a, v) \<in> intra (compile_prog \<Pi> ps mnm main) \<Longrightarrow> v \<noteq> FunctionEntry q"
  using wf_intra_not_into_entry[OF compile_prog_wf] .

text \<open>A return edge for procedure \<open>p\<close> targets its matching result node.\<close>
theorem inv4_ret_to_result:
  "(u, EA_Ret e p, v) \<in> intra (compile_prog \<Pi> ps mnm main) \<Longrightarrow> v = FunctionResult p"
  using edge_step_ret_target[OF compile_prog_wf] .

text \<open>Each procedure has entry and result nodes keyed by its name.  The wrapper emits the entry
  edge, and the procedure always carries some return edge into its result: the fall-through
  \<^term>\<open>EA_Ret None\<close> from the epilogue when the body can complete normally, and otherwise an
  explicit \<^term>\<open>EA_Ret e\<close> from inside the body (\<open>compile_returns_edge\<close>).  Distinct names yield
  distinct nodes.\<close>
theorem inv5_6_proc_entry_result_edges:
  assumes "compile_proc \<Pi> p decl n = (n', E, K)"
  shows "(\<exists>ben. (FunctionEntry p, EA_Nop, ben) \<in> E)
       \<and> (\<exists>bex e. (bex, EA_Ret e p, FunctionResult p) \<in> E)"
proof -
  from assms obtain Eb where
    cb: "compile \<Pi> p (body decl) (Statement (n + csize (body decl))) n
           = (n + csize (body decl), Statement n, Eb, K)"
    and E: "E = insert (FunctionEntry p, EA_Nop, Statement n)
                 (if falls_through (body decl)
                  then insert (Statement (n + csize (body decl)), EA_Ret None p, FunctionResult p) Eb
                  else Eb)"
    by (rule compile_procE)
  have "\<exists>bex e. (bex, EA_Ret e p, FunctionResult p) \<in> E"
  proof (cases "falls_through (body decl)")
    case True then show ?thesis using E by auto
  next
    case False
    then show ?thesis using compile_returns_edge[OF cb] E by auto
  qed
  then show ?thesis using E by auto
qed

theorem inv5_6_entry_result_distinct:
  "p \<noteq> q \<Longrightarrow> FunctionEntry p \<noteq> FunctionEntry q \<and> FunctionResult p \<noteq> FunctionResult q"
  by simp

text \<open>Every call continuation belongs to the compiled CFG.\<close>
theorem inv8_continuation_in_nodes:
  "(u, act, ce, af) \<in> calls (compile_prog \<Pi> ps mnm main)
   \<Longrightarrow> af \<in> cfg_nodes (compile_prog \<Pi> ps mnm main)"
  using call_endpoints_in_nodes(3) .

text \<open>Calls inhabit the separate \<open>calls\<close> relation.  Intra edges cannot carry call actions
  or reach procedure entry nodes.\<close>
theorem inv9_no_intra_call:
  "FunctionEntry p \<notin> intra_successors (compile_prog \<Pi> ps mnm main) u"
  using wf_no_intra_call[OF compile_prog_wf] .

text \<open>A \<open>Return\<close> fragment ignores its continuation: it emits its result edge and nothing
  else, so no node exists to carry a control flow the source does not have.\<close>
theorem inv11_return_ignores_continuation:
  "compile \<Pi> p (Return e) k n = compile \<Pi> p (Return e) k' n"
  by simp

text \<open>Normal fall-through reaches the procedure result through the edge emitted by
  \<open>compile_proc\<close>.\<close>
lemmas inv12_fallthrough = inv5_6_proc_entry_result_edges

text \<open>Return branches of the same procedure converge at \<open>FunctionResult p\<close>.\<close>
theorem inv13_multi_return_converge:
  assumes "compile \<Pi> p (If b (Return e1) (Return e2)) k n = (n', en, E, K)"
  shows "(\<exists>j. (Statement j, EA_Ret e1 p, FunctionResult p) \<in> E)
       \<and> (\<exists>j. (Statement j, EA_Ret e2 p, FunctionResult p) \<in> E)"
  using compile_return_edge[OF assms, of e1] compile_return_edge[OF assms, of e2] by simp

text \<open>A self-call targets the procedure's own entry node; its call site is an ordinary
  statement node and its continuation is the caller's own next program point.\<close>
theorem inv14_recursion_edge:
  "(Statement n, CallEdge None (case \<Pi> p of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) [],
    FunctionEntry p, k)
     \<in> snd (snd (snd (compile \<Pi> p (Call None p []) k n)))"
  by simp

text \<open>The program entry is the entry node of the distinguished root procedure.\<close>
theorem inv16_entry_is_main:
  "cfg_entry (compile_prog \<Pi> ps mnm main) = FunctionEntry mnm"
  unfolding compile_prog_def by (simp add: Let_def split: prod.splits)

subsection \<open>Parameter-binding exhibit: naive entry assignments are wrong\<close>

text \<open>
  Call actions retain their actual expressions because parameter binding evaluates them in
  the caller store.  Evaluating them after \<^const>\<open>enter_state\<close> would read reset local
  variables.  The witness below isolates this store-level distinction.
\<close>
lemma naive_entry_binding_wrong:
  "\<exists>s :: store. \<exists>x. \<not> is_global x \<and> enter_state s x \<noteq> s x"
proof (intro exI conjI)
  show "\<not> is_global ''y''" by (simp add: is_global_def)
  show "enter_state ((\<lambda>_. 0)(''y'' := (5 :: int))) ''y'' \<noteq> ((\<lambda>_. 0)(''y'' := (5 :: int))) ''y''"
    by (simp add: enter_state_def is_global_def)
qed


end

