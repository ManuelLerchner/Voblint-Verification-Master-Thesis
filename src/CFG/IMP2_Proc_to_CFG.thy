theory IMP2_Proc_to_CFG
  imports CFG_Def "Voblint_IMP2.IMP2_Proc"
begin

section \<open>Procedure-aware CFG compilation for \<open>com\<close> programs\<close>

text \<open>
  Compile a \<open>com\<close> program directly into the two-relation procedure-aware CFG.  Nodes are
  \<open>Statement n\<close> (allocated from a counter), \<open>FunctionEntry p\<close>, and \<open>FunctionResult p\<close>.
  The compiler threads the enclosing procedure name \<open>p\<close>, so a source \<open>Return\<close> and the
  normal fall-through both reach \<open>FunctionResult p\<close> through an \<open>EA_Ret\<close> intra edge.

  Layout of one procedure \<open>p\<close> with body \<open>b\<close> and declared result \<open>res\<close>:
    \<^item> \<open>FunctionEntry p --EA_Nop--> entry(b)\<close>;
    \<^item> the compiled body edges;
    \<^item> \<open>exit(b) --EA_Ret res p--> FunctionResult p\<close> (normal fall-through publishes the
       declared result);
    \<^item> each source \<open>Return e\<close> inside \<open>b\<close> compiles to \<open>--EA_Ret e p--> FunctionResult p\<close>
       (early return jumps to the result node; commands after the return sit behind a fresh
       unreachable exit node).

  Control effects and their source counterparts:
    \<^item> source lexical restoration (\<open>Scope\<close> / \<open>Restore\<close>) becomes ordinary intra flow ---
       \<open>Scope\<close> is a transparent \<open>EA_Nop\<close>-bracketed block (Goblint flattens lexical frames);
    \<^item> source \<open>Return\<close> / \<open>Unwind\<close> become an explicit \<open>EA_Ret\<close> edge into \<open>FunctionResult\<close>;
    \<^item> source activation handling becomes \<open>FunctionResult\<close> + the \<open>calls\<close>-edge continuation.

  Calls are emitted only into \<open>calls\<close>; a call never appears as an executable intra edge.
  \<open>Restore\<close> / \<open>Unwind\<close> are runtime-only (excluded by \<^const>\<open>source_com\<close>); their compile
  clauses are trivial one-node stubs that never occur for a source program.
\<close>

subsection \<open>Command compilation\<close>

text \<open>\<open>compile p c n\<close> returns \<open>(n', entry, normal_exit, intra_edges, call_edges)\<close>, allocating
  \<open>Statement\<close> indices in the counter range \<open>[n, n')\<close>.\<close>

fun compile ::
  "pname \<Rightarrow> com \<Rightarrow> nat
   \<Rightarrow> nat \<times> cfg_node \<times> cfg_node
        \<times> (cfg_node \<times> edge_action \<times> cfg_node) set
        \<times> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set"
where
  "compile p SKIP n = (Suc n, Statement n, Statement n, {}, {})"
| "compile p (Assign x a) n =
     (Suc (Suc n), Statement n, Statement (Suc n),
      {(Statement n, EA_Assign x a, Statement (Suc n))}, {})"
| "compile p (Seq c1 c2) n =
     (let (n1, en1, ex1, E1, K1) = compile p c1 n;
          (n2, en2, ex2, E2, K2) = compile p c2 n1
      in (n2, en1, ex2,
          E1 \<union> (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)}) \<union> E2,
          K1 \<union> K2))"
| "compile p (If b c1 c2) n =
     (let (n1, en1, ex1, E1, K1) = compile p c1 (Suc n);
          (n2, en2, ex2, E2, K2) = compile p c2 n1
      in (Suc n2, Statement n, Statement n2,
          {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
            \<union> E1 \<union> E2
            \<union> {(ex1, EA_Nop, Statement n2), (ex2, EA_Nop, Statement n2)},
          K1 \<union> K2))"
| "compile p (While b c) n =
     (let (n1, en1, ex1, E1, K1) = compile p c (Suc n)
      in (Suc n1, Statement n, Statement n1,
          {(Statement n, EA_Assume b, en1),
           (Statement n, EA_AssumeNot b, Statement n1),
           (ex1, EA_Nop, Statement n)} \<union> E1,
          K1))"
| "compile p (Scope c) n =
     (let (n1, en, ex, E, K) = compile p c (Suc n)
      in (Suc n1, Statement n, Statement n1,
          {(Statement n, EA_Nop, en), (ex, EA_Nop, Statement n1)} \<union> E,
          K))"
| "compile p (Call dst q actuals) n =
     (Suc (Suc n), Statement n, Statement (Suc n),
      {},
      {(Statement n, CallEdge dst actuals, FunctionEntry q, Statement (Suc n))})"
| "compile p (Return e) n =
     (Suc (Suc n), Statement n, Statement (Suc n),
      {(Statement n, EA_Ret e p, FunctionResult p)},
      {})"
| "compile p Restore n = (Suc n, Statement n, Statement n, {}, {})"
| "compile p Unwind n = (Suc n, Statement n, Statement n, {}, {})"

subsection \<open>Procedure and program compilation\<close>

text \<open>A procedure wraps its body between \<open>FunctionEntry p\<close> and \<open>FunctionResult p\<close>; the
  normal fall-through publishes the declared result through \<open>EA_Ret (result decl) p\<close>.\<close>

definition compile_proc ::
  "pname \<Rightarrow> proc_decl \<Rightarrow> nat
   \<Rightarrow> nat \<times> (cfg_node \<times> edge_action \<times> cfg_node) set
        \<times> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set"
where
  "compile_proc p decl n =
     (let (n', ben, bex, E, K) = compile p (body decl) n
      in (n',
          insert (FunctionEntry p, EA_Nop, ben)
            (insert (bex, EA_Ret (result decl) p, FunctionResult p) E),
          K))"

fun compile_procs ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> nat
   \<Rightarrow> nat \<times> (cfg_node \<times> edge_action \<times> cfg_node) set
        \<times> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set"
where
  "compile_procs \<Pi> [] n = (n, {}, {})"
| "compile_procs \<Pi> (p # ps) n =
     (case \<Pi> p of
        None \<Rightarrow> compile_procs \<Pi> ps n
      | Some decl \<Rightarrow>
          (let (n1, E, K) = compile_proc p decl n;
               (n2, E', K') = compile_procs \<Pi> ps n1
           in (n2, E \<union> E', K \<union> K')))"

text \<open>The whole program: every declared procedure, plus \<open>main\<close> compiled under the
  designated main name \<open>mnm\<close> (which the well-formedness predicate keeps disjoint from
  \<open>ps\<close>).  There is no global exit: whole-program completion is \<open>FunctionResult mnm\<close>, and the
  entry is \<open>FunctionEntry mnm\<close>.\<close>

definition compile_prog ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> cfg"
where
  "compile_prog \<Pi> ps mnm main =
     (let (n1, Eprocs, Kprocs) = compile_procs \<Pi> ps 0;
          (n2, Emain, Kmain) = compile_proc mnm (proc_decl_of [] main None) n1
      in \<lparr> intra = Eprocs \<union> Emain, calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm \<rparr>)"

subsection \<open>Counter monotonicity and statement ranges\<close>

lemma compile_counter_mono:
  "compile p c n = (n', en, ex, E, K) \<Longrightarrow> n \<le> n'"
proof (induction c arbitrary: n n' en ex E K rule: com.induct)
  case (Seq c1 c2)
  then obtain n1 en1 ex1 E1 K1 n2 en2 ex2 E2 K2 where
    c1: "compile p c1 n = (n1, en1, ex1, E1, K1)"
    and c2: "compile p c2 n1 = (n2, en2, ex2, E2, K2)" and n': "n' = n2"
    by (auto split: prod.splits)
  from Seq.IH(1)[OF c1] Seq.IH(2)[OF c2] n' show ?case by simp
next
  case (If b c1 c2)
  then obtain n1 en1 ex1 E1 K1 n2 en2 ex2 E2 K2 where
    c1: "compile p c1 (Suc n) = (n1, en1, ex1, E1, K1)"
    and c2: "compile p c2 n1 = (n2, en2, ex2, E2, K2)" and n': "n' = Suc n2"
    by (auto split: prod.splits)
  from If.IH(1)[OF c1] If.IH(2)[OF c2] n' show ?case by simp
next
  case (While b c)
  then obtain n1 en1 ex1 E1 K1 where
    c1: "compile p c (Suc n) = (n1, en1, ex1, E1, K1)" and n': "n' = Suc n1"
    by (auto split: prod.splits)
  from While.IH[OF c1] n' show ?case by simp
next
  case (Scope c)
  then obtain n1 en1 ex1 E1 K1 where
    c1: "compile p c (Suc n) = (n1, en1, ex1, E1, K1)" and n': "n' = Suc n1"
    by (auto split: prod.splits)
  from Scope.IH[OF c1] n' show ?case by simp
qed (auto split: prod.splits option.splits)

text \<open>The entry and normal-exit nodes are \<open>Statement\<close> nodes inside the counter range.\<close>
lemma compile_entry_exit_stmt:
  "compile p c n = (n', en, ex, E, K)
   \<Longrightarrow> (\<exists>k. en = Statement k \<and> n \<le> k \<and> k < n') \<and> (\<exists>k. ex = Statement k \<and> n \<le> k \<and> k < n')"
  by (induction c arbitrary: n n' en ex E K rule: com.induct)
     (auto split: prod.splits dest: compile_counter_mono,
      (meson le_less_trans less_imp_le_nat order_trans lessI Suc_leD)+)

text \<open>All \<open>Statement\<close> indices touched by a compiled fragment lie in its counter range.\<close>
definition frag_stmts ::
  "(cfg_node \<times> edge_action \<times> cfg_node) set
   \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set \<Rightarrow> nat set"
where
  "frag_stmts E K =
     {k. \<exists>a v. (Statement k, a, v) \<in> E} \<union> {k. \<exists>u a. (u, a, Statement k) \<in> E}
   \<union> {k. \<exists>act ce af. (Statement k, act, ce, af) \<in> K}
   \<union> {k. \<exists>u act ce. (u, act, ce, Statement k) \<in> K}"

lemma frag_stmts_empty [simp]: "frag_stmts {} {} = {}"
  by (simp add: frag_stmts_def)

lemma frag_stmts_Un:
  "frag_stmts (E1 \<union> E2) (K1 \<union> K2) = frag_stmts E1 K1 \<union> frag_stmts E2 K2"
  by (auto simp: frag_stmts_def)

lemma frag_stmts_mono:
  "E \<subseteq> E' \<Longrightarrow> K \<subseteq> K' \<Longrightarrow> frag_stmts E K \<subseteq> frag_stmts E' K'"
  by (auto simp: frag_stmts_def)

lemma compile_frag_stmts_range:
  "compile p c n = (n', en, ex, E, K) \<Longrightarrow> frag_stmts E K \<subseteq> {n..<n'}"
proof (induction c arbitrary: n n' en ex E K rule: com.induct)
  case SKIP then show ?case by (simp add: frag_stmts_def)
next
  case (Assign x a) then show ?case by (auto simp: frag_stmts_def)
next
  case (Seq c1 c2)
  from Seq.prems obtain n1 en1 ex1 E1 K1 n2 en2 ex2 E2 K2 where
    c1: "compile p c1 n = (n1, en1, ex1, E1, K1)"
    and c2: "compile p c2 n1 = (n2, en2, ex2, E2, K2)"
    and n': "n' = n2"
    and E: "E = E1 \<union> ((if ex1 = en2 then {} else {(ex1, EA_Nop, en2)}) \<union> E2)"
    and K: "K = K1 \<union> ({} \<union> K2)"
    by (auto split: prod.splits)
  have m1: "n \<le> n1" using compile_counter_mono[OF c1] .
  have m2: "n1 \<le> n2" using compile_counter_mono[OF c2] .
  have r1: "frag_stmts E1 K1 \<subseteq> {n..<n1}" using Seq.IH(1)[OF c1] .
  have r2: "frag_stmts E2 K2 \<subseteq> {n1..<n2}" using Seq.IH(2)[OF c2] .
  obtain ka where ex1: "ex1 = Statement ka" "n \<le> ka" "ka < n1"
    using compile_entry_exit_stmt[OF c1] by blast
  obtain kb where en2: "en2 = Statement kb" "n1 \<le> kb" "kb < n2"
    using compile_entry_exit_stmt[OF c2] by blast
  have opt: "frag_stmts (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)}) {} \<subseteq> {n..<n2}"
    using ex1 en2 m1 m2 by (auto simp: frag_stmts_def)
  have "frag_stmts E K
          = frag_stmts E1 K1
              \<union> (frag_stmts (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)}) {}
                   \<union> frag_stmts E2 K2)"
    unfolding E K by (simp only: frag_stmts_Un)
  also have "... \<subseteq> {n..<n2}" using r1 r2 opt m1 m2 by fastforce
  finally show ?case unfolding n' .
next
  case (If b c1 c2)
  from If.prems obtain n1 en1 ex1 E1 K1 n2 en2 ex2 E2 K2 where
    c1: "compile p c1 (Suc n) = (n1, en1, ex1, E1, K1)"
    and c2: "compile p c2 n1 = (n2, en2, ex2, E2, K2)"
    and n': "n' = Suc n2"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                  \<union> ({(ex1, EA_Nop, Statement n2), (ex2, EA_Nop, Statement n2)}
                       \<union> (E1 \<union> E2))"
    and K: "K = {} \<union> ({} \<union> (K1 \<union> K2))"
    by (auto split: prod.splits)
  have m1: "Suc n \<le> n1" using compile_counter_mono[OF c1] .
  have m2: "n1 \<le> n2" using compile_counter_mono[OF c2] .
  have r1: "frag_stmts E1 K1 \<subseteq> {Suc n..<n1}" using If.IH(1)[OF c1] .
  have r2: "frag_stmts E2 K2 \<subseteq> {n1..<n2}" using If.IH(2)[OF c2] .
  obtain k where en1: "en1 = Statement k" "Suc n \<le> k" "k < n1"
    using compile_entry_exit_stmt[OF c1] by blast
  obtain ka where en2: "en2 = Statement ka" "n1 \<le> ka" "ka < n2"
    using compile_entry_exit_stmt[OF c2] by blast
  obtain kb where ex1: "ex1 = Statement kb" "Suc n \<le> kb" "kb < n1"
    using compile_entry_exit_stmt[OF c1] by blast
  obtain kc where ex2: "ex2 = Statement kc" "n1 \<le> kc" "kc < n2"
    using compile_entry_exit_stmt[OF c2] by blast
  have asm: "frag_stmts {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)} {}
               \<subseteq> {n..<Suc n2}"
    using en1 en2 m1 m2 by (auto simp: frag_stmts_def)
  have nops: "frag_stmts {(ex1, EA_Nop, Statement n2), (ex2, EA_Nop, Statement n2)} {}
                \<subseteq> {n..<Suc n2}"
    using ex1 ex2 m1 m2 by (auto simp: frag_stmts_def)
  have "frag_stmts E K
          = frag_stmts {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)} {}
              \<union> (frag_stmts {(ex1, EA_Nop, Statement n2), (ex2, EA_Nop, Statement n2)} {}
                   \<union> (frag_stmts E1 K1 \<union> frag_stmts E2 K2))"
    unfolding E K by (simp only: frag_stmts_Un)
  also have "... \<subseteq> {n..<Suc n2}" using asm nops r1 r2 m1 m2 by fastforce
  finally show ?case unfolding n' .
next
  case (While b c)
  from While.prems obtain n1 en1 ex1 E1 K1 where
    c1: "compile p c (Suc n) = (n1, en1, ex1, E1, K1)"
    and n': "n' = Suc n1"
    and E: "E = {(Statement n, EA_Assume b, en1),
                 (Statement n, EA_AssumeNot b, Statement n1),
                 (ex1, EA_Nop, Statement n)} \<union> E1"
    and K: "K = {} \<union> K1"
    by (auto split: prod.splits)
  have m1: "Suc n \<le> n1" using compile_counter_mono[OF c1] .
  have r1: "frag_stmts E1 K1 \<subseteq> {Suc n..<n1}" using While.IH[OF c1] .
  obtain k where en1: "en1 = Statement k" "Suc n \<le> k" "k < n1"
    using compile_entry_exit_stmt[OF c1] by blast
  obtain ka where ex1: "ex1 = Statement ka" "Suc n \<le> ka" "ka < n1"
    using compile_entry_exit_stmt[OF c1] by blast
  have lit: "frag_stmts {(Statement n, EA_Assume b, en1),
                 (Statement n, EA_AssumeNot b, Statement n1),
                 (ex1, EA_Nop, Statement n)} {} \<subseteq> {n..<Suc n1}"
    using en1 ex1 m1 by (auto simp: frag_stmts_def)
  have "frag_stmts E K = frag_stmts {(Statement n, EA_Assume b, en1),
                 (Statement n, EA_AssumeNot b, Statement n1),
                 (ex1, EA_Nop, Statement n)} {} \<union> frag_stmts E1 K1"
    unfolding E K by (rule frag_stmts_Un)
  also have "... \<subseteq> {n..<Suc n1}" using lit r1 m1 by fastforce
  finally show ?case unfolding n' .
next
  case (Scope c)
  from Scope.prems obtain n1 en ex E1 K1 where
    c1: "compile p c (Suc n) = (n1, en, ex, E1, K1)"
    and n': "n' = Suc n1"
    and E: "E = {(Statement n, EA_Nop, en), (ex, EA_Nop, Statement n1)} \<union> E1"
    and K: "K = {} \<union> K1"
    by (auto split: prod.splits)
  have m1: "Suc n \<le> n1" using compile_counter_mono[OF c1] .
  have r1: "frag_stmts E1 K1 \<subseteq> {Suc n..<n1}" using Scope.IH[OF c1] .
  obtain k where en: "en = Statement k" "Suc n \<le> k" "k < n1"
    using compile_entry_exit_stmt[OF c1] by blast
  obtain ka where ex: "ex = Statement ka" "Suc n \<le> ka" "ka < n1"
    using compile_entry_exit_stmt[OF c1] by blast
  have lit: "frag_stmts {(Statement n, EA_Nop, en), (ex, EA_Nop, Statement n1)} {}
               \<subseteq> {n..<Suc n1}"
    using en ex m1 by (auto simp: frag_stmts_def)
  have "frag_stmts E K
          = frag_stmts {(Statement n, EA_Nop, en), (ex, EA_Nop, Statement n1)} {}
              \<union> frag_stmts E1 K1"
    unfolding E K by (rule frag_stmts_Un)
  also have "... \<subseteq> {n..<Suc n1}" using lit r1 m1 by fastforce
  finally show ?case unfolding n' .
next
  case (Call dst q actuals) then show ?case by (auto simp: frag_stmts_def)
next
  case (Return e) then show ?case by (auto simp: frag_stmts_def)
next
  case Restore then show ?case by (simp add: frag_stmts_def)
next
  case Unwind then show ?case by (simp add: frag_stmts_def)
qed

subsection \<open>Finiteness\<close>

lemma compile_finite:
  "compile p c n = (n', en, ex, E, K) \<Longrightarrow> finite E \<and> finite K"
  by (induction c arbitrary: n n' en ex E K rule: com.induct)
     (auto split: prod.splits)

lemma compile_proc_finite:
  "compile_proc p decl n = (n', E, K) \<Longrightarrow> finite E \<and> finite K"
  by (auto simp: compile_proc_def Let_def split: prod.splits dest: compile_finite)

lemma compile_procs_finite:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> finite E \<and> finite K"
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
      cp: "compile_proc p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')"
      and E: "E = E0 \<union> E'" and K: "K = K0 \<union> K'"
      by (auto split: prod.splits)
    from compile_proc_finite[OF cp] Cons.IH[OF rest] show ?thesis
      unfolding E K by simp
  qed
qed

lemma compile_prog_finite:
  "finite (intra (compile_prog \<Pi> ps mnm main))
   \<and> finite (calls (compile_prog \<Pi> ps mnm main))"
  unfolding compile_prog_def
  by (auto simp: Let_def split: prod.splits
       dest: compile_procs_finite compile_proc_finite)

subsection \<open>Edge shapes for well-formedness\<close>

text \<open>Every emitted call edge targets a \<open>FunctionEntry\<close>; a call is never an intra edge.\<close>
lemma compile_call_ce_entry:
  "compile p c n = (n', en, ex, E, K) \<Longrightarrow> (u, act, ce, af) \<in> K \<Longrightarrow> \<exists>q. ce = FunctionEntry q"
  by (induction c arbitrary: n n' en ex E K rule: com.induct)
     (auto split: prod.splits if_splits)

text \<open>No intra edge enters a \<open>FunctionEntry\<close> node.\<close>
lemma compile_intra_tgt_not_entry:
  "compile p c n = (n', en, ex, E, K) \<Longrightarrow> (u, a, v) \<in> E \<Longrightarrow> v \<noteq> FunctionEntry q"
  by (induction c arbitrary: n n' en ex E K rule: com.induct)
     (auto split: prod.splits if_splits dest: compile_entry_exit_stmt)

text \<open>Every \<open>EA_Ret\<close> edge lands on the matching \<open>FunctionResult\<close> --- the enclosing
  procedure name in the action equals the one in the target node.\<close>
lemma compile_ret_wf:
  "compile p c n = (n', en, ex, E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E \<Longrightarrow> v = FunctionResult q"
  by (induction c arbitrary: n n' en ex E K rule: com.induct)
     (auto split: prod.splits if_splits)

lemma compile_proc_call_ce_entry:
  "compile_proc p decl n = (n', E, K) \<Longrightarrow> (u, act, ce, af) \<in> K \<Longrightarrow> \<exists>q. ce = FunctionEntry q"
  by (auto simp: compile_proc_def Let_def split: prod.splits dest: compile_call_ce_entry)

lemma compile_proc_intra_tgt_not_entry:
  "compile_proc p decl n = (n', E, K) \<Longrightarrow> (u, a, v) \<in> E \<Longrightarrow> v \<noteq> FunctionEntry q"
  by (auto simp: compile_proc_def Let_def split: prod.splits
       dest: compile_intra_tgt_not_entry compile_entry_exit_stmt)

lemma compile_proc_ret_wf:
  "compile_proc p decl n = (n', E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E \<Longrightarrow> v = FunctionResult q"
  by (auto simp: compile_proc_def Let_def split: prod.splits dest: compile_ret_wf)

lemma compile_procs_call_ce_entry:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, act, ce, af) \<in> K \<Longrightarrow> \<exists>q. ce = FunctionEntry q"
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
      cp: "compile_proc p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')" and K: "K = K0 \<union> K'"
      by (auto split: prod.splits)
    from Cons.prems(2) K
    show ?thesis using compile_proc_call_ce_entry[OF cp] Cons.IH[OF rest] by auto
  qed
qed

lemma compile_procs_intra_tgt_not_entry:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, a, v) \<in> E \<Longrightarrow> v \<noteq> FunctionEntry q"
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
      cp: "compile_proc p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')" and E: "E = E0 \<union> E'"
      by (auto split: prod.splits)
    from Cons.prems(2) E
    show ?thesis using compile_proc_intra_tgt_not_entry[OF cp] Cons.IH[OF rest] by auto
  qed
qed

lemma compile_procs_ret_wf:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E \<Longrightarrow> v = FunctionResult q"
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
      cp: "compile_proc p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')" and E: "E = E0 \<union> E'"
      by (auto split: prod.splits)
    from Cons.prems(2) E
    show ?thesis using compile_proc_ret_wf[OF cp] Cons.IH[OF rest] by auto
  qed
qed

subsection \<open>The compiled program is well-formed\<close>

theorem compile_prog_wf: "wf_cfg (compile_prog \<Pi> ps mnm main)"
proof -
  obtain n1 Eprocs Kprocs where
    procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)" by (metis prod_cases3)
  obtain n2 Emain Kmain where
    mainc: "compile_proc mnm (proc_decl_of [] main None) n1 = (n2, Emain, Kmain)"
    by (metis prod_cases3)
  have g: "compile_prog \<Pi> ps mnm main =
             \<lparr> intra = Eprocs \<union> Emain, calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm \<rparr>"
    unfolding compile_prog_def by (simp add: procs mainc Let_def)
  show ?thesis
    unfolding wf_cfg_def g
  proof (intro conjI allI impI)
    fix u act ce af assume "(u, act, ce, af) \<in> calls \<lparr>intra = Eprocs \<union> Emain,
        calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm\<rparr>"
    then have "(u, act, ce, af) \<in> Kprocs \<or> (u, act, ce, af) \<in> Kmain" by simp
    then show "\<exists>p. ce = FunctionEntry p"
      using compile_procs_call_ce_entry[OF procs] compile_proc_call_ce_entry[OF mainc] by blast
  next
    fix u a v p assume "(u, a, v) \<in> intra \<lparr>intra = Eprocs \<union> Emain,
        calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm\<rparr>"
    then have "(u, a, v) \<in> Eprocs \<or> (u, a, v) \<in> Emain" by simp
    then show "v \<noteq> FunctionEntry p"
      using compile_procs_intra_tgt_not_entry[OF procs] compile_proc_intra_tgt_not_entry[OF mainc]
      by blast
  next
    fix u e p v assume "(u, EA_Ret e p, v) \<in> intra \<lparr>intra = Eprocs \<union> Emain,
        calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm\<rparr>"
    then have "(u, EA_Ret e p, v) \<in> Eprocs \<or> (u, EA_Ret e p, v) \<in> Emain" by simp
    then show "v = FunctionResult p"
      using compile_procs_ret_wf[OF procs] compile_proc_ret_wf[OF mainc] by blast
  qed
qed

end

