section \<open>Prototype: continuation-passing compilation\<close>

theory Example_CPS_Prototype
  imports Example_Compile_Baseline
begin

text \<open>
  Design validation for the continuation-passing compiler, run beside the current one instead
  of replacing it.  This is deliberately temporary: it exists to check the compilation rules
  and the allocation arithmetic against measured graphs before \<^const>\<open>compile\<close> itself is
  rewritten, and it is deleted at that point.  A permanently maintained second compiler is
  explicitly not the plan.

  The continuation is an input.  \<^const>\<open>Return\<close> ignores it, \<open>Seq\<close> hands \<open>c1\<close> the entry of
  \<open>c2\<close>, \<open>If\<close> hands both branches the same continuation and allocates no merge node, and
  \<open>While\<close> hands its body the loop head so the back-edge is the body's own last edge.
\<close>

subsection \<open>Allocation size under the new rules\<close>

fun ksize :: "com \<Rightarrow> nat" where
  "ksize SKIP = 1"
| "ksize (Assign x a) = 1"
| "ksize (Seq c1 c2) = ksize c1 + ksize c2"
| "ksize (If b c1 c2) = 1 + ksize c1 + ksize c2"
| "ksize (While b c) = 1 + ksize c"
| "ksize (Call dst q actuals) = 1"
| "ksize (Return e) = 1"
| "ksize Restore = 1"
| "ksize Unwind = 1"

subsection \<open>The continuation-passing clauses\<close>

fun compile_k ::
  "proc_table \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> cfg_node \<Rightarrow> nat
   \<Rightarrow> nat \<times> cfg_node
        \<times> (cfg_node \<times> edge_action \<times> cfg_node) set
        \<times> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set"
where
  "compile_k \<Pi> p SKIP k n =
     (Suc n, Statement n, {(Statement n, EA_Nop, k)}, {})"
| "compile_k \<Pi> p (Assign x a) k n =
     (Suc n, Statement n, {(Statement n, EA_Assign x a, k)}, {})"
| "compile_k \<Pi> p (Seq c1 c2) k n =
     (let m = n + ksize c1;
          (n1, en1, E1, K1) = compile_k \<Pi> p c1 (Statement m) n;
          (n2, en2, E2, K2) = compile_k \<Pi> p c2 k m
      in (n2, en1, E1 \<union> E2, K1 \<union> K2))"
| "compile_k \<Pi> p (If b c1 c2) k n =
     (let (n1, en1, E1, K1) = compile_k \<Pi> p c1 k (Suc n);
          (n2, en2, E2, K2) = compile_k \<Pi> p c2 k n1
      in (n2, Statement n,
          {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
            \<union> E1 \<union> E2,
          K1 \<union> K2))"
| "compile_k \<Pi> p (While b c) k n =
     (let (n1, en1, E1, K1) = compile_k \<Pi> p c (Statement n) (Suc n)
      in (n1, Statement n,
          {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)} \<union> E1,
          K1))"
| "compile_k \<Pi> p (Call dst q actuals) k n =
     (Suc n, Statement n, {},
      {(Statement n,
        CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
        FunctionEntry q, k)})"
| "compile_k \<Pi> p (Return e) k n =
     (Suc n, Statement n, {(Statement n, EA_Ret e p, FunctionResult p)}, {})"
| "compile_k \<Pi> p Restore k n = (Suc n, Statement n, {}, {})"
| "compile_k \<Pi> p Unwind k n = (Suc n, Statement n, {}, {})"

subsection \<open>The two structural invariants\<close>

text \<open>The allocation obligation.  \<open>Seq\<close> predicts \<open>c2\<close>'s entry as \<open>Statement (n + ksize c1)\<close>
  before compiling \<open>c1\<close>, so the design is only sound if \<open>ksize\<close> agrees exactly with what the
  clauses allocate.  This is the lemma that would fail first if a clause and its size ever
  drifted apart.\<close>

theorem compile_k_next_id:
  "compile_k \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> n' = n + ksize c"
proof (induction c arbitrary: k n n' en E K rule: com.induct)
  case (Seq c1 c2)
  then obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile_k \<Pi> p c1 (Statement (n + ksize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile_k \<Pi> p c2 k (n + ksize c1) = (n2, en2, E2, K2)"
    and n': "n' = n2"
    by (auto simp: Let_def split: prod.splits)
  from Seq.IH(2)[OF c2] n' show ?case by simp
next
  case (If b c1 c2)
  then obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile_k \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile_k \<Pi> p c2 k n1 = (n2, en2, E2, K2)" and n': "n' = n2"
    by (auto split: prod.splits)
  from If.IH(1)[OF c1] If.IH(2)[OF c2] n' show ?case by simp
next
  case (While b c)
  then obtain n1 en1 E1 K1 where
    c1: "compile_k \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)" and n': "n' = n1"
    by (auto split: prod.splits)
  from While.IH[OF c1] n' show ?case by simp
qed (auto split: prod.splits option.splits)

text \<open>Every fragment still enters at its base counter, so \<open>compile_entry_node\<close> survives the
  redesign unchanged --- the reason \<^const>\<open>SKIP\<close> keeps a node of its own.\<close>

theorem compile_k_entry:
  "compile_k \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> en = Statement n"
  by (induction c arbitrary: k n n' en E K rule: com.induct)
     (auto simp: Let_def split: prod.splits)

text \<open>\<^const>\<open>Return\<close> ignores its continuation: the fragment is independent of \<open>k\<close>.\<close>

lemma compile_k_Return_ignores_continuation:
  "compile_k \<Pi> p (Return e) k n = compile_k \<Pi> p (Return e) k' n"
  by simp

subsection \<open>Procedure and program layer\<close>

text \<open>The epilogue node \<open>Statement r\<close> is allocated after the body and carries the implicit
  \<open>EA_Ret None\<close>, so every edge into \<^term>\<open>FunctionResult p\<close> is still a return edge.  It is
  inside the procedure's own counter range, which is what keeps the command-level
  continuation generalisation from leaking into procedure-level locality.\<close>

definition compile_proc_k ::
  "proc_table \<Rightarrow> pname \<Rightarrow> proc_decl \<Rightarrow> nat
   \<Rightarrow> nat \<times> (cfg_node \<times> edge_action \<times> cfg_node) set
        \<times> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set"
where
  "compile_proc_k \<Pi> p decl n =
     (let r = n + ksize (body decl);
          (n', ben, E, K) = compile_k \<Pi> p (body decl) (Statement r) n
      in (Suc r,
          insert (FunctionEntry p, EA_Nop, ben)
            (insert (Statement r, EA_Ret None p, FunctionResult p) E),
          K))"

fun compile_procs_k ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> nat
   \<Rightarrow> nat \<times> (cfg_node \<times> edge_action \<times> cfg_node) set
        \<times> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set"
where
  "compile_procs_k \<Pi> [] n = (n, {}, {})"
| "compile_procs_k \<Pi> (p # ps) n =
     (case \<Pi> p of
        None \<Rightarrow> compile_procs_k \<Pi> ps n
      | Some decl \<Rightarrow>
          (let (n1, E, K) = compile_proc_k \<Pi> p decl n;
               (n2, E', K') = compile_procs_k \<Pi> ps n1
           in (n2, E \<union> E', K \<union> K')))"

definition compile_prog_k ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> cfg"
where
  "compile_prog_k \<Pi> ps mnm main =
     (let (n1, Eprocs, Kprocs) = compile_procs_k \<Pi> ps 0;
          (n2, Emain, Kmain) = compile_proc_k \<Pi> mnm (proc_decl_of [] main) n1
      in \<lparr> intra = Eprocs \<union> Emain, calls = Kprocs \<union> Kmain,
           cfg_entry = FunctionEntry mnm \<rparr>)"

definition prog_cfg_k :: "imp_prog \<Rightarrow> cfg" where
  "prog_cfg_k P = compile_prog_k (prog_table P) (prog_procs P) ''main'' (prog_main P)"

subsection \<open>Structural well-formedness survives the redesign\<close>

text \<open>The three \<^const>\<open>wf_cfg\<close> conditions, at command level.  Note the extra hypothesis on
  the second: \<^const>\<open>SKIP\<close> emits an edge into its continuation, so "no intra edge enters a
  procedure entry" now depends on the continuation not being one.  At procedure level the
  continuation is the epilogue \<open>Statement r\<close> and the hypothesis discharges by \<open>simp\<close>.\<close>

lemma compile_k_call_ce_entry:
  "compile_k \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, act, ce, af) \<in> K
   \<Longrightarrow> \<exists>q. ce = FunctionEntry q"
  by (induction c arbitrary: k n n' en E K)
     (auto simp: Let_def split: prod.splits if_splits)

text \<open>Edge endpoints: a source is always an allocated \<open>Statement\<close>, and a target is an
  allocated \<open>Statement\<close>, the own \<^term>\<open>FunctionResult p\<close>, or the continuation.  This is the
  continuation-passing analogue of \<open>compile_E_shape\<close>, and the shape that makes the
  "no intra edge enters a procedure entry" condition provable without carrying a side
  condition through the induction.\<close>

lemma compile_k_E_shape:
  "compile_k \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, a, v) \<in> E
   \<Longrightarrow> (\<exists>j. u = Statement j)
       \<and> (v = k \<or> v = FunctionResult p \<or> (\<exists>j. v = Statement j))"
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  then obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile_k \<Pi> p c1 (Statement (n + ksize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile_k \<Pi> p c2 k (n + ksize c1) = (n2, en2, E2, K2)"
    and E: "E = E1 \<union> E2"
    by (auto simp: Let_def split: prod.splits)
  consider (L) "(u, a, v) \<in> E1" | (R) "(u, a, v) \<in> E2"
    using Seq.prems(2) E by auto
  then show ?case
  proof cases
    case L from Seq.IH(1)[OF c1 L] show ?thesis by auto
  next
    case R from Seq.IH(2)[OF c2 R] show ?thesis by auto
  qed
next
  case (If b c1 c2)
  then obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile_k \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile_k \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                  \<union> E1 \<union> E2"
    by (auto split: prod.splits)
  have e1: "en1 = Statement (Suc n)" using compile_k_entry[OF c1] .
  have e2: "en2 = Statement n1" using compile_k_entry[OF c2] .
  consider (Guard) "(u, a, v) \<in> {(Statement n, EA_Assume b, en1),
                                 (Statement n, EA_AssumeNot b, en2)}"
    | (L) "(u, a, v) \<in> E1" | (R) "(u, a, v) \<in> E2"
    using If.prems(2) E by auto
  then show ?case
  proof cases
    case Guard then show ?thesis using e1 e2 by auto
  next
    case L from If.IH(1)[OF c1 L] show ?thesis by auto
  next
    case R from If.IH(2)[OF c2 R] show ?thesis by auto
  qed
next
  case (While b c)
  then obtain n1 en1 E1 K1 where
    c1: "compile_k \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)} \<union> E1"
    by (auto split: prod.splits)
  have e1: "en1 = Statement (Suc n)" using compile_k_entry[OF c1] .
  consider (Guard) "(u, a, v) \<in> {(Statement n, EA_Assume b, en1),
                                 (Statement n, EA_AssumeNot b, k)}"
    | (Body) "(u, a, v) \<in> E1"
    using While.prems(2) E by auto
  then show ?case
  proof cases
    case Guard then show ?thesis using e1 by auto
  next
    case Body from While.IH[OF c1 Body] show ?thesis by auto
  qed
qed (auto split: prod.splits option.splits)

lemma compile_k_ret_wf:
  "compile_k \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E
   \<Longrightarrow> \<forall>r. k \<noteq> FunctionResult r \<Longrightarrow> v = FunctionResult q"
  by (induction c arbitrary: k n n' en E K)
     (auto simp: Let_def split: prod.splits if_splits)

lemma compile_proc_k_call_ce_entry:
  "compile_proc_k \<Pi> p decl n = (n', E, K) \<Longrightarrow> (u, act, ce, af) \<in> K
   \<Longrightarrow> \<exists>q. ce = FunctionEntry q"
  by (auto simp: compile_proc_k_def Let_def split: prod.splits
       dest: compile_k_call_ce_entry)

lemma compile_proc_k_intra_tgt_not_entry:
  "compile_proc_k \<Pi> p decl n = (n', E, K) \<Longrightarrow> (u, a, v) \<in> E
   \<Longrightarrow> v \<noteq> FunctionEntry q"
  by (auto simp: compile_proc_k_def Let_def split: prod.splits
       dest: compile_k_E_shape compile_k_entry)

lemma compile_proc_k_ret_wf:
  "compile_proc_k \<Pi> p decl n = (n', E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E
   \<Longrightarrow> v = FunctionResult q"
  by (auto simp: compile_proc_k_def Let_def split: prod.splits
       dest: compile_k_ret_wf)

lemma compile_procs_k_call_ce_entry:
  "compile_procs_k \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, act, ce, af) \<in> K
   \<Longrightarrow> \<exists>q. ce = FunctionEntry q"
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
      cp: "compile_proc_k \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs_k \<Pi> ps n1 = (n2, E', K')" and K: "K = K0 \<union> K'"
      by (auto split: prod.splits)
    from Cons.prems(2) K
    show ?thesis using compile_proc_k_call_ce_entry[OF cp] Cons.IH[OF rest] by auto
  qed
qed

lemma compile_procs_k_intra_tgt_not_entry:
  "compile_procs_k \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, a, v) \<in> E
   \<Longrightarrow> v \<noteq> FunctionEntry q"
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
      cp: "compile_proc_k \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs_k \<Pi> ps n1 = (n2, E', K')" and E: "E = E0 \<union> E'"
      by (auto split: prod.splits)
    from Cons.prems(2) E
    show ?thesis using compile_proc_k_intra_tgt_not_entry[OF cp] Cons.IH[OF rest] by auto
  qed
qed

lemma compile_procs_k_ret_wf:
  "compile_procs_k \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E
   \<Longrightarrow> v = FunctionResult q"
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
      cp: "compile_proc_k \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs_k \<Pi> ps n1 = (n2, E', K')" and E: "E = E0 \<union> E'"
      by (auto split: prod.splits)
    from Cons.prems(2) E
    show ?thesis using compile_proc_k_ret_wf[OF cp] Cons.IH[OF rest] by auto
  qed
qed

theorem compile_prog_k_wf: "wf_cfg (compile_prog_k \<Pi> ps mnm main)"
proof -
  obtain n1 Eprocs Kprocs where
    procs: "compile_procs_k \<Pi> ps 0 = (n1, Eprocs, Kprocs)" by (metis prod_cases3)
  obtain n2 Emain Kmain where
    mainc: "compile_proc_k \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    by (metis prod_cases3)
  have g: "compile_prog_k \<Pi> ps mnm main =
             \<lparr> intra = Eprocs \<union> Emain, calls = Kprocs \<union> Kmain,
               cfg_entry = FunctionEntry mnm \<rparr>"
    unfolding compile_prog_k_def by (simp add: procs mainc Let_def)
  show ?thesis
    unfolding wf_cfg_def g
  proof (intro conjI allI impI)
    fix u act ce af
    assume "(u, act, ce, af) \<in> calls \<lparr>intra = Eprocs \<union> Emain,
        calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm\<rparr>"
    then have "(u, act, ce, af) \<in> Kprocs \<or> (u, act, ce, af) \<in> Kmain" by simp
    then show "\<exists>p. ce = FunctionEntry p"
      using compile_procs_k_call_ce_entry[OF procs]
            compile_proc_k_call_ce_entry[OF mainc] by blast
  next
    fix u a v p
    assume "(u, a, v) \<in> intra \<lparr>intra = Eprocs \<union> Emain,
        calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm\<rparr>"
    then have "(u, a, v) \<in> Eprocs \<or> (u, a, v) \<in> Emain" by simp
    then show "v \<noteq> FunctionEntry p"
      using compile_procs_k_intra_tgt_not_entry[OF procs]
            compile_proc_k_intra_tgt_not_entry[OF mainc] by blast
  next
    fix u e p v
    assume "(u, EA_Ret e p, v) \<in> intra \<lparr>intra = Eprocs \<union> Emain,
        calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm\<rparr>"
    then have "(u, EA_Ret e p, v) \<in> Eprocs \<or> (u, EA_Ret e p, v) \<in> Emain" by simp
    then show "v = FunctionResult p"
      using compile_procs_k_ret_wf[OF procs] compile_proc_k_ret_wf[OF mainc] by blast
  qed
qed

subsection \<open>Measured effect on the factorial example\<close>

definition factorial_cfg_k :: cfg where
  "factorial_cfg_k = prog_cfg_k factorial_program"

value "all_nodes_list factorial_cfg_k"

value "dead_list factorial_cfg_k"

value "nop_edge_list factorial_cfg_k"

value "cfg_report factorial_cfg_k"

subsection \<open>Side by side, all regression programs\<close>

text \<open>Each entry is \<open>(current, continuation-passing)\<close> with rows
  \<open>(nodes, dead, intra, nops, calls)\<close>.  The \<open>dead\<close> and \<open>nops\<close> columns are the ones the
  redesign targets; \<open>calls\<close> must be unchanged, since the call relation is not touched.\<close>

value "map (\<lambda>P. (cfg_report (prog_cfg P), cfg_report (prog_cfg_k P)))
  [p01_skip, p02_assign, p03_return, p04_return_then_dead,
   p05_if_both_return, p06_if_one_returns, p07_while_body_returns, p08_nested_if]"

value "map (\<lambda>P. (cfg_report (prog_cfg P), cfg_report (prog_cfg_k P)))
  [p09_one_call, factorial_program, p11_nested_calls, p12_two_call_sites,
   p13_after_guaranteed_return, p14_main_only]"

text \<open>Glue nops are gone everywhere: under the redesign every remaining \<^term>\<open>EA_Nop\<close> is
  either a procedure-entry bracket or a source-level \<^const>\<open>SKIP\<close>.\<close>

value "map (\<lambda>P. (length (nop_edge_list (prog_cfg P)), length (nop_edge_list (prog_cfg_k P))))
  [p01_skip, p02_assign, p03_return, p04_return_then_dead,
   p05_if_both_return, p06_if_one_returns, p07_while_body_returns, p08_nested_if,
   p09_one_call, factorial_program, p11_nested_calls, p12_two_call_sites,
   p13_after_guaranteed_return, p14_main_only]"

text \<open>Observable traces agree: the redesign changes node identities, not behaviour.\<close>

value "trace_from_entry (prog_cfg_k p02_assign) zero_store 20
         = trace_from_entry (prog_cfg p02_assign) zero_store 20"

value "trace_from_entry (prog_cfg_k p06_if_one_returns) zero_store 20
         = trace_from_entry (prog_cfg p06_if_one_returns) zero_store 20"

value "trace_from_entry factorial_cfg_k zero_store 200
         = trace_from_entry factorial_cfg zero_store 200"

end
