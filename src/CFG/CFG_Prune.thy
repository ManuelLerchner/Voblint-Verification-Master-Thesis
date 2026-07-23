theory CFG_Prune
  imports IMP2_Proc_to_CFG
begin

section \<open>Procedure-aware structural reachability and dependency cone\<close>

text \<open>
  \<open>cfg_succ_rel\<close> is the derived structural dependency graph the analysis pruning and
  cone proofs run on --- not the concrete execution relation.  It has four sources,
  induced by \<open>intra g\<close> and \<open>calls g\<close>:

  \<^item> INTRA: an ordinary edge \<open>(u, a, v) \<in> intra g\<close> gives \<open>u \<rightarrow> v\<close> (ordinary flow).
  \<^item> ENTRY: a call \<open>(c, ca, FunctionEntry p, k) \<in> calls g\<close> gives \<open>c \<rightarrow> FunctionEntry p\<close> ---
    the callee entry's abstract state depends on the caller state routed through
    \<open>etf_enter\<close>.
  \<^item> COMB_CALLER: the same call gives \<open>c \<rightarrow> k\<close> --- the continuation depends on the saved
    caller state via \<open>etf_combine\<close>.  This is not a concrete execution edge; execution
    does not skip the callee.
  \<^item> COMB_RESULT: the same call gives \<open>FunctionResult p \<rightarrow> k\<close> --- the continuation depends
    on the callee's result, the second \<open>etf_combine\<close> argument.

  \<open>c \<rightarrow> k\<close> and \<open>FunctionResult p \<rightarrow> k\<close> are combine dependencies of the analysis, kept
  visibly separate from \<open>intra g\<close>.  They are never added to \<open>intra g\<close>.
\<close>

subsection \<open>The structural successor relation\<close>

definition cfg_succ_rel :: "cfg \<Rightarrow> (cfg_node \<times> cfg_node) set" where
  "cfg_succ_rel g =
     {(u, v) | u a v. (u, a, v) \<in> intra g}
   \<union> {(c, ce) | c ca ce k. (c, ca, ce, k) \<in> calls g}
   \<union> {(c, k) | c ca ce k. (c, ca, ce, k) \<in> calls g}
   \<union> {(FunctionResult p, k) | c ca p k. (c, ca, FunctionEntry p, k) \<in> calls g}"

lemma cfg_succ_rel_intra:
  "(u, a, v) \<in> intra g \<Longrightarrow> (u, v) \<in> cfg_succ_rel g"
  unfolding cfg_succ_rel_def by blast

lemma cfg_succ_rel_entry:
  "(c, ca, ce, k) \<in> calls g \<Longrightarrow> (c, ce) \<in> cfg_succ_rel g"
  unfolding cfg_succ_rel_def by blast

lemma cfg_succ_rel_comb_caller:
  "(c, ca, ce, k) \<in> calls g \<Longrightarrow> (c, k) \<in> cfg_succ_rel g"
  unfolding cfg_succ_rel_def by blast

lemma cfg_succ_rel_comb_result:
  "(c, ca, FunctionEntry p, k) \<in> calls g \<Longrightarrow> (FunctionResult p, k) \<in> cfg_succ_rel g"
  unfolding cfg_succ_rel_def by blast

text \<open>The four structural cases of a single successor step.\<close>
lemma cfg_succ_rel_cases:
  assumes "(y, z) \<in> cfg_succ_rel g"
  obtains (INTRA) a where "(y, a, z) \<in> intra g"
    | (ENTRY) ca k where "(y, ca, z, k) \<in> calls g"
    | (COMB_CALLER) ca ce where "(y, ca, ce, z) \<in> calls g"
    | (COMB_RESULT) c ca p k where "(c, ca, FunctionEntry p, k) \<in> calls g"
                                   "y = FunctionResult p" "z = k"
  using assms unfolding cfg_succ_rel_def by blast

lemma cfg_succ_rel_mono:
  assumes "intra g1 \<subseteq> intra g2" "calls g1 \<subseteq> calls g2"
  shows "cfg_succ_rel g1 \<subseteq> cfg_succ_rel g2"
  using assms unfolding cfg_succ_rel_def by blast

subsection \<open>Reachability: reflexive-transitive closure of the successor relation\<close>

definition cfg_succ :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node \<Rightarrow> bool" where
  "cfg_succ g u w \<longleftrightarrow> (u, w) \<in> cfg_succ_rel g"

definition cfg_reaches :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node \<Rightarrow> bool" where
  "cfg_reaches g v v0 \<longleftrightarrow> (v, v0) \<in> (cfg_succ_rel g)\<^sup>*"

definition cone :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node set" where
  "cone g v0 = {v. cfg_reaches g v v0}"

lemma cfg_reaches_refl: "cfg_reaches g v v"
  by (simp add: cfg_reaches_def)

lemma cfg_succ_reaches:
  "cfg_succ g u w \<Longrightarrow> cfg_reaches g w v0 \<Longrightarrow> cfg_reaches g u v0"
  by (auto simp: cfg_succ_def cfg_reaches_def intro: converse_rtrancl_into_rtrancl)

lemma cfg_succ_imp_reaches: "cfg_succ g u w \<Longrightarrow> cfg_reaches g u w"
  using cfg_succ_reaches cfg_reaches_refl by blast

lemma cfg_reaches_trans:
  "cfg_reaches g a b \<Longrightarrow> cfg_reaches g b c \<Longrightarrow> cfg_reaches g a c"
  by (auto simp: cfg_reaches_def)

lemma cfg_reaches_mono:
  assumes "intra g1 \<subseteq> intra g2" "calls g1 \<subseteq> calls g2" "cfg_reaches g1 v w"
  shows "cfg_reaches g2 v w"
proof -
  have "(cfg_succ_rel g1)\<^sup>* \<subseteq> (cfg_succ_rel g2)\<^sup>*"
    by (rule rtrancl_mono) (rule cfg_succ_rel_mono[OF assms(1,2)])
  thus ?thesis using assms(3) unfolding cfg_reaches_def by blast
qed

subsection \<open>Forward one-step reachability for each source\<close>

lemma cfg_reaches_intra:
  "(u, a, v) \<in> intra g \<Longrightarrow> cfg_reaches g u v"
  by (rule cfg_succ_imp_reaches) (simp add: cfg_succ_def cfg_succ_rel_intra)

lemma cfg_reaches_entry:
  "(c, ca, ce, k) \<in> calls g \<Longrightarrow> cfg_reaches g c ce"
  by (rule cfg_succ_imp_reaches) (simp add: cfg_succ_def cfg_succ_rel_entry)

lemma cfg_reaches_comb_caller:
  "(c, ca, ce, k) \<in> calls g \<Longrightarrow> cfg_reaches g c k"
  by (rule cfg_succ_imp_reaches) (simp add: cfg_succ_def cfg_succ_rel_comb_caller)

lemma cfg_reaches_comb_result:
  "(c, ca, FunctionEntry p, k) \<in> calls g \<Longrightarrow> cfg_reaches g (FunctionResult p) k"
  by (rule cfg_succ_imp_reaches) (simp add: cfg_succ_def cfg_succ_rel_comb_result)

subsection \<open>Backward reachability across a step (source reaches what the target reaches)\<close>

lemma cfg_reaches_intra_src:
  assumes "(u, a, v) \<in> intra g" and "cfg_reaches g v v0"
  shows "cfg_reaches g u v0"
proof -
  have "cfg_succ g u v" using cfg_succ_rel_intra[OF assms(1)] by (simp add: cfg_succ_def)
  thus ?thesis using assms(2) by (rule cfg_succ_reaches)
qed

lemma cfg_reaches_entry_src:
  assumes "(c, ca, ce, k) \<in> calls g" and "cfg_reaches g ce v0"
  shows "cfg_reaches g c v0"
proof -
  have "cfg_succ g c ce" using cfg_succ_rel_entry[OF assms(1)] by (simp add: cfg_succ_def)
  thus ?thesis using assms(2) by (rule cfg_succ_reaches)
qed

lemma cfg_reaches_comb_caller_src:
  assumes "(c, ca, ce, k) \<in> calls g" and "cfg_reaches g k v0"
  shows "cfg_reaches g c v0"
proof -
  have "cfg_succ g c k" using cfg_succ_rel_comb_caller[OF assms(1)] by (simp add: cfg_succ_def)
  thus ?thesis using assms(2) by (rule cfg_succ_reaches)
qed

lemma cfg_reaches_comb_result_src:
  assumes "(c, ca, FunctionEntry p, k) \<in> calls g" and "cfg_reaches g k v0"
  shows "cfg_reaches g (FunctionResult p) v0"
proof -
  have "cfg_succ g (FunctionResult p) k"
    using cfg_succ_rel_comb_result[OF assms(1)] by (simp add: cfg_succ_def)
  thus ?thesis using assms(2) by (rule cfg_succ_reaches)
qed

subsection \<open>Whole-program exit node\<close>

text \<open>Whole-program completion is the entry procedure's \<open>FunctionResult\<close>: the compiler
  sets \<open>cfg_entry (compile_prog \<dots> mnm \<dots>) = FunctionEntry mnm\<close>, so \<open>cfg_exit\<close> is
  \<open>FunctionResult mnm\<close>.\<close>
definition cfg_exit :: "cfg \<Rightarrow> cfg_node" where
  "cfg_exit g = (case cfg_entry g of FunctionEntry p \<Rightarrow> FunctionResult p | n \<Rightarrow> n)"

lemma cfg_exit_compile_prog:
  "cfg_exit (compile_prog \<Pi> ps mnm main) = FunctionResult mnm"
  unfolding cfg_exit_def by (simp add: compile_prog_def Let_def split: prod.splits)

subsection \<open>Compiled entry reaches its exit or its procedure result\<close>

text \<open>Along the derived successor relation, a compiled command's entry reaches either
  its fall-through exit or (via an early \<open>Return\<close>) the enclosing procedure's
  \<open>FunctionResult\<close>.  A call site reaches its continuation through the COMB_CALLER
  dependency, so no callee fragment is needed.\<close>
lemma compile_reaches:
  fixes g :: cfg
  shows "compile \<Pi> p c n = (n', en, ex, E, K)
     \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> K \<subseteq> calls g
     \<Longrightarrow> cfg_reaches g en ex \<or> cfg_reaches g en (FunctionResult p)"
proof (induction c arbitrary: n n' en ex E K)
  case SKIP
  then have "en = ex" by (auto split: prod.splits)
  then show ?case by (simp add: cfg_reaches_refl)
next
  case (Assign x a)
  then have en: "en = Statement n" and ex: "ex = Statement (Suc n)"
    and mem: "(Statement n, EA_Assign x a, Statement (Suc n)) \<in> intra g"
    by (auto split: prod.splits)
  from mem have "cfg_reaches g en ex" unfolding en ex by (rule cfg_reaches_intra)
  then show ?case ..
next
  case (Seq c1 c2)
  obtain n1 en1 ex1 E1 K1 n2 en2 ex2 E2 K2 where
      c1': "compile \<Pi> p c1 n = (n1, en1, ex1, E1, K1)"
    and c2': "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    and res: "en = en1" "ex = ex2"
             "E = E1 \<union> (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)}) \<union> E2"
             "K = K1 \<union> K2"
    using Seq.prems(1) by (auto split: prod.splits)
  have E1g: "E1 \<subseteq> intra g" and E2g: "E2 \<subseteq> intra g" using res Seq.prems(2) by auto
  have K1g: "K1 \<subseteq> calls g" and K2g: "K2 \<subseteq> calls g" using res Seq.prems(3) by auto
  have step12: "cfg_reaches g ex1 en2"
  proof (cases "ex1 = en2")
    case True then show ?thesis by (simp add: cfg_reaches_refl)
  next
    case False
    then have "(ex1, EA_Nop, en2) \<in> intra g" using res Seq.prems(2) by auto
    then show ?thesis by (rule cfg_reaches_intra)
  qed
  consider (r1) "cfg_reaches g en1 ex1" | (res1) "cfg_reaches g en1 (FunctionResult p)"
    using Seq.IH(1)[OF c1' E1g K1g] by blast
  then show ?case
  proof cases
    case res1 then show ?thesis using res by simp
  next
    case r1
    consider (r2) "cfg_reaches g en2 ex2" | (res2) "cfg_reaches g en2 (FunctionResult p)"
      using Seq.IH(2)[OF c2' E2g K2g] by blast
    then show ?thesis
    proof cases
      case r2
      have "cfg_reaches g en1 ex2" by (meson r1 step12 r2 cfg_reaches_trans)
      then show ?thesis using res by simp
    next
      case res2
      have "cfg_reaches g en1 (FunctionResult p)" by (meson r1 step12 res2 cfg_reaches_trans)
      then show ?thesis using res by simp
    qed
  qed
next
  case (If b c1 c2)
  obtain n1 en1 ex1 E1 K1 n2 en2 ex2 E2 K2 where
      c1': "compile \<Pi> p c1 (Suc n) = (n1, en1, ex1, E1, K1)"
    and c2': "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    and res: "en = Statement n" "ex = Statement n2"
             "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                    \<union> E1 \<union> E2
                    \<union> {(ex1, EA_Nop, Statement n2), (ex2, EA_Nop, Statement n2)}"
             "K = K1 \<union> K2"
    using If.prems(1) by (auto split: prod.splits)
  have E1g: "E1 \<subseteq> intra g" and K1g: "K1 \<subseteq> calls g" using res If.prems(2,3) by auto
  have e_en1: "cfg_reaches g (Statement n) en1"
    using res If.prems(2) by (auto intro: cfg_reaches_intra)
  have ex1_ex: "cfg_reaches g ex1 (Statement n2)"
    using res If.prems(2) by (auto intro: cfg_reaches_intra)
  consider (r1) "cfg_reaches g en1 ex1" | (res1) "cfg_reaches g en1 (FunctionResult p)"
    using If.IH(1)[OF c1' E1g K1g] by blast
  then show ?case
  proof cases
    case r1
    have "cfg_reaches g (Statement n) (Statement n2)"
      by (meson e_en1 r1 ex1_ex cfg_reaches_trans)
    then show ?thesis using res by simp
  next
    case res1
    have "cfg_reaches g (Statement n) (FunctionResult p)"
      by (meson e_en1 res1 cfg_reaches_trans)
    then show ?thesis using res by simp
  qed
next
  case (While b c)
  obtain n1 en1 ex1 E1 K1 where
      res: "en = Statement n" "ex = Statement n1"
           "(Statement n, EA_AssumeNot b, Statement n1) \<in> E"
    using While.prems(1) by (auto split: prod.splits)
  have "(Statement n, EA_AssumeNot b, Statement n1) \<in> intra g"
    using res While.prems(2) by blast
  then have "cfg_reaches g en ex" unfolding res(1,2) by (rule cfg_reaches_intra)
  then show ?case ..
next
  case (Call dst q actuals)
  have en: "en = Statement n" and ex: "ex = Statement (Suc n)"
    and mem: "(Statement n,
                CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
                FunctionEntry q, Statement (Suc n)) \<in> calls g"
    using Call.prems by (auto split: prod.splits)
  from mem have "cfg_reaches g en ex" unfolding en ex by (rule cfg_reaches_comb_caller)
  then show ?case ..
next
  case (Return e)
  have en: "en = Statement n"
    and mem: "(Statement n, EA_Ret e p, FunctionResult p) \<in> intra g"
    using Return.prems by (auto split: prod.splits)
  from mem have "cfg_reaches g en (FunctionResult p)" unfolding en by (rule cfg_reaches_intra)
  then show ?case ..
next
  case Restore
  then have "en = ex" by (auto split: prod.splits)
  then show ?case by (simp add: cfg_reaches_refl)
next
  case Unwind
  then have "en = ex" by (auto split: prod.splits)
  then show ?case by (simp add: cfg_reaches_refl)
qed

lemma compile_proc_reaches_result:
  fixes g :: cfg
  assumes "compile_proc \<Pi> p decl n = (n', E, K)"
      and "E \<subseteq> intra g" "K \<subseteq> calls g"
  shows "cfg_reaches g (FunctionEntry p) (FunctionResult p)"
proof -
  obtain n0 ben bex Eb Kb where
      body: "compile \<Pi> p (body decl) n = (n0, ben, bex, Eb, Kb)"
    and E_eq: "E = insert (FunctionEntry p, EA_Nop, ben)
                     (insert (bex, EA_Ret None p, FunctionResult p) Eb)"
    and K_eq: "K = Kb"
    using assms(1) unfolding compile_proc_def by (auto split: prod.splits)
  have Ebg: "Eb \<subseteq> intra g" using E_eq assms(2) by auto
  have Kbg: "Kb \<subseteq> calls g" using K_eq assms(3) by simp
  have entry_ben: "cfg_reaches g (FunctionEntry p) ben"
    using E_eq assms(2) by (auto intro: cfg_reaches_intra)
  have bex_res: "cfg_reaches g bex (FunctionResult p)"
    using E_eq assms(2) by (auto intro: cfg_reaches_intra)
  consider (r) "cfg_reaches g ben bex" | (res) "cfg_reaches g ben (FunctionResult p)"
    using compile_reaches[OF body Ebg Kbg] by blast
  then show ?thesis
  proof cases
    case r show ?thesis by (meson entry_ben r bex_res cfg_reaches_trans)
  next
    case res show ?thesis by (meson entry_ben res cfg_reaches_trans)
  qed
qed

theorem compile_prog_entry_cfg_reaches_exit:
  "cfg_reaches (compile_prog \<Pi> ps mnm main)
     (cfg_entry (compile_prog \<Pi> ps mnm main)) (cfg_exit (compile_prog \<Pi> ps mnm main))"
proof -
  obtain n1 Eprocs Kprocs where
    procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    by (cases "compile_procs \<Pi> ps 0") auto
  obtain n2 Emain Kmain where
    cmain: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    by (cases "compile_proc \<Pi> mnm (proc_decl_of [] main) n1") auto
  let ?g = "compile_prog \<Pi> ps mnm main"
  have g_intra: "intra ?g = Eprocs \<union> Emain" and g_calls: "calls ?g = Kprocs \<union> Kmain"
    and g_entry: "cfg_entry ?g = FunctionEntry mnm"
    using procs cmain by (simp_all add: compile_prog_def Let_def)
  have Eg: "Emain \<subseteq> intra ?g" using g_intra by simp
  have Kg: "Kmain \<subseteq> calls ?g" using g_calls by simp
  have "cfg_reaches ?g (FunctionEntry mnm) (FunctionResult mnm)"
    by (rule compile_proc_reaches_result[OF cmain Eg Kg])
  then show ?thesis
    by (simp add: g_entry cfg_exit_compile_prog)
qed

end
