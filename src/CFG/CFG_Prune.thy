theory CFG_Prune
  imports VIMP_Proc_to_CFG
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
  its continuation or (via an early \<open>Return\<close>) the enclosing procedure's
  \<open>FunctionResult\<close>.  A call site reaches its continuation through the COMB_CALLER
  dependency, so no callee fragment is needed.\<close>
lemma compile_reaches:
  fixes g :: cfg
  shows "compile \<Pi> p c k n = (n', en, E, K)
     \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> K \<subseteq> calls g
     \<Longrightarrow> cfg_reaches g en k \<or> cfg_reaches g en (FunctionResult p)"
proof (induction c arbitrary: k n n' en E K)
  case SKIP
  then have en: "en = Statement n" and mem: "(Statement n, EA_Nop, k) \<in> intra g"
    by (auto split: prod.splits)
  from mem have "cfg_reaches g en k" unfolding en by (rule cfg_reaches_intra)
  then show ?case ..
next
  case (Assign x a)
  then have en: "en = Statement n" and mem: "(Statement n, EA_Assign x a, k) \<in> intra g"
    by (auto split: prod.splits)
  from mem have "cfg_reaches g en k" unfolding en by (rule cfg_reaches_intra)
  then show ?case ..
next
  case (Random x)
  then have en: "en = Statement n" and mem: "(Statement n, EA_Random x, k) \<in> intra g"
    by (auto split: prod.splits)
  from mem have "cfg_reaches g en k" unfolding en by (rule cfg_reaches_intra)
  then show ?case ..
next
  case (Check b)
  then have en: "en = Statement n" and mem: "(Statement n, EA_Check b, k) \<in> intra g"
    by (auto split: prod.splits)
  from mem have "cfg_reaches g en k" unfolding en by (rule cfg_reaches_intra)
  then show ?case ..
next
  case (Seq c1 c2)
  obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1': "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2': "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and res: "en = en1" "E = E1 \<union> E2" "K = K1 \<union> K2"
    using Seq.prems(1) by (auto simp: Let_def split: prod.splits)
  have E1g: "E1 \<subseteq> intra g" and E2g: "E2 \<subseteq> intra g" using res Seq.prems(2) by auto
  have K1g: "K1 \<subseteq> calls g" and K2g: "K2 \<subseteq> calls g" using res Seq.prems(3) by auto
  have en2: "en2 = Statement (n + csize c1)" using compile_entry[OF c2'] .
  consider (r1) "cfg_reaches g en1 (Statement (n + csize c1))"
    | (res1) "cfg_reaches g en1 (FunctionResult p)"
    using Seq.IH(1)[OF c1' E1g K1g] by blast
  then show ?case
  proof cases
    case res1 then show ?thesis using res by simp
  next
    case r1
    consider (r2) "cfg_reaches g en2 k" | (res2) "cfg_reaches g en2 (FunctionResult p)"
      using Seq.IH(2)[OF c2' E2g K2g] by blast
    then show ?thesis
    proof cases
      case r2
      have "cfg_reaches g en1 k" using r1 r2 en2 by (meson cfg_reaches_trans)
      then show ?thesis using res by simp
    next
      case res2
      have "cfg_reaches g en1 (FunctionResult p)" using r1 res2 en2
        by (meson cfg_reaches_trans)
      then show ?thesis using res by simp
    qed
  qed
next
  case (If b c1 c2)
  obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1': "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2': "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and res: "en = Statement n"
             "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                    \<union> E1 \<union> E2"
             "K = K1 \<union> K2"
    using If.prems(1) by (auto split: prod.splits)
  have E1g: "E1 \<subseteq> intra g" and K1g: "K1 \<subseteq> calls g" using res If.prems(2,3) by auto
  have e_en1: "cfg_reaches g (Statement n) en1"
    using res If.prems(2) by (auto intro: cfg_reaches_intra)
  consider (r1) "cfg_reaches g en1 k" | (res1) "cfg_reaches g en1 (FunctionResult p)"
    using If.IH(1)[OF c1' E1g K1g] by blast
  then show ?case
  proof cases
    case r1
    have "cfg_reaches g (Statement n) k" by (meson e_en1 r1 cfg_reaches_trans)
    then show ?thesis using res by simp
  next
    case res1
    have "cfg_reaches g (Statement n) (FunctionResult p)"
      by (meson e_en1 res1 cfg_reaches_trans)
    then show ?thesis using res by simp
  qed
next
  case (While b c)
  have res: "en = Statement n" "(Statement n, EA_AssumeNot b, k) \<in> E"
    using While.prems(1) by (auto split: prod.splits)  have "(Statement n, EA_AssumeNot b, k) \<in> intra g"
    using res While.prems(2) by blast
  then have "cfg_reaches g en k" unfolding res(1) by (rule cfg_reaches_intra)
  then show ?case ..
next
  case (Call dst q actuals)
  have en: "en = Statement n"
    and mem: "(Statement n,
                CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
                FunctionEntry q, k) \<in> calls g"
    using Call.prems by (auto split: prod.splits)
  from mem have "cfg_reaches g en k" unfolding en by (rule cfg_reaches_comb_caller)
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
  then have en: "en = Statement n" and mem: "(Statement n, EA_Nop, k) \<in> intra g"
    by (auto split: prod.splits)
  from mem have "cfg_reaches g en k" unfolding en by (rule cfg_reaches_intra)
  then show ?case ..
next
  case Unwind
  then have en: "en = Statement n" and mem: "(Statement n, EA_Nop, k) \<in> intra g"
    by (auto split: prod.splits)
  from mem have "cfg_reaches g en k" unfolding en by (rule cfg_reaches_intra)
  then show ?case ..
qed

text \<open>\<^const>\<open>falls_through\<close> decides which disjunct of \<open>compile_reaches\<close> holds.  A fragment that
  can complete normally reaches its continuation; one that cannot reaches the enclosing
  procedure's \<^term>\<open>FunctionResult\<close> along an explicit \<^const>\<open>Return\<close> edge.  The second direction
  is what lets \<open>compile_proc\<close> leave the epilogue node unallocated without losing
  \<open>compile_prog_entry_cfg_reaches_exit\<close>.\<close>
lemma compile_reaches_falls_through:
  fixes g :: cfg
  shows "compile \<Pi> p c k n = (n', en, E, K)
     \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> K \<subseteq> calls g
     \<Longrightarrow> falls_through c \<Longrightarrow> cfg_reaches g en k"
proof (induction c arbitrary: k n n' en E K)
  case SKIP
  then have en: "en = Statement n" and mem: "(Statement n, EA_Nop, k) \<in> intra g"
    by (auto split: prod.splits)
  from mem show ?case unfolding en by (rule cfg_reaches_intra)
next
  case (Assign x a)
  then have en: "en = Statement n" and mem: "(Statement n, EA_Assign x a, k) \<in> intra g"
    by (auto split: prod.splits)
  from mem show ?case unfolding en by (rule cfg_reaches_intra)
next
  case (Random x)
  then have en: "en = Statement n" and mem: "(Statement n, EA_Random x, k) \<in> intra g"
    by (auto split: prod.splits)
  from mem show ?case unfolding en by (rule cfg_reaches_intra)
next
  case (Check b)
  then have en: "en = Statement n" and mem: "(Statement n, EA_Check b, k) \<in> intra g"
    by (auto split: prod.splits)
  from mem show ?case unfolding en by (rule cfg_reaches_intra)
next
  case (Seq c1 c2)
  obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1': "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2': "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and res: "en = en1" "E = E1 \<union> E2" "K = K1 \<union> K2"
    using Seq.prems(1) by (auto simp: Let_def split: prod.splits)
  have E1g: "E1 \<subseteq> intra g" and E2g: "E2 \<subseteq> intra g" using res Seq.prems(2) by auto
  have K1g: "K1 \<subseteq> calls g" and K2g: "K2 \<subseteq> calls g" using res Seq.prems(3) by auto
  have en2: "en2 = Statement (n + csize c1)" using compile_entry[OF c2'] .
  have f1: "falls_through c1" and f2: "falls_through c2" using Seq.prems(4) by auto
  have r1: "cfg_reaches g en1 (Statement (n + csize c1))" using Seq.IH(1)[OF c1' E1g K1g f1] .
  have r2: "cfg_reaches g en2 k" using Seq.IH(2)[OF c2' E2g K2g f2] .
  show ?case using r1 r2 en2 res by (meson cfg_reaches_trans)
next
  case (If b c1 c2)
  obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1': "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2': "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and res: "en = Statement n"
             "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                    \<union> E1 \<union> E2"
             "K = K1 \<union> K2"
    using If.prems(1) by (auto split: prod.splits)
  have E1g: "E1 \<subseteq> intra g" and K1g: "K1 \<subseteq> calls g" using res If.prems(2,3) by auto
  have E2g: "E2 \<subseteq> intra g" and K2g: "K2 \<subseteq> calls g" using res If.prems(2,3) by auto
  have e_en1: "cfg_reaches g (Statement n) en1"
    using res If.prems(2) by (auto intro: cfg_reaches_intra)
  have e_en2: "cfg_reaches g (Statement n) en2"
    using res If.prems(2) by (auto intro: cfg_reaches_intra)
  from If.prems(4) consider (l) "falls_through c1" | (r) "falls_through c2" by auto
  then show ?case
  proof cases
    case l
    have "cfg_reaches g (Statement n) k"
      using e_en1 If.IH(1)[OF c1' E1g K1g l] by (meson cfg_reaches_trans)
    then show ?thesis using res by simp
  next
    case r
    have "cfg_reaches g (Statement n) k"
      using e_en2 If.IH(2)[OF c2' E2g K2g r] by (meson cfg_reaches_trans)
    then show ?thesis using res by simp
  qed
next
  case (While b c)
  have res: "en = Statement n" "(Statement n, EA_AssumeNot b, k) \<in> E"
    using While.prems(1) by (auto split: prod.splits)
  have "(Statement n, EA_AssumeNot b, k) \<in> intra g" using res While.prems(2) by blast
  then show ?case unfolding res(1) by (rule cfg_reaches_intra)
next
  case (Call dst q actuals)
  have en: "en = Statement n"
    and mem: "(Statement n,
                CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
                FunctionEntry q, k) \<in> calls g"
    using Call.prems by (auto split: prod.splits)
  from mem show ?case unfolding en by (rule cfg_reaches_comb_caller)
next
  case (Return e)
  then show ?case by simp
next
  case Restore
  then have en: "en = Statement n" and mem: "(Statement n, EA_Nop, k) \<in> intra g"
    by (auto split: prod.splits)
  from mem show ?case unfolding en by (rule cfg_reaches_intra)
next
  case Unwind
  then have en: "en = Statement n" and mem: "(Statement n, EA_Nop, k) \<in> intra g"
    by (auto split: prod.splits)
  from mem show ?case unfolding en by (rule cfg_reaches_intra)
qed

lemma compile_reaches_returns:
  fixes g :: cfg
  shows "compile \<Pi> p c k n = (n', en, E, K)
     \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> K \<subseteq> calls g
     \<Longrightarrow> \<not> falls_through c \<Longrightarrow> cfg_reaches g en (FunctionResult p)"
proof (induction c arbitrary: k n n' en E K)
  case SKIP then show ?case by simp
next
  case (Assign x a) then show ?case by simp
next
  case (Random x) then show ?case by simp
next
  case (Check b) then show ?case by simp
next
  case (Seq c1 c2)
  obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1': "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2': "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and res: "en = en1" "E = E1 \<union> E2" "K = K1 \<union> K2"
    using Seq.prems(1) by (auto simp: Let_def split: prod.splits)
  have E1g: "E1 \<subseteq> intra g" and E2g: "E2 \<subseteq> intra g" using res Seq.prems(2) by auto
  have K1g: "K1 \<subseteq> calls g" and K2g: "K2 \<subseteq> calls g" using res Seq.prems(3) by auto
  have en2: "en2 = Statement (n + csize c1)" using compile_entry[OF c2'] .
  show ?case
  proof (cases "falls_through c1")
    case False
    show ?thesis using Seq.IH(1)[OF c1' E1g K1g False] res by simp
  next
    case True
    have f2: "\<not> falls_through c2" using Seq.prems(4) True by simp
    have r1: "cfg_reaches g en1 (Statement (n + csize c1))"
      using compile_reaches_falls_through[OF c1' E1g K1g True] .
    have r2: "cfg_reaches g en2 (FunctionResult p)" using Seq.IH(2)[OF c2' E2g K2g f2] .
    show ?thesis using r1 r2 en2 res by (meson cfg_reaches_trans)
  qed
next
  case (If b c1 c2)
  obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1': "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2': "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and res: "en = Statement n"
             "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                    \<union> E1 \<union> E2"
             "K = K1 \<union> K2"
    using If.prems(1) by (auto split: prod.splits)
  have E1g: "E1 \<subseteq> intra g" and K1g: "K1 \<subseteq> calls g" using res If.prems(2,3) by auto
  have e_en1: "cfg_reaches g (Statement n) en1"
    using res If.prems(2) by (auto intro: cfg_reaches_intra)
  have f1: "\<not> falls_through c1" using If.prems(4) by simp
  have "cfg_reaches g (Statement n) (FunctionResult p)"
    using e_en1 If.IH(1)[OF c1' E1g K1g f1] by (meson cfg_reaches_trans)
  then show ?case using res by simp
next
  case (While b c) then show ?case by simp
next
  case (Call dst q actuals) then show ?case by simp
next
  case (Return e)
  have en: "en = Statement n"
    and mem: "(Statement n, EA_Ret e p, FunctionResult p) \<in> intra g"
    using Return.prems by (auto split: prod.splits)
  from mem show ?case unfolding en by (rule cfg_reaches_intra)
next
  case Restore then show ?case by simp
next
  case Unwind then show ?case by simp
qed

lemma compile_proc_reaches_result:
  fixes g :: cfg
  assumes "compile_proc \<Pi> p decl n = (n', E, K)"
      and "E \<subseteq> intra g" "K \<subseteq> calls g"
  shows "cfg_reaches g (FunctionEntry p) (FunctionResult p)"
proof -
  let ?r = "n + csize (body decl)"
  obtain Eb where
      body: "compile \<Pi> p (body decl) (Statement ?r) n = (?r, Statement n, Eb, K)"
    and E_eq: "E = insert (FunctionEntry p, EA_Nop, Statement n)
                     (if falls_through (body decl)
                      then insert (Statement ?r, EA_Ret None p, FunctionResult p) Eb
                      else Eb)"
    by (rule compile_procE[OF assms(1)])
  have Ebg: "Eb \<subseteq> intra g" using E_eq assms(2) by (auto split: if_splits)
  have entry_ben: "cfg_reaches g (FunctionEntry p) (Statement n)"
    using E_eq assms(2) by (auto intro: cfg_reaches_intra)
  show ?thesis
  proof (cases "falls_through (body decl)")
    case True
    have epi_res: "cfg_reaches g (Statement ?r) (FunctionResult p)"
      using E_eq assms(2) True by (auto intro: cfg_reaches_intra)
    have "cfg_reaches g (Statement n) (Statement ?r)"
      using compile_reaches_falls_through[OF body Ebg assms(3) True] .
    with entry_ben epi_res show ?thesis by (meson cfg_reaches_trans)
  next
    case False
    have "cfg_reaches g (Statement n) (FunctionResult p)"
      using compile_reaches_returns[OF body Ebg assms(3) False] .
    with entry_ben show ?thesis by (meson cfg_reaches_trans)
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
  obtain Cprocs n1' where cprocs: "collect_checks_procs \<Pi> ps 0 = (Cprocs, n1')"
    by (cases "collect_checks_procs \<Pi> ps 0") auto
  let ?g = "compile_prog \<Pi> ps mnm main"
  have g_intra: "intra ?g = Eprocs \<union> Emain" and g_calls: "calls ?g = Kprocs \<union> Kmain"
    and g_entry: "cfg_entry ?g = FunctionEntry mnm"
    using procs cmain cprocs by (simp_all add: compile_prog_def Let_def)
  have Eg: "Emain \<subseteq> intra ?g" using g_intra by simp
  have Kg: "Kmain \<subseteq> calls ?g" using g_calls by simp
  have "cfg_reaches ?g (FunctionEntry mnm) (FunctionResult mnm)"
    by (rule compile_proc_reaches_result[OF cmain Eg Kg])
  then show ?thesis
    by (simp add: g_entry cfg_exit_compile_prog)
qed

end
