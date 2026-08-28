theory CFG_Prune
  imports VIMP_Proc_to_CFG CFG_Transfer
begin

section \<open>Procedure-aware structural reachability and dependency cone\<close>

text \<open>
  \<open>cfg_succ_rel\<close> is the derived structural dependency graph the analysis pruning and
  cone proofs run on --- not the concrete execution relation.  It has four sources,
  induced by \<open>intra g\<close> and \<open>calls g\<close>:

  \<^item> INTRA: an ordinary edge \<open>(u, a, v) \<in> intra g\<close> gives \<open>u \<rightarrow> v\<close> (ordinary flow).
  \<^item> ENTRY: a call \<open>(c, ca, FunctionEntry p, k) \<in> calls g\<close> gives \<open>c \<rightarrow> FunctionEntry p\<close> ---
    the callee entry's abstract state depends on the caller state routed through
    the analysis's own enter operation.
  \<^item> COMB_CALLER: the same call gives \<open>c \<rightarrow> k\<close> --- the continuation depends on the saved
    caller state via \<^const>\<open>combine_collect\<close>.  This is not a concrete execution edge; execution
    does not skip the callee.
  \<^item> COMB_RESULT: the same call gives \<open>FunctionResult p \<rightarrow> k\<close> --- the continuation depends
    on the callee's result, \<^const>\<open>combine_collect\<close>'s callee-exit argument.

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

lemma cfg_succ_rel_cases:
  assumes "(y, z) \<in> cfg_succ_rel g"
  obtains (INTRA) a where "(y, a, z) \<in> intra g"
    | (ENTRY) ca k where "(y, ca, z, k) \<in> calls g"
    | (COMB_CALLER) ca ce where "(y, ca, ce, z) \<in> calls g"
    | (COMB_RESULT) c ca p k where "(c, ca, FunctionEntry p, k) \<in> calls g"
                                   "y = FunctionResult p" "z = k"
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

lemma cfg_reaches_intra:
  "(u, a, v) \<in> intra g \<Longrightarrow> cfg_reaches g u v"
  by (rule cfg_succ_imp_reaches) (simp add: cfg_succ_def cfg_succ_rel_intra)

lemma cfg_reaches_comb_caller:
  "(c, ca, ce, k) \<in> calls g \<Longrightarrow> cfg_reaches g c k"
  by (rule cfg_succ_imp_reaches) (simp add: cfg_succ_def cfg_succ_rel_comb_caller)

text \<open>The fragment-relative forms the compiler inductions use: an edge of a fragment
  included in the graph.\<close>
lemma cfg_reaches_intra_sub:
  "(u, a, v) \<in> E \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> cfg_reaches g u v"
  by (blast intro: cfg_reaches_intra)

lemma cfg_reaches_comb_caller_sub:
  "(c, ca, ce, k) \<in> K \<Longrightarrow> K \<subseteq> calls g \<Longrightarrow> cfg_reaches g c k"
  by (blast intro: cfg_reaches_comb_caller)

subsection \<open>Compiled entry reaches its exit or its procedure result\<close>

text \<open>\<^const>\<open>falls_through\<close> decides where a fragment's entry leads: a fragment that can
  complete normally reaches its continuation; one that cannot reaches the enclosing
  procedure's \<^term>\<open>FunctionResult\<close> along an explicit \<^const>\<open>Return\<close> edge.  The second
  direction is what lets \<open>compile_proc\<close> leave the epilogue node unallocated.\<close>
lemma compile_reaches_falls_through:
  assumes "compile \<Pi> p c k n = (n', en, E, K)" and "E \<subseteq> intra g" and "K \<subseteq> calls g"
    and "falls_through c"
  shows "cfg_reaches g en k"
  using assms
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and res: "en = Statement n" "E = E1 \<union> E2" "K = K1 \<union> K2"
    by (rule compile_SeqE)
  have "cfg_reaches g (Statement n) (Statement (n + csize c1))"
    using Seq.IH(1)[OF c1] Seq.prems res by auto
  moreover have "cfg_reaches g (Statement (n + csize c1)) k"
    using Seq.IH(2)[OF c2] Seq.prems res by auto
  ultimately show ?case unfolding res(1) by (rule cfg_reaches_trans)
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and c2: "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    and res: "en = Statement n"
      "E = {(Statement n, EA_Assume b, Statement (Suc n)),
            (Statement n, EA_AssumeNot b, Statement (Suc n + csize c1))} \<union> E1 \<union> E2"
      "K = K1 \<union> K2"
    by (rule compile_IfE)
  have b1: "cfg_reaches g (Statement n) (Statement (Suc n))"
    and b2: "cfg_reaches g (Statement n) (Statement (Suc n + csize c1))"
    using res(2) If.prems(2) by (blast intro: cfg_reaches_intra_sub)+
  from If.prems(4) consider "falls_through c1" | "falls_through c2" by auto
  then show ?case
  proof cases
    case 1
    have "cfg_reaches g (Statement (Suc n)) k" using If.IH(1)[OF c1] If.prems res 1 by auto
    with b1 show ?thesis unfolding res(1) by (rule cfg_reaches_trans)
  next
    case 2
    have "cfg_reaches g (Statement (Suc n + csize c1)) k"
      using If.IH(2)[OF c2] If.prems res 2 by auto
    with b2 show ?thesis unfolding res(1) by (rule cfg_reaches_trans)
  qed
qed (auto simp: Let_def split: prod.splits option.splits
     intro: cfg_reaches_intra_sub cfg_reaches_comb_caller_sub)

lemma compile_reaches_returns:
  assumes "compile \<Pi> p c k n = (n', en, E, K)" and "E \<subseteq> intra g" and "K \<subseteq> calls g"
    and "\<not> falls_through c"
  shows "cfg_reaches g en (FunctionResult p)"
  using assms
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and res: "en = Statement n" "E = E1 \<union> E2" "K = K1 \<union> K2"
    by (rule compile_SeqE)
  show ?case
  proof (cases "falls_through c1")
    case False
    then show ?thesis using Seq.IH(1)[OF c1] Seq.prems res by auto
  next
    case True
    have "cfg_reaches g (Statement n) (Statement (n + csize c1))"
      using compile_reaches_falls_through[OF c1] Seq.prems res True by auto
    moreover have "cfg_reaches g (Statement (n + csize c1)) (FunctionResult p)"
      using Seq.IH(2)[OF c2] Seq.prems res True by auto
    ultimately show ?thesis unfolding res(1) by (rule cfg_reaches_trans)
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 E1 K1 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and res: "en = Statement n"
      "E = {(Statement n, EA_Assume b, Statement (Suc n)),
            (Statement n, EA_AssumeNot b, Statement (Suc n + csize c1))} \<union> E1 \<union> E2"
      "K = K1 \<union> K2"
    by (rule compile_IfE)
  have "cfg_reaches g (Statement n) (Statement (Suc n))"
    using res(2) If.prems(2) by (blast intro: cfg_reaches_intra_sub)
  moreover have "cfg_reaches g (Statement (Suc n)) (FunctionResult p)"
    using If.IH(1)[OF c1] If.prems res by auto
  ultimately show ?case unfolding res(1) by (rule cfg_reaches_trans)
qed (auto simp: Let_def split: prod.splits option.splits intro: cfg_reaches_intra_sub)

lemma compile_proc_reaches_result:
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
  have entry: "cfg_reaches g (FunctionEntry p) (Statement n)"
    using E_eq assms(2) by (blast intro: cfg_reaches_intra_sub)
  show ?thesis
  proof (cases "falls_through (body decl)")
    case True
    have "cfg_reaches g (Statement ?r) (FunctionResult p)"
      using E_eq assms(2) True using cfg_reaches_intra_sub by auto
    with compile_reaches_falls_through[OF body Ebg assms(3) True] entry show ?thesis
      by (blast intro: cfg_reaches_trans)
  next
    case False
    from compile_reaches_returns[OF body Ebg assms(3) False] entry show ?thesis
      by (rule cfg_reaches_trans[rotated])
  qed
qed

theorem compile_prog_entry_cfg_reaches_exit:
  "cfg_reaches (compile_prog \<Pi> ps mnm main)
     (cfg_entry (compile_prog \<Pi> ps mnm main)) (cfg_exit (compile_prog \<Pi> ps mnm main))"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      cmain: "compile_proc \<Pi> mnm \<lparr>formals = [], body = main\<rparr> n1 = (n2, Emain, Kmain)"
    and g: "intra (compile_prog \<Pi> ps mnm main) = Eprocs \<union> Emain"
           "calls (compile_prog \<Pi> ps mnm main) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  have "cfg_reaches (compile_prog \<Pi> ps mnm main) (FunctionEntry mnm) (FunctionResult mnm)"
    using g by (intro compile_proc_reaches_result[OF cmain]) auto
  then show ?thesis by simp
qed

end
