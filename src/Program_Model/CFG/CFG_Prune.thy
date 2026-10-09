theory CFG_Prune
  imports CFG_Transfer
begin

section \<open>Procedure-aware structural reachability\<close>

text \<open>
  \<open>cfg_succ_rel\<close> is the derived structural dependency graph the analysis pruning and
  cone proofs run on --- not the concrete execution relation.  It has four sources,
  induced by \<open>intra g\<close> and \<open>calls g\<close>:

  \<^item> INTRA: an ordinary edge \<open>(u, a, v) \<in> intra g\<close> gives \<open>u \<rightarrow> v\<close> (ordinary flow).
  \<^item> ENTRY: a call \<open>(c, ca, FunctionEntry p, k) \<in> calls g\<close> gives \<open>c \<rightarrow> FunctionEntry p\<close> ---
    the callee entry's abstract state depends on the caller state routed through
    the analysis's own enter operation.
  \<^item> \<open>COMB_CALLER\<close>: the same call gives \<open>c \<rightarrow> k\<close> --- the continuation depends on the saved
    caller state via \<^const>\<open>combine_collect\<close>.  This is not a concrete execution edge; execution
    does not skip the callee.
  \<^item> \<open>COMB_RESULT\<close>: the same call gives \<open>FunctionResult p \<rightarrow> k\<close> --- the continuation depends
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

text \<open>Reachability over that successor relation.  Because the relation already relates a
  caller to its continuation and a callee result to the same continuation, this closure
  crosses procedure boundaries without any separate interprocedural notion.\<close>
definition cfg_reaches :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node \<Rightarrow> bool" where
  "cfg_reaches g v v0 \<longleftrightarrow> (v, v0) \<in> (cfg_succ_rel g)\<^sup>*"

subsection \<open>Reachability inside one activation\<close>

text \<open>The same closure without entering callees: a call site steps straight to its
  continuation.  These are the steps a routed equation reads backwards, so this is the
  reachability the solver's coverage argument needs.\<close>

definition local_succ_rel :: "cfg \<Rightarrow> (cfg_node \<times> cfg_node) set" where
  "local_succ_rel g =
     {(u, v). \<exists>a. (u, a, v) \<in> intra g}
     \<union> {(u, k). \<exists>ca q. (u, ca, FunctionEntry q, k) \<in> calls g}"

definition local_reaches :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node \<Rightarrow> bool" where
  "local_reaches g u v \<longleftrightarrow> (u, v) \<in> (local_succ_rel g)\<^sup>*"

lemma local_reaches_refl [simp]: "local_reaches g v v"
  by (simp add: local_reaches_def)

lemma local_reaches_trans:
  "local_reaches g u v \<Longrightarrow> local_reaches g v w \<Longrightarrow> local_reaches g u w"
  unfolding local_reaches_def by (rule rtrancl_trans)

lemma local_reaches_intra_step:
  "(u, a, v) \<in> intra g \<Longrightarrow> local_reaches g v w \<Longrightarrow> local_reaches g u w"
  unfolding local_reaches_def local_succ_rel_def
  by (rule converse_rtrancl_into_rtrancl) blast+

lemma local_reaches_comb_step:
  "(u, ca, FunctionEntry q, k) \<in> calls g \<Longrightarrow> local_reaches g k w \<Longrightarrow> local_reaches g u w"
  unfolding local_reaches_def local_succ_rel_def
  by (rule converse_rtrancl_into_rtrancl) blast+

lemma local_reaches_cfg_reaches:
  "local_reaches g u v \<Longrightarrow> cfg_reaches g u v"
  unfolding local_reaches_def cfg_reaches_def
proof (induction rule: rtrancl_induct)
  case (step y z)
  then have "(y, z) \<in> cfg_succ_rel g"
    unfolding local_succ_rel_def by (auto simp: cfg_succ_rel_intra cfg_succ_rel_comb_caller)
  with step.IH show ?case by (rule rtrancl_into_rtrancl)
qed simp

end
