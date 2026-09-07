theory CFG_Prune
  imports CFG_Transfer
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

text \<open>Reachability over that successor relation, with the transitivity and one-step
  introduction rules consumers actually cite.  Because the relation already relates a caller
  to its continuation and a callee result to the same continuation, this closure crosses
  procedure boundaries without any separate interprocedural notion.\<close>
definition cfg_succ :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node \<Rightarrow> bool" where
  "cfg_succ g u w \<longleftrightarrow> (u, w) \<in> cfg_succ_rel g"

definition cfg_reaches :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node \<Rightarrow> bool" where
  "cfg_reaches g v v0 \<longleftrightarrow> (v, v0) \<in> (cfg_succ_rel g)\<^sup>*"

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

end
