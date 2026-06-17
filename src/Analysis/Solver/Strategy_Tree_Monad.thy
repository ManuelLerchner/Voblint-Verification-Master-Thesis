theory Strategy_Tree_Monad
  imports TD_Side_CFG
begin

section \<open>Strategy tree monad: sequential composition\<close>

text \<open>
  seqcomp_tree sequences two strategy trees: run t, pass its Answer value to
  continuation k.  Monadic bind for the strategy tree monad; the key combinator
  for building effectful IP folds from per-edge trees.
\<close>

primrec seqcomp_tree ::
  "('x, 'g, 'd) strategy_tree
   \<Rightarrow> ('d \<Rightarrow> ('x, 'g, 'd) strategy_tree)
   \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "seqcomp_tree (Answer v)   k = k v"
| "seqcomp_tree (QueryL u f) k = QueryL u  (\<lambda>d. seqcomp_tree (f d) k)"
| "seqcomp_tree (QueryG g f) k = QueryG g  (\<lambda>d. seqcomp_tree (f d) k)"
| "seqcomp_tree (Side g v t) k = Side g v  (seqcomp_tree t k)"

lemma traverse_seqcomp:
  "traverse_rhs (seqcomp_tree t k) \<sigma> = traverse_rhs (k (traverse_rhs t \<sigma>)) \<sigma>"
  by (induction t arbitrary: k) (auto intro: rangeI)

lemma dep_aux_seqcomp:
  "dep_aux \<sigma> (seqcomp_tree t k)
   = dep_aux \<sigma> t \<union> dep_aux \<sigma> (k (traverse_rhs t \<sigma>))"
  by (induction t arbitrary: k) (auto intro: rangeI)

text \<open>
  Monotonicity is preserved by bind: if t is monotone in the environment, every
  continuation k v is monotone in the environment, and k is monotone in the value
  it receives, then seqcomp_tree t k is monotone in the environment.
\<close>

lemma seqcomp_mono:
  fixes t :: "('x, 'g, 'd::order_bot) strategy_tree"
  assumes t_mono:
    "\<And>\<sigma>1 \<sigma>2. \<sigma>1 \<le> \<sigma>2 \<Longrightarrow> traverse_rhs t \<sigma>1 \<le> traverse_rhs t \<sigma>2"
  assumes k_mono_env:
    "\<And>v \<sigma>1 \<sigma>2. \<sigma>1 \<le> \<sigma>2 \<Longrightarrow> traverse_rhs (k v) \<sigma>1 \<le> traverse_rhs (k v) \<sigma>2"
  assumes k_mono_val:
    "\<And>\<sigma> v1 v2. v1 \<le> v2 \<Longrightarrow> traverse_rhs (k v1) \<sigma> \<le> traverse_rhs (k v2) \<sigma>"
  assumes le: "\<sigma>1 \<le> \<sigma>2"
  shows "traverse_rhs (seqcomp_tree t k) \<sigma>1 \<le> traverse_rhs (seqcomp_tree t k) \<sigma>2"
proof -
  have "traverse_rhs (seqcomp_tree t k) \<sigma>1 = traverse_rhs (k (traverse_rhs t \<sigma>1)) \<sigma>1"
    by (simp add: traverse_seqcomp)
  also have "\<dots> \<le> traverse_rhs (k (traverse_rhs t \<sigma>1)) \<sigma>2"
    by (rule k_mono_env[OF le])
  also have "\<dots> \<le> traverse_rhs (k (traverse_rhs t \<sigma>2)) \<sigma>2"
    by (rule k_mono_val[OF t_mono[OF le]])
  also have "\<dots> = traverse_rhs (seqcomp_tree t k) \<sigma>2"
    by (simp add: traverse_seqcomp)
  finally show ?thesis .
qed

subsection \<open>Static dependencies\<close>

text \<open>
  static_deps t: the set of unknowns queried in t does not depend on the
  environment.  The TD solver's mono_deps precondition needs this.  It holds
  for trees whose QueryL/QueryG skeleton is fixed and only the Side/Answer
  values vary with the environment (the safe invariant for effectful TF trees).
\<close>

definition static_deps :: "('x, 'g, 'd::order_bot) strategy_tree \<Rightarrow> bool" where
  "static_deps t \<longleftrightarrow> (\<forall>\<sigma>1 \<sigma>2. dep_aux \<sigma>1 t = dep_aux \<sigma>2 t)"

lemma static_depsI:
  "(\<And>\<sigma>1 \<sigma>2. dep_aux \<sigma>1 t = dep_aux \<sigma>2 t) \<Longrightarrow> static_deps t"
  unfolding static_deps_def by blast

lemma static_deps_Answer [simp]: "static_deps (Answer d)"
  unfolding static_deps_def by simp

text \<open>
  bind preserves static dependencies when the continuation's dependency set is
  independent of both the value it receives and the environment.  The latter
  rules out value-dependent branching that changes which nodes are queried.
\<close>

lemma static_deps_seqcomp:
  fixes t :: "('x, 'g, 'd::order_bot) strategy_tree"
  assumes t_static: "static_deps t"
  assumes k_static: "\<And>v1 v2 \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (k v1) = dep_aux \<sigma>2 (k v2)"
  shows "static_deps (seqcomp_tree t k)"
proof (rule static_depsI)
  fix \<sigma>1 \<sigma>2 :: "'x + 'g \<Rightarrow> 'd"
  have t_eq: "dep_aux \<sigma>1 t = dep_aux \<sigma>2 t"
    using t_static unfolding static_deps_def by blast
  have k_eq: "dep_aux \<sigma>1 (k (traverse_rhs t \<sigma>1)) = dep_aux \<sigma>2 (k (traverse_rhs t \<sigma>2))"
    by (rule k_static)
  have "dep_aux \<sigma>1 (seqcomp_tree t k)
        = dep_aux \<sigma>1 t \<union> dep_aux \<sigma>1 (k (traverse_rhs t \<sigma>1))"
    by (rule dep_aux_seqcomp)
  also have "\<dots> = dep_aux \<sigma>2 t \<union> dep_aux \<sigma>2 (k (traverse_rhs t \<sigma>2))"
    by (simp only: t_eq k_eq)
  also have "\<dots> = dep_aux \<sigma>2 (seqcomp_tree t k)"
    by (rule dep_aux_seqcomp[symmetric])
  finally show "dep_aux \<sigma>1 (seqcomp_tree t k) = dep_aux \<sigma>2 (seqcomp_tree t k)" .
qed

end
