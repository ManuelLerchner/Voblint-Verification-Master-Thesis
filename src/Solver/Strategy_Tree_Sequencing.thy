theory Strategy_Tree_Sequencing
  imports "TD.Basics_side" "HOL-Library.Monad_Syntax"
begin

section \<open>Sequencing strategy trees, and when their query set is environment-independent\<close>

text \<open>
  \<open>('x, 'g, 'd) strategy_tree\<close>, its constructors \<open>Answer\<close>/\<open>QueryL\<close>/\<open>QueryG\<close>/
  \<open>Side\<close>, and its interpreters \<open>traverse_rhs\<close> (the local answer),
  \<open>dep_aux\<close> (the unknowns queried) and \<open>sides_of_rhs\<close> (the global
  contributions published) are all vendored from \<open>TD.Basics_side\<close>, not
  defined in this codebase. This theory adds bind for the strategy-tree monad
  (\<open>seqcomp_tree\<close>: run \<open>t\<close>, pass its answer to continuation \<open>k\<close> -- the
  combinator every effectful fold over per-edge trees is built from), and two
  dependency invariants a tree's query set can satisfy: \<open>env_indep_deps\<close>
  (constant in the environment) and its strictly weaker cousin
  \<open>mono_tree_deps\<close> (monotone in the environment).
\<close>

subsection \<open>Sequential composition (bind)\<close>

primrec seqcomp_tree ::
  "('x, 'g, 'd) strategy_tree
   \<Rightarrow> ('d \<Rightarrow> ('x, 'g, 'd) strategy_tree)
   \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "seqcomp_tree (Answer v)   k = k v"
| "seqcomp_tree (QueryL u f) k = QueryL u  (\<lambda>d. seqcomp_tree (f d) k)"
| "seqcomp_tree (QueryG g f) k = QueryG g  (\<lambda>d. seqcomp_tree (f d) k)"
| "seqcomp_tree (Side g v t) k = Side g v  (seqcomp_tree t k)"

text \<open>
  \<^const>\<open>seqcomp_tree\<close> registered under \<^const>\<open>Monad_Syntax.bind\<close>'s ad hoc
  overloading, so \<open>t \<bind> k\<close> and \<open>do { x \<leftarrow> t; k x }\<close> both parse to exactly
  \<open>seqcomp_tree t k\<close> -- a pure syntax translation resolved at elaboration
  time, so every lemma below applies unchanged to code written with \<open>do\<close>
  notation.
\<close>

adhoc_overloading Monad_Syntax.bind == seqcomp_tree

lemma traverse_seqcomp[simp]:
  "traverse_rhs (t \<bind> k) \<sigma> = traverse_rhs (k (traverse_rhs t \<sigma>)) \<sigma>"
  by (induction t arbitrary: k) (auto intro: rangeI)

lemma dep_aux_seqcomp[simp]:
  "dep_aux \<sigma> (t \<bind> k) = dep_aux \<sigma> t \<union> dep_aux \<sigma> (k (traverse_rhs t \<sigma>))"
  by (induction t arbitrary: k) (auto intro: rangeI)

lemma sides_of_rhs_seqcomp[simp]:
  fixes t :: "('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree"
  shows "sides_of_rhs (t \<bind> k) \<sigma>
         = sides_of_rhs t \<sigma> \<squnion> sides_of_rhs (k (traverse_rhs t \<sigma>)) \<sigma>"
  by (induction t arbitrary: k) (auto simp: Let_def sup_fun_def fun_upd_def ac_simps)

text \<open>
  The monad laws: \<open>Answer\<close> is a right identity for \<open>seqcomp_tree\<close> (its left
  identity is already \<^const>\<open>seqcomp_tree\<close>'s own defining equation on
  \<open>Answer\<close>), and \<open>seqcomp_tree\<close> is associative. Left bare rather than
  \<open>[simp]\<close>: associativity has two competing rewrite directions, and which one
  a proof wants is not fixed in advance.
\<close>

lemma seqcomp_Answer_right [simp]: "t \<bind> Answer = t"
  by (induction t) simp_all

lemma seqcomp_assoc:
  fixes t :: "('x, 'g, 'd) strategy_tree"
  shows "t \<bind> k \<bind> h = t \<bind> (\<lambda>v. k v \<bind> h)"
  by (induction t arbitrary: k) simp_all

subsection \<open>Monotonicity of bind\<close>

text \<open>
  If \<open>t\<close> is monotone in the environment, every continuation \<open>k v\<close> is
  monotone in the environment, and \<open>k\<close> is monotone in the value it receives,
  then \<open>t \<bind> k\<close> is monotone in the environment.
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
  shows "traverse_rhs (t \<bind> k) \<sigma>1 \<le> traverse_rhs (t \<bind> k) \<sigma>2"
  using assms by (fastforce intro: order_trans)

subsection \<open>Environment-independent dependencies\<close>

text \<open>
  \<open>env_indep_deps t\<close>: the set of unknowns queried in \<open>t\<close> does not depend on
  the environment at all, for any two environments, related or not. It holds
  for trees whose \<open>QueryL\<close>/\<open>QueryG\<close> skeleton is fixed and only the
  \<open>Side\<close>/\<open>Answer\<close> values vary with the environment -- every tree this
  codebase currently builds.
\<close>

definition env_indep_deps :: "('x, 'g, 'd::order_bot) strategy_tree \<Rightarrow> bool" where
  "env_indep_deps t \<longleftrightarrow> (\<forall>\<sigma>1 \<sigma>2. dep_aux \<sigma>1 t = dep_aux \<sigma>2 t)"

lemma env_indep_depsI [intro]:
  "(\<And>\<sigma>1 \<sigma>2. dep_aux \<sigma>1 t = dep_aux \<sigma>2 t) \<Longrightarrow> env_indep_deps t"
  unfolding env_indep_deps_def by blast

lemma env_indep_deps_Answer [simp]: "env_indep_deps (Answer d)"
  unfolding env_indep_deps_def by simp

text \<open>
  bind preserves environment-independent dependencies when the continuation's
  dependency set is independent of both the value it receives and the
  environment.  The latter rules out value-dependent branching that changes
  which nodes are queried.
\<close>

lemma env_indep_deps_seqcomp[intro]:
  fixes t :: "('x, 'g, 'd::order_bot) strategy_tree"
  assumes t_indep: "env_indep_deps t"
  assumes k_indep: "\<And>v1 v2 \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (k v1) = dep_aux \<sigma>2 (k v2)"
  shows "env_indep_deps (t \<bind> k)"
proof (rule env_indep_depsI)
  fix \<sigma>1 \<sigma>2 :: "'x + 'g \<Rightarrow> 'd"
  have t_eq: "dep_aux \<sigma>1 t = dep_aux \<sigma>2 t"
    using t_indep unfolding env_indep_deps_def by blast
  have k_eq: "dep_aux \<sigma>1 (k (traverse_rhs t \<sigma>1)) = dep_aux \<sigma>2 (k (traverse_rhs t \<sigma>2))"
    by (rule k_indep)
  have "dep_aux \<sigma>1 (t \<bind> k)
        = dep_aux \<sigma>1 t \<union> dep_aux \<sigma>1 (k (traverse_rhs t \<sigma>1))"
    by (rule dep_aux_seqcomp)
  also have "\<dots> = dep_aux \<sigma>2 t \<union> dep_aux \<sigma>2 (k (traverse_rhs t \<sigma>2))"
    by (simp only: t_eq k_eq)
  also have "\<dots> = dep_aux \<sigma>2 (t \<bind> k)"
    by (rule dep_aux_seqcomp[symmetric])
  finally show "dep_aux \<sigma>1 (t \<bind> k) = dep_aux \<sigma>2 (t \<bind> k)" .
qed

subsection \<open>Monotone dependencies\<close>

text \<open>
  \<open>mono_tree_deps t\<close> is the per-tree form of the vendored solver's own
  \<open>mono_deps\<close> precondition: the query set may only grow, never shrink, as
  the environment grows. Every \<^const>\<open>env_indep_deps\<close> tree satisfies it for
  free (\<open>env_indep_deps_imp_mono_tree_deps\<close>); a future tree whose skeleton
  itself depends on the environment, and can therefore only be shown monotone
  rather than constant, has an interface to satisfy without reproving the
  stronger property. No construction in this codebase needs that yet.
\<close>

definition mono_tree_deps :: "('x, 'g, 'd::order_bot) strategy_tree \<Rightarrow> bool" where
  "mono_tree_deps t \<longleftrightarrow> (\<forall>\<sigma>1 \<sigma>2. \<sigma>1 \<le> \<sigma>2 \<longrightarrow> dep_aux \<sigma>1 t \<subseteq> dep_aux \<sigma>2 t)"

lemma mono_tree_depsI [intro]:
  "(\<And>\<sigma>1 \<sigma>2. \<sigma>1 \<le> \<sigma>2 \<Longrightarrow> dep_aux \<sigma>1 t \<subseteq> dep_aux \<sigma>2 t) \<Longrightarrow> mono_tree_deps t"
  unfolding mono_tree_deps_def by blast

lemma env_indep_deps_imp_mono_tree_deps [intro]:
  "env_indep_deps t \<Longrightarrow> mono_tree_deps t"
  unfolding env_indep_deps_def mono_tree_deps_def by blast
end

