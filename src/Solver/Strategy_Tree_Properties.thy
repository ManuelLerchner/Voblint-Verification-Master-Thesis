theory Strategy_Tree_Properties
  imports "TD.Basics_side"
begin

section \<open>When a tree's query set does not depend on the environment\<close>

text \<open>
  \<open>env_indep_deps\<close> and \<open>mono_tree_deps\<close> classify a \<open>strategy_tree\<close> by how
  its \<^const>\<open>dep_aux\<close> query set behaves as the environment varies -- a
  property of the tree \<^emph>\<open>value\<close> itself, independent of how that tree was
  built (by \<open>seqcomp_tree\<close>, by a typed \<open>strategy_program\<close>, or by hand).
\<close>

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
