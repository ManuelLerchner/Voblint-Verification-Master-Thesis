theory Strategy_Tree_Post_Solution
  imports Strategy_Tree_Fold
begin

section \<open>What one unknown owes a post-solution\<close>

text \<open>
  A valuation covers a strategy tree when it bounds both the tree's local answer
  and every side contribution produced during the same traversal.  The local
  unknown bounds @{const traverse_rhs}; the complete valuation bounds
  @{const sides_of_rhs} pointwise.  \<^const>\<open>part_post_solution\<close> is exactly this
  obligation at every covered unknown together with dependency closure, so a
  projection or seeding argument only ever re-derives the per-unknown half.
\<close>

subsection \<open>The covering obligation\<close>

definition se_constraint_holds ::
  "('x,'g,'d::bounded_semilattice_sup_bot) strategy_tree \<Rightarrow> ('x + 'g \<Rightarrow> 'd) \<Rightarrow> 'x \<Rightarrow> bool"
where
  "se_constraint_holds t \<sigma> u \<equiv>
     traverse_rhs t \<sigma> \<le> \<sigma> (Inl u) \<and> sides_of_rhs t \<sigma> \<le> \<sigma>"

text \<open>
  The two halves of \<^const>\<open>se_constraint_holds\<close>, split out so a call site
  can cite the half it needs instead of re-unfolding the conjunction.
\<close>

lemma se_constraint_holds_local [dest]:
  "se_constraint_holds t \<sigma> u \<Longrightarrow> traverse_rhs t \<sigma> \<le> \<sigma> (Inl u)"
  unfolding se_constraint_holds_def by simp

lemma se_constraint_holds_sides [dest]:
  "se_constraint_holds t \<sigma> u \<Longrightarrow> sides_of_rhs t \<sigma> \<le> \<sigma>"
  unfolding se_constraint_holds_def by simp

subsection \<open>Equivalent forms\<close>

lemma part_post_solution_imp_se_constraint_holds:
  assumes "part_post_solution T x \<sigma> vars" and "u \<in> vars"
  shows "se_constraint_holds (T u) \<sigma> u"
  using assms unfolding se_constraint_holds_def by auto

lemma part_post_solution_iff_se_constraint_holds:
  "part_post_solution T x \<sigma> vars \<longleftrightarrow>
     x \<in> vars \<and> (\<forall>u \<in> vars. dep\<^sub>L T \<sigma> u \<subseteq> vars \<and> se_constraint_holds (T u) \<sigma> u)"
  unfolding se_constraint_holds_def by auto

end
