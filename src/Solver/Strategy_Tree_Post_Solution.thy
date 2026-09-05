theory Strategy_Tree_Post_Solution
  imports "TD.Basics_side"
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

definition tree_covered_at ::
  "('x,'g,'d::bounded_semilattice_sup_bot) strategy_tree \<Rightarrow> ('x + 'g \<Rightarrow> 'd) \<Rightarrow> 'x \<Rightarrow> bool"
where
  "tree_covered_at t \<sigma> u \<equiv>
     traverse_rhs t \<sigma> \<le> \<sigma> (Inl u) \<and> sides_of_rhs t \<sigma> \<le> \<sigma>"

text \<open>
  The two halves of \<^const>\<open>tree_covered_at\<close>, split out so a call site
  can cite the half it needs instead of re-unfolding the conjunction.
\<close>

lemma tree_covered_at_local [dest]:
  "tree_covered_at t \<sigma> u \<Longrightarrow> traverse_rhs t \<sigma> \<le> \<sigma> (Inl u)"
  unfolding tree_covered_at_def by simp

lemma tree_covered_at_sides [dest]:
  "tree_covered_at t \<sigma> u \<Longrightarrow> sides_of_rhs t \<sigma> \<le> \<sigma>"
  unfolding tree_covered_at_def by simp

lemma tree_covered_atI [intro]:
  "traverse_rhs t \<sigma> \<le> \<sigma> (Inl u) \<Longrightarrow> sides_of_rhs t \<sigma> \<le> \<sigma> \<Longrightarrow> tree_covered_at t \<sigma> u"
  unfolding tree_covered_at_def by simp

subsection \<open>Equivalent forms\<close>

lemma part_post_solution_iff_tree_covered_at:
  "part_post_solution T x \<sigma> vars \<longleftrightarrow>
     x \<in> vars \<and> (\<forall>u \<in> vars. dep\<^sub>L T \<sigma> u \<subseteq> vars \<and> tree_covered_at (T u) \<sigma> u)"
  unfolding tree_covered_at_def by auto

lemma part_post_solution_imp_tree_covered_at:
  assumes "part_post_solution T x \<sigma> vars" and "u \<in> vars"
  shows "tree_covered_at (T u) \<sigma> u"
  using assms part_post_solution_iff_tree_covered_at by blast

subsection \<open>Two systems the solution cannot tell apart\<close>

text \<open>
  \<^const>\<open>part_post_solution\<close> reads an equation system only through the three
  observations, so two systems agreeing on all three at every unknown are
  post-solved by exactly the same valuations. Any re-encoding that preserves
  answer, publications and dependencies --- buffering a right-hand side,
  reshaping its contributions --- transports its post-solutions through this
  one congruence, rather than through a second copy of whatever argument
  established the agreement.
\<close>

lemma part_post_solution_cong:
  assumes traverse: "\<And>u. traverse_rhs (T u) \<sigma> = traverse_rhs (T' u) \<sigma>"
    and deps: "\<And>u. dep_aux \<sigma> (T u) = dep_aux \<sigma> (T' u)"
    and sides: "\<And>u. sides_of_rhs (T u) \<sigma> = sides_of_rhs (T' u) \<sigma>"
  shows "part_post_solution T x \<sigma> vars \<longleftrightarrow> part_post_solution T' x \<sigma> vars"
  unfolding part_post_solution_iff_tree_covered_at tree_covered_at_def dep\<^sub>L_def dep_def
  by (simp add: traverse deps sides)

end
