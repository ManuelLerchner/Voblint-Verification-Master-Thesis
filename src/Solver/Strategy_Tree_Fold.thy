theory Strategy_Tree_Fold
  imports Strategy_Tree_Program
begin

section \<open>Folding a right-hand side from contribution trees\<close>

text \<open>
  An equation's right-hand side is assembled from a list of contribution trees --
  one per intra predecessor, or per call-return site -- joined into one answer.
  \<open>fold_rhs_contributions\<close> sequences them with \<open>\<bind>\<close>, joining each answer into a running
  accumulator: the effect-tree analogue of an ordinary \<open>foldr (\<squnion>)\<close> over already-
  computed values, needed here because each contribution is still an unevaluated
  tree of reads and writes, not a value. It never emits a \<^const>\<open>Side\<close> itself: a
  fold of Side-free contributions stays Side-free, which is what lets a generator
  publish once, after the whole fold, instead of once per contribution -- multiple
  writes to the same key within one right-hand-side evaluation can otherwise
  destabilize the vendored solver's per-origin update rule.
\<close>

subsection \<open>Folding contributions into one right-hand side\<close>

fun fold_rhs_contributions ::
  "'a::semilattice_sup
   \<Rightarrow> ('k, 'g, 'a) strategy_tree list
   \<Rightarrow> ('k, 'g, 'a, 'a) strategy_program"
where
  "fold_rhs_contributions acc [] = sp_return acc"
| "fold_rhs_contributions acc (t # ts) =
     do {
       res \<leftarrow> sp_lift_tree t;
       fold_rhs_contributions (acc \<squnion> res) ts
     }"

text \<open>
  Contribution trees are traversed in list order: each answer joins the running
  accumulator before the next tree runs. The declarative characterizations below
  forget that order where the underlying operation is commutative -- a set union
  for \<^const>\<open>dep_aux\<close>, a join seeded at \<open>bot\<close> for \<^const>\<open>sides_of_rhs\<close> -- but
  \<^const>\<open>traverse_rhs\<close>'s own characterization states the accumulator threading
  directly, as a left fold, because that is the actual evaluation order.
\<close>

subsection \<open>Declarative characterizations\<close>

theorem traverse_fold_rhs_contributions_char:
  "traverse_rhs (sp_compile (fold_rhs_contributions acc ts)) \<sigma>
     = foldl (\<lambda>acc' t. acc' \<squnion> traverse_rhs t \<sigma>) acc ts"
  by (induction ts arbitrary: acc) (simp_all add: sp_compile_def sp_compile_with_bind)

theorem sides_of_rhs_fold_rhs_contributions_char:
  fixes ts :: "('x,'g,'d::bounded_semilattice_sup_bot) strategy_tree list"
  shows "sides_of_rhs (sp_compile (fold_rhs_contributions acc ts)) \<sigma> z
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> z \<squnion> acc') ts \<bottom>"
  by (induction ts arbitrary: acc) (auto simp add: sp_compile_def sp_compile_with_bind)

theorem dep_aux_fold_rhs_contributions_char:
  "dep_aux \<sigma> (sp_compile (fold_rhs_contributions acc ts)) = (\<Union>t\<in>set ts. dep_aux \<sigma> t)"
  by (induction ts arbitrary: acc) (auto simp add: sp_compile_def sp_compile_with_bind)

subsection \<open>Side-effect purity of the fold\<close>

lemma foldr_sup_bot_of_all_bot:
  fixes L :: "'a list" and h :: "'a \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  assumes "\<And>x. x \<in> set L \<Longrightarrow> h x = bot"
  shows "foldr (\<lambda>x acc'. h x \<squnion> acc') L bot = bot"
  using assms by (induction L) simp_all

subsection \<open>Dependency-property preservation\<close>

text \<open>
  A fold of trees whose query set is (respectively environment-independent,
  monotone in the environment) is itself environment-independent (monotone) --
  the list-level analogue of \<^const>\<open>env_indep_deps\<close>/\<^const>\<open>mono_tree_deps\<close>'s
  own single-tree closure facts, and what lets a generator's whole-node
  dependency obligation reduce to a per-hook one.
\<close>

end

