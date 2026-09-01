theory Strategy_Tree_Fold
  imports Strategy_Tree_Sequencing
begin

section \<open>Folding a right-hand side from contribution trees\<close>

text \<open>
  An equation's right-hand side is assembled from a list of contribution trees --
  one per intra predecessor, or per call-return site -- joined into one answer.
  \<open>fold_rhs_trees\<close> sequences them with \<open>\<bind>\<close>, joining each answer into a running
  accumulator: the effect-tree analogue of an ordinary \<open>foldr (\<squnion>)\<close> over already-
  computed values, needed here because each contribution is still an unevaluated
  tree of reads and writes, not a value. It never emits a \<^const>\<open>Side\<close> itself: a
  fold of Side-free contributions stays Side-free, which is what lets a generator
  publish once, after the whole fold, instead of once per contribution -- multiple
  writes to the same key within one right-hand-side evaluation can otherwise
  destabilize the vendored solver's per-origin update rule.
\<close>

subsection \<open>Folding contributions into one right-hand side\<close>

fun fold_rhs_trees ::
  "'a::bounded_semilattice_sup_bot
   \<Rightarrow> ('k, 'g, 'a) strategy_tree list
   \<Rightarrow> ('k, 'g, 'a) strategy_tree"
where
  "fold_rhs_trees acc [] = Answer acc"
| "fold_rhs_trees acc (t # ts) = t \<bind> (\<lambda>res. fold_rhs_trees (acc \<squnion> res) ts)"

subsection \<open>List-algebra helpers\<close>

lemma foldr_sup_seed_swap:
  fixes h :: "'t \<Rightarrow> 'd::semilattice_sup"
  shows "foldr (\<lambda>t acc'. h t \<squnion> acc') ts (a \<squnion> b) = a \<squnion> foldr (\<lambda>t acc'. h t \<squnion> acc') ts b"
  by (induction ts) (simp_all add: ac_simps)

subsection \<open>Declarative characterizations\<close>

text \<open>
  The fold's \<^const>\<open>traverse_rhs\<close>, \<^const>\<open>sides_of_rhs\<close> and \<^const>\<open>dep_aux\<close>
  values are ordinary folds over the elements' own values at a fixed environment,
  which is what lets a per-contribution fact transport to the whole list.
\<close>

theorem traverse_fold_rhs_trees_char:
  "traverse_rhs (fold_rhs_trees acc ts) \<sigma> = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') ts acc"
  by (induction ts arbitrary: acc)
     (auto simp add: foldr_sup_seed_swap sup_commute[of _ "traverse_rhs _ \<sigma>"])

theorem sides_of_rhs_fold_rhs_trees_char:
  fixes ts :: "('x,'g,'d::bounded_semilattice_sup_bot) strategy_tree list"
  shows "sides_of_rhs (fold_rhs_trees acc ts) \<sigma> z
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> z \<squnion> acc') ts \<bottom>"
  by (induction ts arbitrary: acc) auto

theorem dep_aux_fold_rhs_trees_char:
  "dep_aux \<sigma> (fold_rhs_trees acc ts) = (\<Union>t\<in>set ts. dep_aux \<sigma> t)"
  by (induction ts arbitrary: acc) auto

subsection \<open>Side-effect purity of the fold\<close>

lemma sides_of_rhs_fold_rhs_trees_bot:
  fixes cs :: "('x,'g,'d::bounded_semilattice_sup_bot) strategy_tree list"
  assumes "\<And>c \<sigma>. c \<in> set cs \<Longrightarrow> sides_of_rhs c \<sigma> = \<bottom>"
  shows "sides_of_rhs (fold_rhs_trees acc cs) \<sigma> = \<bottom>"
  using assms by (induction cs arbitrary: acc) auto

end

