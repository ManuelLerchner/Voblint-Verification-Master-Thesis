theory Strategy_Tree_Rhs
  imports Strategy_Tree_Monad
begin

section \<open>Folding a right-hand side from contribution trees\<close>

text \<open>
  An equation's right-hand side is assembled from a list of contribution trees.
  \<open>fold_rhs_trees\<close> sequences them with \<^const>\<open>seqcomp_tree\<close>, joining each
  answer into a running accumulator. The characterization lemmas below rewrite
  the fold's \<^const>\<open>traverse_rhs\<close>, \<^const>\<open>sides_of_rhs\<close> and \<^const>\<open>dep_aux\<close>
  values as ordinary folds over the elements' own values at a fixed environment,
  which is what lets a per-contribution fact transport to the whole list.

  \<open>fold_rhs_trees\<close> itself never emits a \<^const>\<open>Side\<close>: a fold of Side-free
  contributions is Side-free, so a generator that splits and publishes once
  after the fold emits exactly one \<^const>\<open>Side\<close> per right-hand-side evaluation.
\<close>

fun fold_rhs_trees ::
  "'a::bounded_semilattice_sup_bot
   \<Rightarrow> ('k, 'g, 'a) strategy_tree list
   \<Rightarrow> ('k, 'g, 'a) strategy_tree"
where
  "fold_rhs_trees acc [] = Answer acc"
| "fold_rhs_trees acc (t # ts) =
     seqcomp_tree t (\<lambda>res. fold_rhs_trees (acc \<squnion> res) ts)"

lemma sides_of_rhs_fold_rhs_trees_bot:
  fixes cs :: "('x,'g,'d::bounded_semilattice_sup_bot) strategy_tree list"
  assumes "\<And>c \<sigma>. c \<in> set cs \<Longrightarrow> sides_of_rhs c \<sigma> = \<bottom>"
  shows "sides_of_rhs (fold_rhs_trees acc cs) \<sigma> = \<bottom>"
  using assms
proof (induction cs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  then show ?case by simp
qed

lemma foldr_sup_seed_swap:
  fixes h :: "'t \<Rightarrow> 'd::semilattice_sup"
  shows "foldr (\<lambda>t acc'. h t \<squnion> acc') ts (a \<squnion> b) = a \<squnion> foldr (\<lambda>t acc'. h t \<squnion> acc') ts b"
  by (induction ts) (simp_all add: ac_simps)

lemma traverse_fold_rhs_trees_char:
  "traverse_rhs (fold_rhs_trees acc ts) \<sigma>
     = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') ts acc"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have "traverse_rhs (fold_rhs_trees acc (t # ts)) \<sigma>
          = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') ts (acc \<squnion> traverse_rhs t \<sigma>)"
    using Cons.IH by simp
  also have "\<dots> = traverse_rhs t \<sigma> \<squnion> foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') ts acc"
    by (simp add: sup_commute[of acc] foldr_sup_seed_swap)
  finally show ?case by simp
qed

lemma fold_rhs_trees_map_join_char:
  "traverse_rhs (fold_rhs_trees acc (map f xs)) \<sigma>
     = foldr (\<lambda>x acc'. traverse_rhs (f x) \<sigma> \<squnion> acc') xs acc"
proof (induction xs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (simp add: sup_commute[of acc] foldr_sup_seed_swap)
qed

lemma sides_of_rhs_fold_rhs_trees_char:
  fixes ts :: "('x,'g,'d::bounded_semilattice_sup_bot) strategy_tree list"
  shows "sides_of_rhs (fold_rhs_trees acc ts) \<sigma> z
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> z \<squnion> acc') ts \<bottom>"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  then show ?case by simp
qed

lemma dep_aux_fold_rhs_trees_char:
  "dep_aux \<sigma> (fold_rhs_trees acc ts) = (\<Union>t\<in>set ts. dep_aux \<sigma> t)"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  then show ?case by simp
qed

end
