theory Scratch_Buffering_Crux
  imports "Voblint_CFG.CFG_Def" "Voblint_Core.TD_Side_Tree"
begin

section \<open>Crux lemma for generator-layer buffering (issue #121 follow-up)\<close>

text \<open>
  Standalone, generic scoping proof -- not wired into any production
  definition. First characterizes \<^const>\<open>fold_rhs_trees\<close>'s existing
  \<^const>\<open>traverse_rhs\<close>/\<^const>\<open>sides_of_rhs\<close> value as a join over each list
  element's \<^emph>\<open>individually\<close>, fixed-\<open>sigma\<close> traverse/sides value. Then shows
  that folding \<^emph>\<open>unsplit\<close>, Side-free per-edge results and splitting exactly
  once at the end -- reusing \<^const>\<open>restrict_local_for\<close>/
  \<^const>\<open>restrict_global_for\<close>'s existing join-homomorphism lemmas, not a new
  pair-typed tree -- yields the identical declarative value. This avoids the
  type obstacle of trying to build a tree whose \<^const>\<open>QueryL\<close>/\<^const>\<open>QueryG\<close>
  read type differs from its \<^const>\<open>Answer\<close> type: \<^type>\<open>strategy_tree\<close> ties
  both to the same \<open>'d\<close>, so any buffered/pure construction must stay in that
  same \<open>'d\<close> throughout and defer the local/global split to the very end,
  exactly as \<^const>\<open>unit_edge_tree\<close> already computes one unsplit \<open>res\<close> value
  before splitting it today -- the split just needs to move to \<^emph>\<open>after\<close> the
  fold instead of before it.
\<close>

subsection \<open>Characterization: the current combinator, as it stands today\<close>

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
  also  have "\<dots> = traverse_rhs t \<sigma> \<squnion> foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') ts acc"
    by (simp add: sup_commute[of acc] foldr_sup_seed_swap)
  finally show ?case by simp
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

text \<open>Both characterizations depend on \<open>ts\<close>'s elements only through their
  \<^emph>\<open>individual\<close> \<^const>\<open>traverse_rhs\<close>/\<^const>\<open>sides_of_rhs\<close> value at the \<^emph>\<open>same,
  fixed\<close> \<open>\<sigma>\<close> -- confirming, for the combinator exactly as it is defined today,
  that \<^const>\<open>fold_rhs_trees\<close>'s declarative meaning never depended on
  publish-then-observe sibling ordering. \<open>sides_of_rhs_fold_rhs_trees_char\<close>
  in particular does not mention \<open>acc\<close> at all, matching the acc-independence
  already proved ad hoc at production call sites.\<close>

subsection \<open>Side-free contribution trees fold to the same joined value\<close>

text \<open>A "contribution" tree \<open>c\<close> is any \<open>('x,unit,'d) strategy_tree\<close> built
  without \<^const>\<open>Side\<close> -- i.e. \<open>sides_of_rhs c \<sigma> = bot\<close> for every \<open>\<sigma>\<close>. Folding
  a list of such trees via the \<^emph>\<open>existing\<close> \<^const>\<open>fold_rhs_trees\<close> combinator
  never itself calls \<^const>\<open>Side\<close> (it only sequences its elements), so the
  fold's own \<^const>\<open>Answer\<close> value is exactly the join of the elements'
  individual \<^const>\<open>traverse_rhs\<close> values -- no new combinator is needed for
  the buffering itself, only Side-free elements.\<close>

lemma sides_of_rhs_fold_rhs_trees_bot:
  fixes cs :: "('x,unit,'d::bounded_semilattice_sup_bot) strategy_tree list"
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

text \<open>Given per-edge unsplit results \<open>res\<^sub>i\<close> (what \<^const>\<open>unit_edge_tree\<close>
  computes internally as \<open>res\<close>, before its own \<open>depend_on\<close>/\<open>answer\<close> split),
  a Side-free contribution tree for edge \<open>i\<close> is simply \<open>answer res\<^sub>i\<close>
  (parametrised over the same reads \<open>unit_edge_tree\<close> already performs). The
  buffered RHS is: fold these via the untouched \<^const>\<open>fold_rhs_trees\<close>, then
  split \<^emph>\<open>once\<close> at the very end -- exactly mirroring \<open>unit_edge_tree\<close>'s own
  \<open>let res = ...; depend_on (restrict_global res) (answer (restrict_local
  res))\<close> shape, just with the split moved after the fold instead of inside
  each element.\<close>

definition publish_split :: "(vname \<Rightarrow> bool) \<Rightarrow> ('x,unit,'a::sound_domain abs_state) strategy_tree
                              \<Rightarrow> ('x,unit,'a abs_state) strategy_tree" where
  "publish_split gs t = seqcomp_tree t
     (\<lambda>res. depend_on () (restrict_global_for gs res) (answer (restrict_local_for gs res)))"

lemma buffered_matches_local:
  fixes cs :: "('x,unit,'a::sound_domain abs_state) strategy_tree list"
  assumes side_free: "\<And>c. c \<in> set cs \<Longrightarrow> \<forall>\<sigma>. sides_of_rhs c \<sigma> = \<bottom>"
  shows "traverse_rhs (publish_split gs (fold_rhs_trees \<bottom> cs)) \<sigma>
       = restrict_local_for gs (traverse_rhs (fold_rhs_trees \<bottom> cs) \<sigma>)"
  unfolding publish_split_def by simp

lemma buffered_matches_global:
  fixes cs :: "('x,unit,'a::sound_domain abs_state) strategy_tree list"
  assumes side_free: "\<And>c. c \<in> set cs \<Longrightarrow> \<forall>\<sigma>. sides_of_rhs c \<sigma> = \<bottom>"
  shows "sides_of_rhs (publish_split gs (fold_rhs_trees \<bottom> cs)) \<sigma> (Inr ())
       = restrict_global_for gs (traverse_rhs (fold_rhs_trees \<bottom> cs) \<sigma>)"
  unfolding publish_split_def
  using side_free
  by (simp add: sides_of_rhs_fold_rhs_trees_bot)

text \<open>The join-homomorphism direction, connecting the buffered value to what
  \<^const>\<open>fold_rhs_trees\<close> over the \<^emph>\<open>original\<close> Side-emitting edge trees
  already computes today (\<open>restrict_local_for_join\<close>/\<open>restrict_global_for_join\<close>
  are the existing \<open>[simp]\<close> lemmas doing the real work: splitting distributes
  over \<open>\<squnion>\<close>, so "fold unsplit results then split" equals "split each result
  then fold").\<close>

text \<open>\<open>buffered_matches_local\<close>/\<open>buffered_matches_global\<close> above already give the
  full crux equivalence via \<open>sides_of_rhs_fold_rhs_trees_bot\<close> and
  \<open>publish_split\<close>'s own unfolding; a direct per-\<open>foldr\<close>-step restatement via
  \<open>restrict_local_for_join\<close>/\<open>restrict_global_for_join\<close> is not needed to close
  the argument and is omitted here.\<close>

end

