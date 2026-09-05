theory Strategy_Tree_Fold
  imports Strategy_Tree_Program
begin

section \<open>Folding a right-hand side from contribution trees\<close>

text \<open>
  An equation's right-hand side is assembled from a list of contribution trees ---
  one per incoming contribution, such as an intra predecessor, a call return, or
  a routed activation hook --- joined into one answer. The fold sequences them
  with \<open>\<bind>\<close>, joining each answer into a running accumulator: the effect-tree
  analogue of an ordinary \<open>foldr (\<squnion>)\<close> over already-computed values, needed here
  because each contribution is still an unevaluated tree of reads and writes, not
  a value. It never emits a \<^const>\<open>Side\<close> itself: a fold of Side-free
  contributions stays Side-free, which is what lets a generator publish once,
  after the whole fold, instead of once per contribution --- several updates to
  one key during a single right-hand-side evaluation otherwise change what the
  vendored solver's per-origin update rule widens against.

  What a caller varies is \<^emph>\<open>how much of each answer accumulates\<close>. The fold
  therefore takes a projection \<open>prj\<close> into the accumulator and an embedding
  \<open>emb\<close> back out. At the identity pair the whole answer accumulates. A D/G
  instance instead projects the local half into the accumulator and embeds the
  result as \<open>DG d bot\<close>; the global half of a contribution simply does not reach
  the node's answer, and a contribution tree that has one to share must publish
  it itself through \<^const>\<open>Side\<close>. Nothing here makes that happen.

  The two parameters are used as a projection and a final embedding, but the
  fold assumes no inverse or homomorphism law relating them. Order preservation
  is required only where it is actually used, by the environment-monotonicity
  results; the publication and dependency characterizations hold for arbitrary
  \<open>prj\<close> and \<open>emb\<close>.
\<close>

subsection \<open>Join-folds over a list\<close>

text \<open>
  Every characterization below states the fold as an ordinary
  \<open>foldr (\<squnion>)\<close> over already-computed values, so its consumers keep needing
  the same handful of facts about that: the seed can be moved out, a bound
  against the fold is a bound against every element, one element is below the
  fold, only the element set matters, a pointwise bound lifts, two lists that
  agree elementwise agree, and an all-\<^const>\<open>bot\<close> fold is \<^const>\<open>bot\<close>.

  They are collected here, ahead of the fold they serve, rather than restated
  per generator. \<open>foldr_sup_seed_swap\<close> is the one with content --- it needs
  only \<open>semilattice_sup\<close> --- and the two seed orientations below it are
  readings of that single equation, kept under their own names because proofs
  phrase their goals both ways.
\<close>

lemma foldr_sup_seed_swap:
  fixes h :: "'a \<Rightarrow> 'b::semilattice_sup"
  shows "foldr (\<lambda>t acc'. h t \<squnion> acc') ts (acc \<squnion> x) = x \<squnion> foldr (\<lambda>t acc'. h t \<squnion> acc') ts acc"
  by (induction ts arbitrary: acc) (simp_all add: sup_assoc sup_commute sup_left_commute)

lemma foldr_join_seed_out:
  fixes h :: "'a \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  shows "foldr (\<lambda>t acc'. h t \<squnion> acc') ts a = a \<squnion> foldr (\<lambda>t acc'. h t \<squnion> acc') ts bot"
  using foldr_sup_seed_swap[of h ts bot a] by simp

lemma foldr_sup_acc:
  fixes h :: "'a \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  shows "foldr (\<lambda>t acc'. h t \<squnion> acc') xs bot \<squnion> b = foldr (\<lambda>t acc'. h t \<squnion> acc') xs b"
  by (simp only: foldr_join_seed_out[of h xs b]) (rule sup_commute)

lemma foldr_sup_le_iff [simp]:
  fixes h :: "'a \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  shows "foldr (\<lambda>t acc'. h t \<squnion> acc') xs bot \<le> y \<longleftrightarrow> (\<forall>x \<in> set xs. h x \<le> y)"
  by (induction xs) auto

lemma foldr_sup_member_le [intro]:
  fixes h :: "'a \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  assumes "x \<in> set xs"
  shows "h x \<le> foldr (\<lambda>t acc'. h t \<squnion> acc') xs bot"
  using assms by (induction xs) (auto intro: le_supI2)

lemma foldr_sup_mono:
  fixes f g :: "'a \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> g x"
  shows "foldr (\<lambda>t a. f t \<squnion> a) xs bot \<le> foldr (\<lambda>t a. g t \<squnion> a) xs bot"
  using assms by (auto intro: order_trans[OF _ foldr_sup_member_le])

lemma foldr_sup_set_cong:
  fixes h :: "'a \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  assumes eq: "set xs = set ys"
  shows "foldr (\<lambda>t acc'. h t \<squnion> acc') xs b = foldr (\<lambda>t acc'. h t \<squnion> acc') ys b"
proof -
  have "foldr (\<lambda>t acc'. h t \<squnion> acc') xs bot = foldr (\<lambda>t acc'. h t \<squnion> acc') ys bot"
  proof (rule order_antisym)
    show "foldr (\<lambda>t acc'. h t \<squnion> acc') xs bot \<le> foldr (\<lambda>t acc'. h t \<squnion> acc') ys bot"
      by (auto simp: eq)
  next
    show "foldr (\<lambda>t acc'. h t \<squnion> acc') ys bot \<le> foldr (\<lambda>t acc'. h t \<squnion> acc') xs bot"
      by (auto simp: eq[symmetric])
  qed
  then show ?thesis
    using foldr_sup_acc[of h xs b] foldr_sup_acc[of h ys b] by simp
qed

text \<open>Two lists whose elements agree under their respective observations have
  the same join-fold. This is what lets a correspondence proof relate two
  generators' contribution lists elementwise instead of reasoning about the
  folds themselves.\<close>

lemma foldr_sup_list_all2_cong:
  fixes f :: "'a \<Rightarrow> 'c::bounded_semilattice_sup_bot"
  assumes "list_all2 (\<lambda>x y. f x = g y) xs ys"
  shows "foldr (\<lambda>x a. f x \<squnion> a) xs seed = foldr (\<lambda>y a. g y \<squnion> a) ys seed"
  using assms by (induction rule: list_all2_induct) simp_all

text \<open>The two ways such a correspondence is built and consumed: establishing
  it between two maps over one list, and reading it as an equality of unions.
  Neither mentions a fold, a tree, or a graph.\<close>

lemma list_all2_map_diag:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P (f x) (g x)) \<Longrightarrow> list_all2 P (map f xs) (map g xs)"
  by (induction xs) simp_all

lemma list_all2_Union_eq:
  assumes "list_all2 (\<lambda>a b. f a = g b) xs ys"
  shows "(\<Union>x\<in>set xs. f x) = (\<Union>y\<in>set ys. g y)"
  using assms by (induction rule: list_all2_induct) auto

lemma foldr_sup_bot_of_all_bot:
  fixes L :: "'a list" and h :: "'a \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  assumes "\<And>x. x \<in> set L \<Longrightarrow> h x = bot"
  shows "foldr (\<lambda>x acc'. h x \<squnion> acc') L bot = bot"
  using assms by (induction L) simp_all
subsection \<open>Folding contributions into one right-hand side\<close>

fun fold_rhs_projected ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b::semilattice_sup
   \<Rightarrow> ('k, 'g, 'a) strategy_tree list
   \<Rightarrow> ('k, 'g, 'a, 'a) strategy_program"
where
  "fold_rhs_projected prj emb acc [] = sp_return (emb acc)"
| "fold_rhs_projected prj emb acc (t # ts) =
     do {
       res \<leftarrow> sp_lift_tree t;
       fold_rhs_projected prj emb (acc \<squnion> prj res) ts
     }"

text \<open>The accumulator read declaratively off a valuation, rather than run.
  Every answer characterization below is stated through it.\<close>

fun fold_acc_projected ::
  "('a::bounded_semilattice_sup_bot \<Rightarrow> 'b::semilattice_sup) \<Rightarrow> 'b
   \<Rightarrow> ('k + 'g \<Rightarrow> 'a) \<Rightarrow> ('k, 'g, 'a) strategy_tree list \<Rightarrow> 'b"
where
  "fold_acc_projected prj acc \<sigma> [] = acc"
| "fold_acc_projected prj acc \<sigma> (t # ts) =
     fold_acc_projected prj (acc \<squnion> prj (traverse_rhs t \<sigma>)) \<sigma> ts"

subsection \<open>Declarative characterizations\<close>

text \<open>
  Contribution trees are traversed in list order: each answer joins the running
  accumulator before the next tree runs. The publication and dependency
  characterizations forget that order, the underlying operation being
  commutative --- a set union for \<^const>\<open>dep_aux\<close>, a join seeded at \<open>bot\<close> for
  \<^const>\<open>sides_of_rhs\<close> --- and neither sees \<open>prj\<close> or \<open>emb\<close> at all: what a fold
  publishes and reads is its contributions' business, not its accumulator's.
  That is also why both are independent of the accumulator it starts from.
\<close>

theorem traverse_fold_rhs_projected_char:
  "traverse_rhs (sp_compile (fold_rhs_projected prj emb acc ts)) \<sigma>
     = emb (fold_acc_projected prj acc \<sigma> ts)"
  by (induction ts arbitrary: acc)
     (simp_all add: sp_compile_def sp_compile_with_bind)

theorem sides_of_rhs_fold_rhs_projected_char:
  fixes ts :: "('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree list"
  shows "sides_of_rhs (sp_compile (fold_rhs_projected prj emb acc ts)) \<sigma> z
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> z \<squnion> acc') ts \<bottom>"
  by (induction ts arbitrary: acc) (auto simp add: sp_compile_def sp_compile_with_bind)

theorem dep_aux_fold_rhs_projected_char:
  "dep_aux \<sigma> (sp_compile (fold_rhs_projected prj emb acc ts)) = (\<Union>t\<in>set ts. dep_aux \<sigma> t)"
  by (induction ts arbitrary: acc) (auto simp add: sp_compile_def sp_compile_with_bind)

lemma fold_acc_projected_as_foldr:
  fixes prj :: "'a::bounded_semilattice_sup_bot \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  shows "fold_acc_projected prj acc \<sigma> ts
           = acc \<squnion> foldr (\<lambda>t a. prj (traverse_rhs t \<sigma>) \<squnion> a) ts bot"
  by (induction ts arbitrary: acc) (simp_all add: sup_assoc)

lemma fold_acc_projected_acc_mono:
  fixes prj :: "'a::bounded_semilattice_sup_bot \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  assumes "acc1 \<le> acc2"
  shows "fold_acc_projected prj acc1 \<sigma> ts \<le> fold_acc_projected prj acc2 \<sigma> ts"
  using assms by (simp add: fold_acc_projected_as_foldr le_supI1)

text \<open>
  Monotonicity in the \<^emph>\<open>environment\<close> rather than the accumulator. This is
  where \<open>prj\<close> and \<open>emb\<close> stop being arbitrary: a fold inherits its
  contributions' monotonicity only if the two also preserve order. Publications
  and dependencies need no such hypothesis, since neither passes through them.
\<close>

lemma fold_acc_projected_env_mono:
  fixes prj :: "'a::bounded_semilattice_sup_bot \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  assumes prj_mono: "mono prj"
    and trees_mono: "\<And>t. t \<in> set ts \<Longrightarrow> traverse_rhs t \<sigma>1 \<le> traverse_rhs t \<sigma>2"
  shows "fold_acc_projected prj acc \<sigma>1 ts \<le> fold_acc_projected prj acc \<sigma>2 ts"
  unfolding fold_acc_projected_as_foldr
  by (rule sup_mono[OF order_refl])
     (rule foldr_sup_mono, rule monoD[OF prj_mono, OF trees_mono])

lemma traverse_fold_rhs_projected_mono:
  fixes prj :: "'a::bounded_semilattice_sup_bot \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  assumes prj_mono: "mono prj"
    and emb_mono: "mono emb"
    and trees_mono: "\<And>t. t \<in> set ts \<Longrightarrow> traverse_rhs t \<sigma>1 \<le> traverse_rhs t \<sigma>2"
  shows "traverse_rhs (sp_compile (fold_rhs_projected prj emb acc ts)) \<sigma>1
       \<le> traverse_rhs (sp_compile (fold_rhs_projected prj emb acc ts)) \<sigma>2"
  unfolding traverse_fold_rhs_projected_char
  by (rule monoD[OF emb_mono])
     (rule fold_acc_projected_env_mono[OF prj_mono trees_mono])

lemma sides_of_rhs_fold_rhs_projected_mono:
  fixes ts :: "('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree list"
  assumes trees_mono: "\<And>t. t \<in> set ts \<Longrightarrow> sides_of_rhs t \<sigma>1 \<le> sides_of_rhs t \<sigma>2"
  shows "sides_of_rhs (sp_compile (fold_rhs_projected prj emb acc ts)) \<sigma>1
       \<le> sides_of_rhs (sp_compile (fold_rhs_projected prj emb acc ts)) \<sigma>2"
  unfolding le_fun_def sides_of_rhs_fold_rhs_projected_char
  using trees_mono
  by (fastforce simp: le_fun_def
        intro: order_trans[OF _ foldr_sup_member_le])

text \<open>A fold of Side-free contributions is Side-free --- the fold's own
  \<open>Answer\<close> publishes nothing, whatever the accumulator holds.\<close>

lemma sides_of_rhs_fold_rhs_projected_bot:
  fixes ts :: "('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree list"
  assumes "\<And>t z. t \<in> set ts \<Longrightarrow> sides_of_rhs t \<sigma> z = bot"
  shows "sides_of_rhs (sp_compile (fold_rhs_projected prj emb acc ts)) \<sigma> = bot"
  using assms
  by (auto simp: fun_eq_iff sides_of_rhs_fold_rhs_projected_char
        intro: foldr_sup_bot_of_all_bot)

lemma sides_of_rhs_fold_rhs_projected_acc_indep:
  fixes ts :: "('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree list"
  shows "sides_of_rhs (sp_compile (fold_rhs_projected prj emb acc1 ts)) \<sigma>
       = sides_of_rhs (sp_compile (fold_rhs_projected prj emb acc2 ts)) \<sigma>"
  by (simp add: fun_eq_iff sides_of_rhs_fold_rhs_projected_char)

lemma dep_aux_fold_rhs_projected_acc_indep:
  "dep_aux \<sigma> (sp_compile (fold_rhs_projected prj emb acc1 ts))
     = dep_aux \<sigma> (sp_compile (fold_rhs_projected prj emb acc2 ts))"
  by (simp add: dep_aux_fold_rhs_projected_char)

subsection \<open>Accumulating the whole answer\<close>

text \<open>The identity instance: nothing is projected away, so the accumulator has
  the answer type and every contribution joins into the node's answer whole.\<close>

definition fold_rhs_contributions ::
  "'a::semilattice_sup
   \<Rightarrow> ('k, 'g, 'a) strategy_tree list
   \<Rightarrow> ('k, 'g, 'a, 'a) strategy_program"
where
  "fold_rhs_contributions acc ts = fold_rhs_projected id id acc ts"

lemma fold_rhs_contributions_simps [simp, code]:
  "fold_rhs_contributions acc [] = sp_return acc"
  "fold_rhs_contributions acc (t # ts) =
     do { res \<leftarrow> sp_lift_tree t; fold_rhs_contributions (acc \<squnion> res) ts }"
  by (simp_all add: fold_rhs_contributions_def)

theorem traverse_fold_rhs_contributions_char:
  "traverse_rhs (sp_compile (fold_rhs_contributions acc ts)) \<sigma>
     = foldl (\<lambda>acc' t. acc' \<squnion> traverse_rhs t \<sigma>) acc ts"
  by (induction ts arbitrary: acc) (simp_all add: sp_compile_def sp_compile_with_bind)

text \<open>The same answer as a right fold. \<open>traverse_fold_rhs_contributions_char\<close>
  states the accumulator threading in evaluation order, which is a left fold;
  proofs about a node's contributions are usually already phrased as a right
  fold, and \<^const>\<open>traverse_rhs\<close> only ever joins, so the two agree.\<close>

theorem traverse_fold_rhs_contributions_char_foldr:
  "traverse_rhs (sp_compile (fold_rhs_contributions acc ts)) \<sigma>
     = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') ts acc"
  by (induction ts arbitrary: acc)
     (simp_all add: sp_compile_def sp_compile_with_bind foldr_sup_seed_swap)

theorem sides_of_rhs_fold_rhs_contributions_char:
  fixes ts :: "('x,'g,'d::bounded_semilattice_sup_bot) strategy_tree list"
  shows "sides_of_rhs (sp_compile (fold_rhs_contributions acc ts)) \<sigma> z
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> z \<squnion> acc') ts \<bottom>"
  unfolding fold_rhs_contributions_def
  by (rule sides_of_rhs_fold_rhs_projected_char)

theorem dep_aux_fold_rhs_contributions_char:
  "dep_aux \<sigma> (sp_compile (fold_rhs_contributions acc ts)) = (\<Union>t\<in>set ts. dep_aux \<sigma> t)"
  unfolding fold_rhs_contributions_def
  by (rule dep_aux_fold_rhs_projected_char)


subsection \<open>Dependency-property preservation\<close>

text \<open>
  A fold of trees whose query set is (respectively environment-independent,
  monotone in the environment) is itself environment-independent (monotone) --
  the list-level analogue of \<^const>\<open>env_indep_deps\<close>/\<^const>\<open>mono_tree_deps\<close>'s
  own single-tree closure facts, and what lets a generator's whole-node
  dependency obligation reduce to a per-hook one.

  Both read straight off \<open>dep_aux_fold_rhs_projected_char\<close>: a fold's
  dependencies are the union of its contributions', so whatever closure
  property each contribution has, the union inherits.
\<close>

lemma env_indep_deps_fold_rhs_projected:
  assumes "\<And>t. t \<in> set ts \<Longrightarrow> env_indep_deps t"
  shows "env_indep_deps (sp_compile (fold_rhs_projected prj emb acc ts))"
  using assms
  unfolding env_indep_deps_def
  by (simp add: dep_aux_fold_rhs_projected_char) blast

lemma mono_tree_deps_fold_rhs_projected:
  assumes "\<And>t. t \<in> set ts \<Longrightarrow> mono_tree_deps t"
  shows "mono_tree_deps (sp_compile (fold_rhs_projected prj emb acc ts))"
  using assms
  unfolding mono_tree_deps_def
  by (fastforce simp: dep_aux_fold_rhs_projected_char)

end

