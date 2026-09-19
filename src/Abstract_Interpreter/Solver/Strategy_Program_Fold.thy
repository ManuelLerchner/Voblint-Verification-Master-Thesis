theory Strategy_Program_Fold
  imports Strategy_Tree_Program
begin

section \<open>Folding a right-hand side from contribution programs\<close>

text \<open>
  An equation's right-hand side is assembled from a list of contributions ---
  one per incoming contribution, such as an intra predecessor, a call return, or
  a routed activation hook --- joined into one answer. Each contribution is a
  \<^emph>\<open>program\<close>, not a finished tree: the fold sequences them with \<open>\<bind>\<close>, joining
  each answer into a running accumulator, and the result is again a program.
  Nothing is compiled here. A generator compiles once, at the end, where the
  solver takes over.

  That is why the characterizations below can speak one vocabulary on both
  sides. \<open>traverse_program\<close>, \<open>sides_of_program\<close> and \<open>dep_program\<close> ask a
  contribution the same questions they ask the fold, and each hypothesis
  \<open>\<forall>p \<in> set ps. sp_wf p\<close> is what makes asking them of a program well posed at
  all: an arbitrary program may ignore or duplicate its continuation, and then
  what it publishes would depend on what follows it.

  The fold never emits a \<^const>\<open>Side\<close> itself: a fold of Side-free
  contributions stays Side-free, which is what lets a generator publish once,
  after the whole fold, instead of once per contribution --- several updates to
  one key during a single right-hand-side evaluation otherwise change what the
  vendored solver's per-origin update rule widens against.

  What a caller varies is \<^emph>\<open>how much of each answer accumulates\<close>. The fold
  therefore takes a projection \<open>prj\<close> into the accumulator and an embedding
  \<open>emb\<close> back out. At the identity pair the whole answer accumulates. A D/G
  instance instead projects the local half into the accumulator and embeds the
  result as \<open>DG d bot\<close>; the global half of a contribution simply does not reach
  the node's answer, and a contribution that has one to share must publish
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

text \<open>Several contribution programs, one right-hand side: run each in list order, join its
  answer into the accumulator, and answer with the accumulator.  \<open>prj\<close> and \<open>emb\<close> keep the
  fold generic in which part of an answer accumulates -- that is what later lets the D/G
  layer join the local half while the global half travels as a side effect.\<close>

fun fold_rhs_program_projected ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b::semilattice_sup
   \<Rightarrow> ('k, 'g, 'a, 'a) strategy_program list
   \<Rightarrow> ('k, 'g, 'a, 'a) strategy_program"
where
  "fold_rhs_program_projected prj emb acc [] = sp_return (emb acc)"
| "fold_rhs_program_projected prj emb acc (p # ps) =
     do {
       res \<leftarrow> p;
       fold_rhs_program_projected prj emb (acc \<squnion> prj res) ps
     }"

text \<open>The accumulator read declaratively off a valuation, rather than run.
  Every answer characterization below is stated through it.\<close>

fun fold_acc_projected ::
  "('a::bounded_semilattice_sup_bot \<Rightarrow> 'b::semilattice_sup) \<Rightarrow> 'b
   \<Rightarrow> ('k + 'g \<Rightarrow> 'a) \<Rightarrow> ('k, 'g, 'a, 'a) strategy_program list \<Rightarrow> 'b"
where
  "fold_acc_projected prj acc \<sigma> [] = acc"
| "fold_acc_projected prj acc \<sigma> (p # ps) =
     fold_acc_projected prj (acc \<squnion> prj (traverse_program p \<sigma>)) \<sigma> ps"

subsection \<open>Declarative characterizations\<close>

text \<open>
  Contributions are traversed in list order: each answer joins the running
  accumulator before the next program runs. The publication and dependency
  characterizations forget that order, the underlying operation being
  commutative --- a set union for \<^const>\<open>dep_aux\<close>, a join seeded at \<open>bot\<close> for
  \<^const>\<open>sides_of_rhs\<close> --- and neither sees \<open>prj\<close> or \<open>emb\<close> at all: what a fold
  publishes and reads is its contributions' business, not its accumulator's.
  That is also why both are independent of the accumulator it starts from.
\<close>

theorem traverse_fold_rhs_program_projected_char:
  assumes "\<forall>p \<in> set ps. sp_wf p"
  shows "traverse_program (fold_rhs_program_projected prj emb acc ps) \<sigma>
     = emb (fold_acc_projected prj acc \<sigma> ps)"
  using assms
  by (induction ps arbitrary: acc)
     (simp_all add: sp_compile_def sp_compile_with_bind traverse_rhs_sp_wf)

theorem sides_of_program_fold_rhs_program_projected_char:
  fixes ps :: "('x, 'g, 'd::bounded_semilattice_sup_bot, 'd) strategy_program list"
  assumes "\<forall>p \<in> set ps. sp_wf p"
  shows "sides_of_program (fold_rhs_program_projected prj emb acc ps) \<sigma> z
     = foldr (\<lambda>p acc'. sides_of_program p \<sigma> z \<squnion> acc') ps \<bottom>"
  using assms
  by (induction ps arbitrary: acc)
     (auto simp add: sp_compile_def sp_compile_with_bind sides_of_rhs_sp_wf traverse_rhs_sp_wf)

theorem dep_program_fold_rhs_program_projected_char:
  assumes "\<forall>p \<in> set ps. sp_wf p"
  shows "dep_program \<sigma> (fold_rhs_program_projected prj emb acc ps)
     = (\<Union>p\<in>set ps. dep_program \<sigma> p)"
  using assms
  by (induction ps arbitrary: acc)
     (auto simp add: sp_compile_def sp_compile_with_bind dep_aux_sp_wf traverse_rhs_sp_wf)

lemma fold_acc_projected_as_foldr:
  fixes prj :: "'a::bounded_semilattice_sup_bot \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  shows "fold_acc_projected prj acc \<sigma> ps
           = acc \<squnion> foldr (\<lambda>p a. prj (traverse_program p \<sigma>) \<squnion> a) ps bot"
  by (induction ps arbitrary: acc) (simp_all add: sup_assoc)

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
    and progs_mono: "\<And>p. p \<in> set ps \<Longrightarrow> traverse_program p \<sigma>1 \<le> traverse_program p \<sigma>2"
  shows "fold_acc_projected prj acc \<sigma>1 ps \<le> fold_acc_projected prj acc \<sigma>2 ps"
  unfolding fold_acc_projected_as_foldr
  by (rule sup_mono[OF order_refl])
     (rule foldr_sup_mono, rule monoD[OF prj_mono, OF progs_mono])

lemma traverse_fold_rhs_program_projected_mono:
  fixes prj :: "'a::bounded_semilattice_sup_bot \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
    and prj_mono: "mono prj"
    and emb_mono: "mono emb"
    and progs_mono: "\<And>p. p \<in> set ps \<Longrightarrow> traverse_program p \<sigma>1 \<le> traverse_program p \<sigma>2"
  shows "traverse_program (fold_rhs_program_projected prj emb acc ps) \<sigma>1
       \<le> traverse_program (fold_rhs_program_projected prj emb acc ps) \<sigma>2"
  unfolding traverse_fold_rhs_program_projected_char[OF wf]
  by (rule monoD[OF emb_mono])
     (rule fold_acc_projected_env_mono[OF prj_mono progs_mono])

lemma sides_of_program_fold_rhs_program_projected_mono:
  fixes ps :: "('x, 'g, 'd::bounded_semilattice_sup_bot, 'd) strategy_program list"
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
    and progs_mono: "\<And>p. p \<in> set ps \<Longrightarrow> sides_of_program p \<sigma>1 \<le> sides_of_program p \<sigma>2"
  shows "sides_of_program (fold_rhs_program_projected prj emb acc ps) \<sigma>1
       \<le> sides_of_program (fold_rhs_program_projected prj emb acc ps) \<sigma>2"
  unfolding le_fun_def sides_of_program_fold_rhs_program_projected_char[OF wf]
  using progs_mono
  by (fastforce simp: le_fun_def
        intro: order_trans[OF _ foldr_sup_member_le])

text \<open>A fold of Side-free contributions is Side-free --- the fold's own
  \<open>Answer\<close> publishes nothing, whatever the accumulator holds.\<close>

lemma sides_of_program_fold_rhs_program_projected_bot:
  fixes ps :: "('x, 'g, 'd::bounded_semilattice_sup_bot, 'd) strategy_program list"
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
    and "\<And>p z. p \<in> set ps \<Longrightarrow> sides_of_program p \<sigma> z = bot"
  shows "sides_of_program (fold_rhs_program_projected prj emb acc ps) \<sigma> = bot"
  using assms
  by (auto simp: fun_eq_iff sides_of_program_fold_rhs_program_projected_char[OF wf]
        intro: foldr_sup_bot_of_all_bot)

lemma sides_of_program_fold_rhs_program_projected_acc_indep:
  fixes ps :: "('x, 'g, 'd::bounded_semilattice_sup_bot, 'd) strategy_program list"
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
  shows "sides_of_program (fold_rhs_program_projected prj emb acc1 ps) \<sigma>
       = sides_of_program (fold_rhs_program_projected prj emb acc2 ps) \<sigma>"
  by (simp add: fun_eq_iff sides_of_program_fold_rhs_program_projected_char[OF wf])

lemma dep_program_fold_rhs_program_projected_acc_indep:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
  shows "dep_program \<sigma> (fold_rhs_program_projected prj emb acc1 ps)
     = dep_program \<sigma> (fold_rhs_program_projected prj emb acc2 ps)"
  by (simp add: dep_program_fold_rhs_program_projected_char[OF wf])

subsection \<open>Accumulating the whole answer\<close>

text \<open>The identity instance: nothing is projected away, so the accumulator has
  the answer type and every contribution joins into the node's answer whole.\<close>

lemma sp_wf_fold_rhs_program_projected [intro]:
  "\<forall>p \<in> set ps. sp_wf p \<Longrightarrow> sp_wf (fold_rhs_program_projected prj emb acc ps)"
  by (induction ps arbitrary: acc) auto

definition fold_rhs_program ::
  "'a::semilattice_sup
   \<Rightarrow> ('k, 'g, 'a, 'a) strategy_program list
   \<Rightarrow> ('k, 'g, 'a, 'a) strategy_program"
where
  "fold_rhs_program acc ps = fold_rhs_program_projected id id acc ps"

lemma sp_wf_fold_rhs_program [intro]:
  "\<forall>p \<in> set ps. sp_wf p \<Longrightarrow> sp_wf (fold_rhs_program acc ps)"
  unfolding fold_rhs_program_def by (rule sp_wf_fold_rhs_program_projected)

lemma fold_rhs_program_simps [simp, code]:
  "fold_rhs_program acc [] = sp_return acc"
  "fold_rhs_program acc (p # ps) =
     do { res \<leftarrow> p; fold_rhs_program (acc \<squnion> res) ps }"
  by (simp_all add: fold_rhs_program_def)

theorem traverse_fold_rhs_program_char:
  assumes "\<forall>p \<in> set ps. sp_wf p"
  shows "traverse_program (fold_rhs_program acc ps) \<sigma>
     = foldl (\<lambda>acc' p. acc' \<squnion> traverse_program p \<sigma>) acc ps"
  using assms
  by (induction ps arbitrary: acc)
     (simp_all add: sp_compile_def sp_compile_with_bind traverse_rhs_sp_wf)

text \<open>The same answer as a right fold. \<open>traverse_fold_rhs_program_char\<close>
  states the accumulator threading in evaluation order, which is a left fold;
  proofs about a node's contributions are usually already phrased as a right
  fold, and \<^const>\<open>traverse_rhs\<close> only ever joins, so the two agree.\<close>

theorem traverse_fold_rhs_program_char_foldr:
  assumes "\<forall>p \<in> set ps. sp_wf p"
  shows "traverse_program (fold_rhs_program acc ps) \<sigma>
     = foldr (\<lambda>p acc'. traverse_program p \<sigma> \<squnion> acc') ps acc"
  using assms
  by (induction ps arbitrary: acc)
     (simp_all add: sp_compile_def sp_compile_with_bind foldr_sup_seed_swap
        traverse_rhs_sp_wf)

theorem sides_of_program_fold_rhs_program_char:
  fixes ps :: "('x,'g,'d::bounded_semilattice_sup_bot,'d) strategy_program list"
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
  shows "sides_of_program (fold_rhs_program acc ps) \<sigma> z
     = foldr (\<lambda>p acc'. sides_of_program p \<sigma> z \<squnion> acc') ps \<bottom>"
  unfolding fold_rhs_program_def
  by (rule sides_of_program_fold_rhs_program_projected_char[OF wf])

theorem dep_program_fold_rhs_program_char:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
  shows "dep_program \<sigma> (fold_rhs_program acc ps) = (\<Union>p\<in>set ps. dep_program \<sigma> p)"
  unfolding fold_rhs_program_def
  by (rule dep_program_fold_rhs_program_projected_char[OF wf])


subsection \<open>Dependency-property preservation\<close>

text \<open>
  A fold of programs whose query set is (respectively environment-independent,
  monotone in the environment) is itself environment-independent (monotone) --
  the list-level analogue of \<^const>\<open>env_indep_deps\<close>/\<^const>\<open>mono_tree_deps\<close>'s
  own single-tree closure facts, and what lets a generator's whole-node
  dependency obligation reduce to a per-hook one.

  Both read straight off \<open>dep_program_fold_rhs_program_projected_char\<close>: a fold's
  dependencies are the union of its contributions', so whatever closure
  property each contribution has, the union inherits.
\<close>

lemma env_indep_deps_fold_rhs_program_projected:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
    and "\<And>p. p \<in> set ps \<Longrightarrow> env_indep_deps (sp_compile p)"
  shows "env_indep_deps (sp_compile (fold_rhs_program_projected prj emb acc ps))"
  using assms
  unfolding env_indep_deps_def
  by (auto simp add: dep_program_fold_rhs_program_projected_char[OF wf]; blast)

lemma mono_tree_deps_fold_rhs_program_projected:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
    and "\<And>p. p \<in> set ps \<Longrightarrow> mono_tree_deps (sp_compile p)"
  shows "mono_tree_deps (sp_compile (fold_rhs_program_projected prj emb acc ps))"
  using assms
  unfolding mono_tree_deps_def
  by (fastforce simp: dep_program_fold_rhs_program_projected_char[OF wf])

end

