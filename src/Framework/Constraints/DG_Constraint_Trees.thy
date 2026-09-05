theory DG_Constraint_Trees
  imports DG_State "Voblint_Solver.Strategy_Tree_Fold"
begin

context
begin

text \<open>
  This theory reasons about \<^const>\<open>sp_compile\<close> at the compiled-tree level
  throughout, so \<open>sp_compile_def\<close> is simp for its whole body -- a local
  re-declaration, not exported to importers, which keep the public
  discipline of crossing that boundary explicitly.
\<close>
declare sp_compile_def [simp]

section \<open>What a right-hand side over the packed D/G carrier is\<close>

text \<open>
  What a generator hands the solver, and how several of those combine. An edge
  former takes its source as an address in the solver's own valuation space and
  its published slot as an explicit key, and produces a strategy program the
  solver can run: the tree reads what it needs, publishes what it must, and
  answers with a \<^type>\<open>dg_state\<close>. A generator that has several such trees for
  one unknown --- several predecessors, several call sites --- folds them here,
  and the fold's own answer, publications and dependencies are each the join,
  respectively union, over the members.

  \<^theory>\<open>Voblint_Framework.DG_State\<close> supplies the value type and its lattice.
  Nothing here inspects a domain, a variable, a global classifier, or a CFG: an
  address and a key are all a former sees, which is why the same former reads a
  contribution-only unknown and an equation-driven one.\<close>

subsection \<open>Low-level edge formers over a solution address\<close>

text \<open>
  The two formers in this subsection take a step in the direct shape
  \<open>'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl\<close>, which no analysis writes any more: a specification
  supplies manager-native transfers, and \<open>DG_Spec\<close> compiles those. They
  survive because the keyed-solver update-rule regression
  needs a step it can vary directly, without a \<open>dg_spec\<close> in the way, and that
  regression is their only consumer. Read them as the minimal thing a
  right-hand side can be, not as the shape production equations take.

  An edge or combine former takes its source as an \<^emph>\<open>address\<close> in the solver's
  own valuation space \<^typ>\<open>'x + 'k\<close> and its published slot as an explicit key,
  rather than fixing the source to a local unknown and the slot to the
  \<^typ>\<open>unit\<close> key -- what lets a keyed generator target an arbitrary
  activation-indexed unknown directly, with no separate address-rewriting pass.

  A program point whose value is carried by a contribution-only unknown --
  one with no equation of its own, so that its value is exactly the join of
  what was published to it -- is then read by exactly the same former as one
  carried by an equation-driven unknown, since \<^const>\<open>QueryL\<close> and
  \<^const>\<open>QueryG\<close> project the same valuation.

  \<^const>\<open>sp_read_at\<close> itself (\<^theory>\<open>Voblint_Solver.Strategy_Tree_Program\<close>) is a
  generic solver-address dispatcher with no notion of \<open>D\<close>/\<open>G\<close>; here it is
  instantiated at \<open>'d = ('dl, 'dg) dg_state\<close>, so the value it returns is
  already one of this file's packed \<open>DG _ bot\<close> / \<open>DG bot _\<close> slots, not a raw
  \<open>D\<close>. Reading through an address is therefore an operation on already-packed
  DG state, not a general "query something of unknown kind" primitive.
\<close>

definition dg_edge_tree_at ::
  "('dl::bounded_semilattice_sup_bot \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> 'x + 'k \<Rightarrow> 'k \<Rightarrow> ('x, 'k, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_edge_tree_at step src gk =
     sp_compile (do {
       d \<leftarrow> sp_read_at src;
       g \<leftarrow> sp_read_global gk;
       _ \<leftarrow> sp_publish gk (DG bot (fst (step (locals d) (globs g))));
       sp_return (DG (snd (step (locals d) (globs g))) bot)
     })"

definition dg_edge_contribution_tree_at ::
  "('dl::bounded_semilattice_sup_bot \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> 'x + 'k \<Rightarrow> 'k \<Rightarrow> ('x, 'k, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_edge_contribution_tree_at step src gk =
     sp_compile (do {
       d \<leftarrow> sp_read_at src;
       g \<leftarrow> sp_read_global gk;
       sp_return (DG (snd (step (locals d) (globs g))) (fst (step (locals d) (globs g))))
     })"

lemma dep_aux_dg_edge_tree_at:
  "dep_aux tau (dg_edge_tree_at step src gk) = {src, Inr gk}"
  by (cases src) (simp_all add: dg_edge_tree_at_def)

subsection \<open>The framework boundary, as theorems\<close>

text \<open>
  Two independent opaque domains. An analysis provides
  \<open>step : D \<Rightarrow> G \<Rightarrow> G \<times> D\<close> --- transfer plus publication; the framework reads the
  source address's \<open>D\<close> and the published slot's \<open>G\<close>, and transports the step's
  \<open>Side : G\<close> and \<open>Answer : D\<close>. Slot packing (\<open>DG _ bot\<close> / \<open>DG bot _\<close>) encodes the
  two-typed unknown space into the solver's single value type; the framework
  never looks inside \<open>D\<close> or \<open>G\<close>. The two theorems say so for \<^emph>\<open>every\<close> step and
  every address: an answer carries no \<open>G\<close>, a publication no \<open>D\<close>.
\<close>

subsection \<open>Why a Side-free analogue exists\<close>

text \<open>
  \<^const>\<open>dg_edge_tree_at\<close> publishes its \<open>G\<close> contribution as soon as it is
  evaluated (\<^const>\<open>Side\<close>). When a generator folds several such trees into one
  equation's right-hand side --- several intra predecessors, or several return
  sites --- each one's \<open>Side\<close> is published at a different moment within the same
  evaluation, and the vendored solver's warrowing/APINIS update rule gates
  convergence per \<^emph>\<open>origin\<close>: repeated writes to one key from one origin can
  destabilize the equation's own dependency and never converge.

  \<^const>\<open>dg_edge_contribution_tree_at\<close> is the Side-free analogue. It answers the
  \<^emph>\<open>unsplit\<close> \<open>(G, D)\<close> result as one \<^type>\<open>dg_state\<close> and publishes nothing, so a
  caller folds several of them with \<^const>\<open>fold_rhs_contributions\<close> --- whose own
  \<^const>\<open>Side\<close> is empty --- and splits the aggregate once, after every
  contribution has been read. The two lemmas below are what makes that
  substitution legitimate: each half of the contribution answer is exactly the
  observation the Side form makes.
\<close>

subsection \<open>Folding a list of trees into one D/G value\<close>

text \<open>
  One unknown can have several right-hand sides --- one per intra predecessor,
  one per call site --- and the solver takes one tree per equation.
  \<open>side_rhs_fold_dg\<close> is that reduction: it runs the trees in order, joins their
  answers into a running local accumulator, and answers \<open>DG acc bot\<close>, letting
  each tree's own publications pass through untouched. \<open>side_acc_dg\<close> is the
  same accumulator read declaratively off a valuation, and it is what the
  characterization lemmas below state the fold's three observations --- answer,
  publications, dependencies --- in terms of.
\<close>

fun side_rhs_fold_dg ::
  "'d::bounded_semilattice_sup_bot
   \<Rightarrow> ('x, 'g, ('d, 'h::bounded_semilattice_sup_bot) dg_state) strategy_tree list
   \<Rightarrow> ('x, 'g, ('d, 'h) dg_state, ('d, 'h) dg_state) strategy_program"
where
  "side_rhs_fold_dg acc [] = sp_return (DG acc bot)"
| "side_rhs_fold_dg acc (t # ts) =
     do {
       res \<leftarrow> sp_lift_tree t;
       side_rhs_fold_dg (acc \<squnion> locals res) ts
     }"

fun side_acc_dg ::
  "'d::bounded_semilattice_sup_bot
   \<Rightarrow> ('x + 'g \<Rightarrow> ('d, 'h::bounded_semilattice_sup_bot) dg_state)
   \<Rightarrow> ('x, 'g, ('d, 'h) dg_state) strategy_tree list \<Rightarrow> 'd"
where
  "side_acc_dg acc \<tau> [] = acc"
| "side_acc_dg acc \<tau> (t # ts) =
     side_acc_dg (acc \<squnion> locals (traverse_rhs t \<tau>)) \<tau> ts"

lemma traverse_side_rhs_fold_dg:
  "traverse_rhs (sp_compile (side_rhs_fold_dg acc ts)) \<tau> =
   DG (side_acc_dg acc \<tau> ts) bot"
  by (induction ts arbitrary: acc) (simp_all add: sp_compile_with_bind traverse_rhs_sp_lift_tree)

text \<open>
  \<open>side_rhs_fold_dg\<close>'s accumulator only ever reaches the terminal \<open>Answer\<close>,
  so both its answer and its dependency set are monotone, respectively
  independent, in the accumulator alone --- the recursion skeleton over \<open>ts\<close>
  never branches on \<open>acc\<close>.  These two lemmas isolate that fact so the
  environment-monotonicity and static-dependency lemmas below do not have to
  re-derive it.
\<close>

lemma side_rhs_fold_dg_acc_mono:
  "acc1 \<le> acc2
   \<Longrightarrow> traverse_rhs (sp_compile (side_rhs_fold_dg acc1 ts)) sigma \<le> traverse_rhs (sp_compile (side_rhs_fold_dg acc2 ts)) sigma"
proof (induction ts arbitrary: acc1 acc2)
  case Nil
  then show ?case by (simp add: less_eq_dg_state_def)
next
  case (Cons t ts)
  from Cons.prems have "acc1 \<squnion> locals (traverse_rhs t sigma) \<le> acc2 \<squnion> locals (traverse_rhs t sigma)"
    by (rule sup_mono[OF _ order_refl])
  then show ?case
    using Cons.IH by (simp add: sp_compile_with_bind traverse_rhs_sp_lift_tree)
qed

lemma dep_aux_side_rhs_fold_dg_acc_indep:
  "dep_aux sigma (sp_compile (side_rhs_fold_dg acc1 ts)) = dep_aux sigma (sp_compile (side_rhs_fold_dg acc2 ts))"
proof (induction ts arbitrary: acc1 acc2)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  show ?case
    using Cons.IH[of "acc1 \<squnion> locals (traverse_rhs t sigma)" "acc2 \<squnion> locals (traverse_rhs t sigma)"]
    by (simp add: sp_compile_with_bind dep_aux_sp_lift_tree)
qed

lemma dep_aux_side_rhs_fold_dg_char:
  "dep_aux sigma (sp_compile (side_rhs_fold_dg acc ts)) = (\<Union>t\<in>set ts. dep_aux sigma t)"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have "dep_aux sigma (sp_compile (side_rhs_fold_dg acc (t # ts)))
          = dep_aux sigma t \<union> dep_aux sigma (sp_compile (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t sigma)) ts))"
    by (simp add: sp_compile_with_bind dep_aux_sp_lift_tree)
  also have "dep_aux sigma (sp_compile (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t sigma)) ts))
               = dep_aux sigma (sp_compile (side_rhs_fold_dg acc ts))"
    by (rule dep_aux_side_rhs_fold_dg_acc_indep)
  also have "\<dots> = (\<Union>t\<in>set ts. dep_aux sigma t)"
    by (rule Cons.IH)
  finally show ?case by simp
qed

lemma side_rhs_fold_dg_val_mono:
  "v1 \<le> v2
   \<Longrightarrow> traverse_rhs (sp_compile (side_rhs_fold_dg (acc \<squnion> locals v1) ts)) sigma
         \<le> traverse_rhs (sp_compile (side_rhs_fold_dg (acc \<squnion> locals v2) ts)) sigma"
proof -
  assume "v1 \<le> v2"
  then have "locals v1 \<le> locals v2" unfolding less_eq_dg_state_def by simp
  then have "acc \<squnion> locals v1 \<le> acc \<squnion> locals v2"
    by (rule sup_mono[OF order_refl])
  then show ?thesis by (rule side_rhs_fold_dg_acc_mono)
qed

text \<open>
  Environment-monotonicity of the fold, given every folded tree is itself
  environment-monotone.  \<open>k_mono_val\<close> --- the continuation's monotonicity in
  the value it receives --- reduces to @{thm side_rhs_fold_dg_acc_mono}, and
  \<open>k_mono_env\<close> --- for a fixed value --- is the induction hypothesis on the
  tail, so the only per-tree work @{thm traverse_rhs_sp_lift_tree_mono} leaves is \<open>t_mono\<close>
  itself, supplied by the assumption.
\<close>

lemma side_rhs_fold_dg_mono:
  assumes tree_mono: "\<forall>t \<in> set ts. \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> traverse_rhs t s1 \<le> traverse_rhs t s2"
  shows "\<And>acc s1 s2. s1 \<le> s2 \<Longrightarrow>
           traverse_rhs (sp_compile (side_rhs_fold_dg acc ts)) s1 \<le> traverse_rhs (sp_compile (side_rhs_fold_dg acc ts)) s2"
using tree_mono proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have tail_mono: "\<forall>t' \<in> set ts. \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> traverse_rhs t' s1 \<le> traverse_rhs t' s2"
    using Cons.prems by simp
  note IH = Cons.IH[OF _ tail_mono]
  fix acc s1 s2
  show "s1 \<le> s2 \<Longrightarrow> traverse_rhs (sp_compile (side_rhs_fold_dg acc (t # ts))) s1
          \<le> traverse_rhs (sp_compile (side_rhs_fold_dg acc (t # ts))) s2"
  proof -
    assume le: "s1 \<le> s2"
    have t_mono: "\<And>s1 s2. s1 \<le> s2 \<Longrightarrow> traverse_rhs t s1 \<le> traverse_rhs t s2"
      using Cons.prems by simp
    have k_mono_env: "\<And>v s1 s2. s1 \<le> s2 \<Longrightarrow>
        traverse_rhs (sp_compile (side_rhs_fold_dg (acc \<squnion> locals v) ts)) s1
          \<le> traverse_rhs (sp_compile (side_rhs_fold_dg (acc \<squnion> locals v) ts)) s2"
      using IH by blast
    have k_mono_val: "\<And>s v1 v2. v1 \<le> v2 \<Longrightarrow>
        traverse_rhs (sp_compile (side_rhs_fold_dg (acc \<squnion> locals v1) ts)) s
          \<le> traverse_rhs (sp_compile (side_rhs_fold_dg (acc \<squnion> locals v2) ts)) s"
      by (rule side_rhs_fold_dg_val_mono)
    show "traverse_rhs (sp_compile (side_rhs_fold_dg acc (t # ts))) s1
            \<le> traverse_rhs (sp_compile (side_rhs_fold_dg acc (t # ts))) s2"
      using traverse_rhs_sp_lift_tree_mono[OF t_mono k_mono_env k_mono_val le]
      by (simp add: sp_compile_with_bind)
  qed
qed

text \<open>
  Static dependencies of the fold, given every folded tree has static
  dependencies. The chain at each cons cell relates the two accumulators
  first by @{thm dep_aux_side_rhs_fold_dg_acc_indep} (their dependency sets
  agree at a fixed environment regardless of the accumulator), then by the
  induction hypothesis (the tail's dependency set is itself environment
  independent).
\<close>

lemma side_rhs_fold_dg_env_indep_deps:
  assumes tree_static: "\<forall>t \<in> set ts. env_indep_deps t"
  shows "env_indep_deps (sp_compile (side_rhs_fold_dg acc ts))"
  unfolding env_indep_deps_def
proof (intro allI)
  fix sigma1 sigma2
  show "dep_aux sigma1 (sp_compile (side_rhs_fold_dg acc ts)) = dep_aux sigma2 (sp_compile (side_rhs_fold_dg acc ts))"
    using tree_static
  proof (induction ts arbitrary: acc)
    case Nil
    then show ?case by simp
  next
    case (Cons t ts)
    have t_static: "dep_aux sigma1 t = dep_aux sigma2 t"
      using Cons.prems unfolding env_indep_deps_def by simp
    have tail_static: "\<forall>t' \<in> set ts. env_indep_deps t'"
      using Cons.prems by simp
    have "dep_aux sigma1 (sp_compile (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t sigma1)) ts))
            = dep_aux sigma1 (sp_compile (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t sigma2)) ts))"
      by (rule dep_aux_side_rhs_fold_dg_acc_indep)
    also have "\<dots> = dep_aux sigma2 (sp_compile (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t sigma2)) ts))"
      using Cons.IH[OF tail_static] by simp
    finally show ?case
      by (simp add: sp_compile_with_bind dep_aux_sp_lift_tree t_static)
  qed
qed

text \<open>
  The vendored solver's own @{const mono_deps} precondition only needs the
  weaker, order-conditional guarantee @{const mono_tree_deps}, not the full
  equality @{const env_indep_deps} proves above; every current fold satisfies
  the strong property anyway, so this is a one-line corollary through
  @{thm env_indep_deps_imp_mono_tree_deps} rather than a separate induction.
\<close>

lemma side_rhs_fold_dg_mono_tree_deps:
  assumes tree_static: "\<forall>t \<in> set ts. env_indep_deps t"
  shows "mono_tree_deps (sp_compile (side_rhs_fold_dg acc ts))"
  by (rule env_indep_deps_imp_mono_tree_deps[OF side_rhs_fold_dg_env_indep_deps[OF tree_static]])

text \<open>
  The fold's Side contributions are carried only by the per-tree Side nodes;
  the accumulator flows into the final \<open>Answer\<close> (whose own sides are \<open>bot\<close>),
  so the side map is acc-independent --- the same fact
  @{thm dep_aux_side_rhs_fold_dg_acc_indep} established for dependencies,
  mirrored here for sides. This is what lets @{thm side_rhs_fold_dg_mono}'s
  proof strategy repeat for @{const sides_of_rhs} without also needing
  @{const traverse_rhs}-monotonicity as a hypothesis.
\<close>

lemma sides_of_rhs_side_rhs_fold_dg_acc_indep:
  "sides_of_rhs (sp_compile (side_rhs_fold_dg acc1 ts)) sigma = sides_of_rhs (sp_compile (side_rhs_fold_dg acc2 ts)) sigma"
proof (induction ts arbitrary: acc1 acc2)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  show ?case
    using Cons.IH[of "acc1 \<squnion> locals (traverse_rhs t sigma)" "acc2 \<squnion> locals (traverse_rhs t sigma)"]
    by (simp add: sp_compile_with_bind sides_of_rhs_sp_lift_tree)
qed

text \<open>
  The declarative twin of \<^const>\<open>side_acc_dg\<close>: \<open>side_rhs_fold_dg\<close>'s side contribution
  at any one key is a plain fold over each element's own \<^const>\<open>sides_of_rhs\<close>, seeded at
  \<open>bot\<close> rather than the running local accumulator -- @{thm
  sides_of_rhs_side_rhs_fold_dg_acc_indep} already shows the accumulator never affects a
  side read, so unfolding \<^const>\<open>sp_lift_tree\<close>'s side equation and re-seeding at \<open>bot\<close>
  after each step is exact, not merely a bound.
\<close>

lemma sides_of_rhs_side_rhs_fold_dg_char:
  fixes ts :: "('x, 'k, ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state)
                 strategy_tree list"
  shows "sides_of_rhs (sp_compile (side_rhs_fold_dg acc ts)) \<tau> z = foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') ts bot"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have "sides_of_rhs (sp_compile (side_rhs_fold_dg acc (t # ts))) \<tau> z
          = sides_of_rhs t \<tau> z \<squnion> sides_of_rhs (sp_compile (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t \<tau>)) ts)) \<tau> z"
    by (simp add: sp_compile_with_bind)
  also have "sides_of_rhs (sp_compile (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t \<tau>)) ts)) \<tau> z
               = sides_of_rhs (sp_compile (side_rhs_fold_dg acc ts)) \<tau> z"
    using sides_of_rhs_side_rhs_fold_dg_acc_indep[of "acc \<squnion> locals (traverse_rhs t \<tau>)" ts \<tau> acc] by simp
  also have "\<dots> = foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') ts bot"
    by (rule Cons.IH)
  finally show ?case by simp
qed

text \<open>
  Grouping is invisible to a fold. All three observables of \<^const>\<open>side_rhs_fold_dg\<close> ---
  the local accumulator, the side contribution at one key, and the dependency set --- are
  sups, respectively unions, over the elements, so replacing a segment by a segment of
  nested folds with the same underlying elements changes nothing. This is what lets a
  generator that folds one tree per call site agree with one that folds one tree per
  call-site/callee pair.
\<close>

lemma foldr_sup_acc:
  fixes f :: "'a \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  shows "foldr (\<lambda>t a. f t \<squnion> a) xs bot \<squnion> b = foldr (\<lambda>t a. f t \<squnion> a) xs b"
  by (induction xs) (simp_all add: sup_assoc)

lemma foldr_sup_le_iff:
  fixes f :: "'a \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  shows "foldr (\<lambda>t a. f t \<squnion> a) xs bot \<le> y \<longleftrightarrow> (\<forall>x \<in> set xs. f x \<le> y)"
  by (induction xs) auto

lemma foldr_sup_set_cong:
  fixes f :: "'a \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  assumes eq: "set xs = set ys"
  shows "foldr (\<lambda>t a. f t \<squnion> a) xs b = foldr (\<lambda>t a. f t \<squnion> a) ys b"
proof -
  have "foldr (\<lambda>t a. f t \<squnion> a) xs bot = foldr (\<lambda>t a. f t \<squnion> a) ys bot"
  proof (rule antisym)
    show "foldr (\<lambda>t a. f t \<squnion> a) xs bot \<le> foldr (\<lambda>t a. f t \<squnion> a) ys bot"
      using eq foldr_sup_le_iff[of f ys "foldr (\<lambda>t a. f t \<squnion> a) ys bot"]
      by (simp add: foldr_sup_le_iff)
  next
    show "foldr (\<lambda>t a. f t \<squnion> a) ys bot \<le> foldr (\<lambda>t a. f t \<squnion> a) xs bot"
      using eq foldr_sup_le_iff[of f xs "foldr (\<lambda>t a. f t \<squnion> a) xs bot"]
      by (simp add: foldr_sup_le_iff)
  qed
  then show ?thesis
    using foldr_sup_acc[of f xs b] foldr_sup_acc[of f ys b] by simp
qed

lemma side_acc_dg_as_foldr:
  "side_acc_dg acc \<tau> ts = acc \<squnion> foldr (\<lambda>t a. locals (traverse_rhs t \<tau>) \<squnion> a) ts bot"
  by (induction ts arbitrary: acc) (simp_all add: sup_assoc)

lemma foldr_sup_locals_map_fold:
  "foldr (\<lambda>t a. locals (traverse_rhs t \<tau>) \<squnion> a) (map (\<lambda>ts. sp_compile (side_rhs_fold_dg bot ts)) tss) b
     = foldr (\<lambda>t a. locals (traverse_rhs t \<tau>) \<squnion> a) (concat tss) b"
  by (induction tss arbitrary: b)
     (simp_all add: traverse_side_rhs_fold_dg side_acc_dg_as_foldr foldr_sup_acc del: sp_compile_def)

lemma foldr_sup_sides_map_fold:
  "foldr (\<lambda>t a. sides_of_rhs t \<tau> z \<squnion> a) (map (\<lambda>ts. sp_compile (side_rhs_fold_dg bot ts)) tss) b
     = foldr (\<lambda>t a. sides_of_rhs t \<tau> z \<squnion> a) (concat tss) b"
  by (induction tss arbitrary: b)
     (simp_all add: sides_of_rhs_side_rhs_fold_dg_char foldr_sup_acc del: sp_compile_def)

lemma side_rhs_fold_dg_flat_cong:
  assumes eq: "set (concat tss) = set us"
  shows
    "traverse_rhs (sp_compile (side_rhs_fold_dg acc (xs @ map (\<lambda>ts. sp_compile (side_rhs_fold_dg bot ts)) tss @ zs))) \<tau>
       = traverse_rhs (sp_compile (side_rhs_fold_dg acc (xs @ us @ zs))) \<tau>"
    "sides_of_rhs (sp_compile (side_rhs_fold_dg acc (xs @ map (\<lambda>ts. sp_compile (side_rhs_fold_dg bot ts)) tss @ zs))) \<tau> z
       = sides_of_rhs (sp_compile (side_rhs_fold_dg acc (xs @ us @ zs))) \<tau> z"
    "dep_aux \<sigma> (sp_compile (side_rhs_fold_dg acc (xs @ map (\<lambda>ts. sp_compile (side_rhs_fold_dg bot ts)) tss @ zs)))
       = dep_aux \<sigma> (sp_compile (side_rhs_fold_dg acc (xs @ us @ zs)))"
proof -
  show "traverse_rhs (sp_compile (side_rhs_fold_dg acc (xs @ map (\<lambda>ts. sp_compile (side_rhs_fold_dg bot ts)) tss @ zs))) \<tau>
          = traverse_rhs (sp_compile (side_rhs_fold_dg acc (xs @ us @ zs))) \<tau>"
    by (simp add: traverse_side_rhs_fold_dg side_acc_dg_as_foldr
          foldr_sup_locals_map_fold foldr_sup_set_cong[OF eq] del: sp_compile_def)
next
  show "sides_of_rhs (sp_compile (side_rhs_fold_dg acc (xs @ map (\<lambda>ts. sp_compile (side_rhs_fold_dg bot ts)) tss @ zs))) \<tau> z
          = sides_of_rhs (sp_compile (side_rhs_fold_dg acc (xs @ us @ zs))) \<tau> z"
    by (simp add: sides_of_rhs_side_rhs_fold_dg_char
          foldr_sup_sides_map_fold foldr_sup_set_cong[OF eq] del: sp_compile_def)
next
  show "dep_aux \<sigma> (sp_compile (side_rhs_fold_dg acc (xs @ map (\<lambda>ts. sp_compile (side_rhs_fold_dg bot ts)) tss @ zs)))
          = dep_aux \<sigma> (sp_compile (side_rhs_fold_dg acc (xs @ us @ zs)))"
    by (auto simp add: dep_aux_side_rhs_fold_dg_char simp flip: eq simp del: sp_compile_def)
qed

lemma side_rhs_fold_dg_sides_mono:
  assumes tree_sides_mono: "\<forall>t \<in> set ts. \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> sides_of_rhs t s1 \<le> sides_of_rhs t s2"
  shows "\<And>acc s1 s2. s1 \<le> s2 \<Longrightarrow>
           sides_of_rhs (sp_compile (side_rhs_fold_dg acc ts)) s1
             \<le> sides_of_rhs (sp_compile (side_rhs_fold_dg acc ts)) s2"
using tree_sides_mono proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have tail_sides_mono: "\<forall>t' \<in> set ts. \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> sides_of_rhs t' s1 \<le> sides_of_rhs t' s2"
    using Cons.prems by simp
  note IH = Cons.IH[OF _ tail_sides_mono]
  fix acc s1 s2
  show "s1 \<le> s2 \<Longrightarrow> sides_of_rhs (sp_compile (side_rhs_fold_dg acc (t # ts))) s1
          \<le> sides_of_rhs (sp_compile (side_rhs_fold_dg acc (t # ts))) s2"
  proof -
    assume le: "s1 \<le> s2"
    have t_sides_mono: "sides_of_rhs t s1 \<le> sides_of_rhs t s2"
      using Cons.prems le by simp
    have tail_mono: "sides_of_rhs (sp_compile (side_rhs_fold_dg acc ts)) s1
                        \<le> sides_of_rhs (sp_compile (side_rhs_fold_dg acc ts)) s2"
      using IH le by blast
    have i1: "sides_of_rhs (sp_compile (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t s1)) ts)) s1
                = sides_of_rhs (sp_compile (side_rhs_fold_dg acc ts)) s1"
      by (rule sides_of_rhs_side_rhs_fold_dg_acc_indep)
    have i2: "sides_of_rhs (sp_compile (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t s2)) ts)) s2
                = sides_of_rhs (sp_compile (side_rhs_fold_dg acc ts)) s2"
      by (rule sides_of_rhs_side_rhs_fold_dg_acc_indep)
    show "sides_of_rhs (sp_compile (side_rhs_fold_dg acc (t # ts))) s1
            \<le> sides_of_rhs (sp_compile (side_rhs_fold_dg acc (t # ts))) s2"
      using sup_mono[OF t_sides_mono tail_mono]
      by (simp add: sides_of_rhs_sp_lift_tree i1[unfolded sp_compile_def] i2[unfolded sp_compile_def]
            sp_compile_with_bind)
  qed
qed

end

end
