theory DG_Constraint_Programs
  imports DG_State "Voblint_Solver.Strategy_Program_Fold"
begin

context
begin

text \<open>
  This theory states its observations at the program level --- \<open>traverse_program\<close>,
  \<open>sides_of_program\<close>, \<open>dep_program\<close> --- reaching for \<^const>\<open>sp_compile\<close> only
  where a statement must meet the vendored solver's own tree vocabulary,
  and does not unfold it globally: the named observation
  equations in \<^theory>\<open>Voblint_Solver.Strategy_Tree_Program\<close> are stated
  against \<open>sp_compile\<close> itself, and proofs meet those rather than the
  compiler's representation.
\<close>

section \<open>What a right-hand side over the packed D/G carrier is\<close>

text \<open>
  What a generator hands the solver, and how several of those combine. An edge
  former takes its source as an address in the solver's own valuation space and
  its published slot as an explicit key, and produces a strategy program the
  solver can run: the program reads what it needs, publishes what it must, and
  answers with a \<^type>\<open>dg_state\<close>. A generator with several such programs for
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
  \<open>'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl\<close>, which no analysis writes: a specification
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

definition dg_edge_program_at ::
  "('dl::bounded_semilattice_sup_bot \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> 'x + 'k \<Rightarrow> 'k
   \<Rightarrow> ('x, 'k, ('dl, 'dg) dg_state, ('dl, 'dg) dg_state) strategy_program"
where
  "dg_edge_program_at step src gk =
     (do {
       d \<leftarrow> sp_read_at src;
       g \<leftarrow> sp_read_global gk;
       _ \<leftarrow> sp_publish gk (DG bot (fst (step (locals d) (globs g))));
       sp_return (DG (snd (step (locals d) (globs g))) bot)
     })"

definition dg_edge_contribution_program_at ::
  "('dl::bounded_semilattice_sup_bot \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> 'x + 'k \<Rightarrow> 'k
   \<Rightarrow> ('x, 'k, ('dl, 'dg) dg_state, ('dl, 'dg) dg_state) strategy_program"
where
  "dg_edge_contribution_program_at step src gk =
     (do {
       d \<leftarrow> sp_read_at src;
       g \<leftarrow> sp_read_global gk;
       sp_return (DG (snd (step (locals d) (globs g))) (fst (step (locals d) (globs g))))
     })"

lemma dep_dg_edge_program_at:
  "dep_program tau (dg_edge_program_at step src gk) = {src, Inr gk}"
  by (cases src) (simp_all add: dg_edge_program_at_def sp_compile_def)

lemma sp_wf_dg_edge_program_at [intro, simp]: "sp_wf (dg_edge_program_at step src gk)"
  unfolding dg_edge_program_at_def by (intro sp_wf_bind) simp_all

lemma sp_wf_dg_edge_contribution_program_at [intro, simp]:
  "sp_wf (dg_edge_contribution_program_at step src gk)"
  unfolding dg_edge_contribution_program_at_def by (intro sp_wf_bind) simp_all

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
  \<^const>\<open>dg_edge_program_at\<close> publishes its \<open>G\<close> contribution as soon as it is
  evaluated (\<^const>\<open>Side\<close>). When a generator folds several such programs into one
  equation's right-hand side --- several intra predecessors, or several return
  sites --- each one's \<open>Side\<close> is published at a different moment within the same
  evaluation, and the vendored solver's warrowing/APINIS update rule gates
  convergence per \<^emph>\<open>origin\<close>: repeated writes to one key from one origin can
  destabilize the equation's own dependency and never converge.

  \<^const>\<open>dg_edge_contribution_program_at\<close> is the Side-free analogue. It answers the
  \<^emph>\<open>unsplit\<close> \<open>(G, D)\<close> result as one \<^type>\<open>dg_state\<close> and publishes nothing, so a
  caller folds several of them with \<^const>\<open>fold_rhs_program\<close> --- whose own
  \<^const>\<open>Side\<close> is empty --- and splits the aggregate once, after every
  contribution has been read. The two lemmas below are what makes that
  substitution legitimate: each half of the contribution answer is exactly the
  observation the Side form makes.
\<close>

subsection \<open>Folding a list of programs into one D/G value\<close>

text \<open>
  One unknown can have several right-hand sides --- one per intra predecessor,
  one per call site --- and the solver takes one tree per equation.
  \<open>side_rhs_fold_dg\<close> is that reduction: it runs the programs in order, joins their
  answers into a running local accumulator, and answers \<open>DG acc bot\<close>, letting
  each program's own publications pass through untouched. \<open>side_acc_dg\<close> is the
  same accumulator read declaratively off a valuation, and it is what the
  characterization lemmas below state the fold's three observations --- answer,
  publications, dependencies --- in terms of.

  Both this and \<^const>\<open>fold_rhs_program\<close> are specializations of one
  fold, \<^const>\<open>fold_rhs_program_projected\<close>, and the choice of specialization is the
  whole direct/buffered split. The identity specialization accumulates
  complete answers, so a contribution's global half joins into the node's
  answer; this one accumulates only \<^const>\<open>locals\<close> and embeds the result as
  \<open>DG d bot\<close>, so a global half never reaches the answer and each program
  publishes its own \<^const>\<open>Side\<close> as it runs. The buffered generator wants the
  first --- it gathers every global contribution into the answer precisely so
  it can publish once per node --- and the direct generator wants the second.
  Replacing either fold by the other would exchange the two generators, not
  simplify them.

  The narrow definitions here exist to keep the D/G vocabulary the generators
  and the routed soundness development actually reason in, rather than
  spelling out \<open>fold_rhs_program_projected locals (\<lambda>d. DG d bot)\<close> in every statement.
  Their algebra is inherited: each observation and monotonicity fact below is
  a specialization of the generic one.
\<close>

definition side_rhs_fold_dg ::
  "'d::bounded_semilattice_sup_bot
   \<Rightarrow> ('x, 'g, ('d, 'h::bounded_semilattice_sup_bot) dg_state,
        ('d, 'h) dg_state) strategy_program list
   \<Rightarrow> ('x, 'g, ('d, 'h) dg_state, ('d, 'h) dg_state) strategy_program"
where
  "side_rhs_fold_dg acc ps = fold_rhs_program_projected locals (\<lambda>d. DG d bot) acc ps"

lemma side_rhs_fold_dg_simps [simp, code]:
  "side_rhs_fold_dg acc [] = sp_return (DG acc bot)"
  "side_rhs_fold_dg acc (p # ps) =
     do {
       res \<leftarrow> p;
       side_rhs_fold_dg (acc \<squnion> locals res) ps
     }"
  by (simp_all add: side_rhs_fold_dg_def)

lemma sp_compile_side_rhs_fold_dg_Cons:
  assumes "sp_wf p"
  shows "sp_compile (side_rhs_fold_dg acc (p # ps))
     = sp_lift_tree (sp_compile p) (\<lambda>v. sp_compile (side_rhs_fold_dg (acc \<squnion> locals v) ps))"
  by (simp add: sp_compile_bind sp_wfD[OF assms])

lemma sp_wf_side_rhs_fold_dg [intro]:
  "\<forall>p \<in> set ps. sp_wf p \<Longrightarrow> sp_wf (side_rhs_fold_dg acc ps)"
  unfolding side_rhs_fold_dg_def by (rule sp_wf_fold_rhs_program_projected)

definition side_acc_dg ::
  "'d::bounded_semilattice_sup_bot
   \<Rightarrow> ('x + 'g \<Rightarrow> ('d, 'h::bounded_semilattice_sup_bot) dg_state)
   \<Rightarrow> ('x, 'g, ('d, 'h) dg_state, ('d, 'h) dg_state) strategy_program list \<Rightarrow> 'd"
where
  "side_acc_dg acc \<tau> ps = fold_acc_projected locals acc \<tau> ps"

lemma side_acc_dg_simps [simp, code]:
  "side_acc_dg acc \<tau> [] = acc"
  "side_acc_dg acc \<tau> (p # ps) =
     side_acc_dg (acc \<squnion> locals (traverse_program p \<tau>)) \<tau> ps"
  by (simp_all add: side_acc_dg_def)

lemma traverse_side_rhs_fold_dg:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
  shows "traverse_program (side_rhs_fold_dg acc ps) \<tau> = DG (side_acc_dg acc \<tau> ps) bot"
  unfolding side_rhs_fold_dg_def side_acc_dg_def
  by (rule traverse_fold_rhs_program_projected_char[OF wf])

text \<open>
  \<open>side_rhs_fold_dg\<close>'s accumulator only ever reaches the terminal \<open>Answer\<close>,
  so both its answer and its dependency set are monotone, respectively
  independent, in the accumulator alone --- the recursion skeleton over \<open>ps\<close>
  never branches on \<open>acc\<close>.  These two lemmas isolate that fact so the
  environment-monotonicity and static-dependency lemmas below do not have to
  re-derive it.
\<close>

lemma side_rhs_fold_dg_acc_mono:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
  shows "acc1 \<le> acc2
   \<Longrightarrow> traverse_program (side_rhs_fold_dg acc1 ps) sigma
         \<le> traverse_program (side_rhs_fold_dg acc2 ps) sigma"
  by (simp add: traverse_side_rhs_fold_dg[OF wf] side_acc_dg_def
        fold_acc_projected_acc_mono)

lemma dep_program_side_rhs_fold_dg_char:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
  shows "dep_program sigma (side_rhs_fold_dg acc ps) = (\<Union>p\<in>set ps. dep_program sigma p)"
  unfolding side_rhs_fold_dg_def
  by (rule dep_program_fold_rhs_program_projected_char[OF wf])

lemma dep_program_side_rhs_fold_dg_acc_indep:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
  shows "dep_program sigma (side_rhs_fold_dg acc1 ps)
     = dep_program sigma (side_rhs_fold_dg acc2 ps)"
  by (simp add: dep_program_side_rhs_fold_dg_char[OF wf])

text \<open>
  The two order-preservation facts the generic fold asks for before it will
  carry its contributions' environment-monotonicity: the D/G instance's
  projection and its embedding.
\<close>

lemma mono_locals: "mono (locals :: ('d::order, 'h::order) dg_state \<Rightarrow> 'd)"
  by (rule monoI) (simp add: less_eq_dg_state_def)

lemma mono_DG_bot:
  "mono (\<lambda>d. DG d bot :: ('d::order, 'h::order_bot) dg_state)"
  by (rule monoI) simp

text \<open>
  Environment-monotonicity of the fold, given every folded program is itself
  environment-monotone. The content is
  \<open>traverse_fold_rhs_program_projected_mono\<close>'s; this instance only supplies the two
  monotonicity facts above.
\<close>

lemma side_rhs_fold_dg_mono:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
    and prog_mono: "\<forall>p \<in> set ps. \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> traverse_program p s1 \<le> traverse_program p s2"
  shows "\<And>acc s1 s2. s1 \<le> s2 \<Longrightarrow>
           traverse_program (side_rhs_fold_dg acc ps) s1
             \<le> traverse_program (side_rhs_fold_dg acc ps) s2"
  using prog_mono
  unfolding side_rhs_fold_dg_def
  by (auto intro!: traverse_fold_rhs_program_projected_mono[OF wf mono_locals mono_DG_bot])

text \<open>
  Static dependencies of the fold, given every folded contribution has static
  dependencies. The chain at each cons cell relates the two accumulators
  first by @{thm dep_program_side_rhs_fold_dg_acc_indep} (their dependency sets
  agree at a fixed environment regardless of the accumulator), then by the
  induction hypothesis (the tail's dependency set is itself environment
  independent).
\<close>

lemma side_rhs_fold_dg_env_indep_deps:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
    and prog_static: "\<And>p. p \<in> set ps \<Longrightarrow> env_indep_deps (sp_compile p)"
  shows "env_indep_deps (sp_compile (side_rhs_fold_dg acc ps))"
  unfolding side_rhs_fold_dg_def
  by (rule env_indep_deps_fold_rhs_program_projected[OF wf prog_static])

text \<open>
  The vendored solver's own @{const mono_deps} precondition only needs the
  weaker, order-conditional guarantee @{const mono_tree_deps}, not the full
  equality @{const env_indep_deps} proves above; every current fold satisfies
  the strong property anyway, so this is a one-line corollary through
  @{thm env_indep_deps_imp_mono_tree_deps} rather than a separate induction.
\<close>

lemma side_rhs_fold_dg_mono_tree_deps:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
    and prog_mono: "\<And>p. p \<in> set ps \<Longrightarrow> mono_tree_deps (sp_compile p)"
  shows "mono_tree_deps (sp_compile (side_rhs_fold_dg acc ps))"
  unfolding side_rhs_fold_dg_def
  by (rule mono_tree_deps_fold_rhs_program_projected[OF wf prog_mono])

text \<open>
  The fold's Side contributions are carried only by the per-contribution Side
  nodes; the accumulator flows into the final \<open>Answer\<close> (whose own sides are
  \<open>bot\<close>), so the side map is acc-independent --- the same fact
  @{thm dep_program_side_rhs_fold_dg_acc_indep} established for dependencies,
  mirrored here for sides. This is what lets @{thm side_rhs_fold_dg_mono}'s
  proof strategy repeat for @{const sides_of_rhs} without also needing
  @{const traverse_rhs}-monotonicity as a hypothesis.
\<close>

lemma sides_of_program_side_rhs_fold_dg_acc_indep:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
  shows "sides_of_program (side_rhs_fold_dg acc1 ps) sigma
     = sides_of_program (side_rhs_fold_dg acc2 ps) sigma"
  unfolding side_rhs_fold_dg_def
  by (rule sides_of_program_fold_rhs_program_projected_acc_indep[OF wf])

text \<open>
  The declarative twin of \<^const>\<open>side_acc_dg\<close>: \<open>side_rhs_fold_dg\<close>'s side contribution
  at any one key is a plain fold over each element's own \<^const>\<open>sides_of_rhs\<close>, seeded at
  \<open>bot\<close> rather than the running local accumulator -- @{thm
  sides_of_program_side_rhs_fold_dg_acc_indep} already shows the accumulator never affects a
  side read, so unfolding \<^const>\<open>sp_lift_tree\<close>'s side equation and re-seeding at \<open>bot\<close>
  after each step is exact, not merely a bound.
\<close>

lemma sides_of_program_side_rhs_fold_dg_char:
  fixes ps :: "('x, 'k, ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state,
                 ('d, 'h) dg_state) strategy_program list"
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
  shows "sides_of_program (side_rhs_fold_dg acc ps) \<tau> z
           = foldr (\<lambda>p acc'. sides_of_program p \<tau> z \<squnion> acc') ps bot"
  unfolding side_rhs_fold_dg_def
  by (rule sides_of_program_fold_rhs_program_projected_char[OF wf])

text \<open>
  Grouping is invisible to a fold. All three observables of \<^const>\<open>side_rhs_fold_dg\<close> ---
  the local accumulator, the side contribution at one key, and the dependency set --- are
  sups, respectively unions, over the elements, so replacing a segment by a segment of
  nested folds with the same underlying elements changes nothing. This is what lets a
  generator that folds one contribution per call site agree with one that folds one per
  call-site/callee pair.
\<close>

lemma side_acc_dg_as_foldr:
  "side_acc_dg acc \<tau> ps = acc \<squnion> foldr (\<lambda>p a. locals (traverse_program p \<tau>) \<squnion> a) ps bot"
  by (simp add: side_acc_dg_def fold_acc_projected_as_foldr)

text \<open>The same equation with the accumulator left as the fold's seed, which is
  how a proof that already has a right fold in hand meets it.\<close>

lemma side_acc_dg_as_foldr_seeded:
  "side_acc_dg acc \<tau> ps = foldr (\<lambda>p a. locals (traverse_program p \<tau>) \<squnion> a) ps acc"
  by (simp only: side_acc_dg_as_foldr foldr_join_seed_out[symmetric])

lemma foldr_sup_locals_map_fold:
  assumes wf: "\<forall>ps \<in> set pss. \<forall>p \<in> set ps. sp_wf p"
  shows "foldr (\<lambda>p a. locals (traverse_program p \<tau>) \<squnion> a)
       (map (\<lambda>ps. side_rhs_fold_dg bot ps) pss) b
     = foldr (\<lambda>p a. locals (traverse_program p \<tau>) \<squnion> a) (concat pss) b"
  using wf
  by (induction pss arbitrary: b)
     (simp_all add: traverse_side_rhs_fold_dg side_acc_dg_as_foldr foldr_sup_acc)

lemma foldr_sup_sides_map_fold:
  assumes wf: "\<forall>ps \<in> set pss. \<forall>p \<in> set ps. sp_wf p"
  shows "foldr (\<lambda>p a. sides_of_program p \<tau> z \<squnion> a) (map (\<lambda>ps. side_rhs_fold_dg bot ps) pss) b
     = foldr (\<lambda>p a. sides_of_program p \<tau> z \<squnion> a) (concat pss) b"
  using wf
  by (induction pss arbitrary: b)
     (simp_all add: sides_of_program_side_rhs_fold_dg_char foldr_sup_acc)

lemma side_rhs_fold_dg_flat_cong:
  assumes eq: "set (concat pss) = set us"
    and wf: "\<forall>ps \<in> set pss. \<forall>p \<in> set ps. sp_wf p"
    and wf_all: "\<forall>p \<in> set (xs @ map (\<lambda>ps. side_rhs_fold_dg bot ps) pss @ zs). sp_wf p"
    and wf_us: "\<forall>p \<in> set (xs @ us @ zs). sp_wf p"
  shows
    "traverse_program (side_rhs_fold_dg acc
        (xs @ map (\<lambda>ps. side_rhs_fold_dg bot ps) pss @ zs)) \<tau>
       = traverse_program (side_rhs_fold_dg acc (xs @ us @ zs)) \<tau>"
    (is ?T)
    "sides_of_program (side_rhs_fold_dg acc
        (xs @ map (\<lambda>ps. side_rhs_fold_dg bot ps) pss @ zs)) \<tau> z
       = sides_of_program (side_rhs_fold_dg acc (xs @ us @ zs)) \<tau> z"
    (is ?S)
    "dep_program \<sigma> (side_rhs_fold_dg acc
        (xs @ map (\<lambda>ps. side_rhs_fold_dg bot ps) pss @ zs))
       = dep_program \<sigma> (side_rhs_fold_dg acc (xs @ us @ zs))"
    (is ?D)
proof -
  show ?T
    by (simp add: traverse_side_rhs_fold_dg[OF wf_all] traverse_side_rhs_fold_dg[OF wf_us]
          side_acc_dg_as_foldr foldr_sup_locals_map_fold[OF wf] foldr_sup_set_cong[OF eq])
next
  show ?S
    by (simp add: sides_of_program_side_rhs_fold_dg_char[OF wf_all]
          sides_of_program_side_rhs_fold_dg_char[OF wf_us]
          foldr_sup_sides_map_fold[OF wf] foldr_sup_set_cong[OF eq])
next
  show ?D
    using wf
    by (auto simp add: dep_program_side_rhs_fold_dg_char[OF wf_all]
          dep_program_side_rhs_fold_dg_char[OF wf_us]
          dep_program_side_rhs_fold_dg_char simp flip: eq)
qed

lemma side_rhs_fold_dg_sides_mono:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
    and prog_sides_mono:
      "\<forall>p \<in> set ps. \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> sides_of_program p s1 \<le> sides_of_program p s2"
  shows "\<And>acc s1 s2. s1 \<le> s2 \<Longrightarrow>
           sides_of_program (side_rhs_fold_dg acc ps) s1
             \<le> sides_of_program (side_rhs_fold_dg acc ps) s2"
  using prog_sides_mono
  unfolding side_rhs_fold_dg_def
  by (auto intro!: sides_of_program_fold_rhs_program_projected_mono[OF wf])

subsection \<open>Pushing a projection through a join-fold\<close>

text \<open>
  A \<^type>\<open>dg_state\<close> join is componentwise, so either projection commutes with
  a join-fold. These are what let a proof that has folded whole states read
  off one component afterwards, rather than carrying two folds along.
\<close>

lemma locals_foldr_generic:
  "locals (foldr (\<lambda>t acc'. h t \<squnion> acc') L
      (acc::('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state))
     = foldr (\<lambda>t acc'. locals (h t) \<squnion> acc') L (locals acc)"
  by (induction L) simp_all

lemma globs_foldr_generic:
  "globs (foldr (\<lambda>t acc'. h t \<squnion> acc') L
      (acc::('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state))
     = foldr (\<lambda>t acc'. globs (h t) \<squnion> acc') L (globs acc)"
  by (induction L) simp_all

lemma foldr_globs_sides_char:
  fixes L :: "('x, 'k, ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state,
                ('d, 'h) dg_state) strategy_program list"
  shows "foldr (\<lambda>t acc'. globs (sides_of_program t \<tau> z) \<squnion> acc') L bot
       = globs (foldr (\<lambda>t acc'. sides_of_program t \<tau> z \<squnion> acc') L bot)"
  by (simp add: globs_foldr_generic)

lemma foldr_sides_locals_bot:
  fixes L :: "('x, 'k, ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state,
                ('d, 'h) dg_state) strategy_program list"
  assumes "\<And>t. t \<in> set L \<Longrightarrow> locals (sides_of_program t \<tau> z) = bot"
  shows "locals (foldr (\<lambda>t acc'. sides_of_program t \<tau> z \<squnion> acc') L bot) = bot"
  using assms
  by (simp add: locals_foldr_generic foldr_sup_bot_of_all_bot)

lemma DG_sup_bot_left:
  "DG (bot::'d::bounded_semilattice_sup_bot) a \<squnion> DG bot b = DG bot (a \<squnion> b)"
  by (simp add: sup_dg_state_def bot_dg_state_def)

subsection \<open>What one folded program contributes\<close>

text \<open>
  Lower bounds, the counterpart of the upper bounds above: every folded program's
  answer and side contribution is below the fold's, and the accumulator only
  grows. A soundness proof reaches one selected contribution through these,
  having reached the fold itself through the generator.

  All three are the same fact about a join-fold --- \<open>foldr_sup_member_le\<close>,
  proved once with the rest of that algebra where the fold itself is defined
  --- read off the two characterizations above.
\<close>

lemma side_acc_dg_ge_acc:
  "acc \<le> side_acc_dg acc \<sigma> ts"
  by (simp add: side_acc_dg_as_foldr)

lemma locals_traverse_le_side_acc_dg:
  assumes "p \<in> set ps"
  shows "locals (traverse_program p \<sigma>) \<le> side_acc_dg acc \<sigma> ps"
  unfolding side_acc_dg_as_foldr
  using foldr_sup_member_le[where h = "\<lambda>p. locals (traverse_program p \<sigma>)", OF assms]
  by (rule le_supI2)

lemma sides_le_side_rhs_fold_dg:
  assumes wf: "\<forall>p \<in> set ps. sp_wf p"
    and mem: "p \<in> set ps"
  shows "sides_of_program p \<sigma> k \<le> sides_of_program (side_rhs_fold_dg acc ps) \<sigma> k"
  unfolding sides_of_program_side_rhs_fold_dg_char[OF wf]
  by (rule foldr_sup_member_le[OF mem])

end

end
