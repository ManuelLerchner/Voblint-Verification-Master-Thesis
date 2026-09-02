theory DG_Constraint_Trees
  imports DG_State
begin

section \<open>Turning a specification and a CFG edge into solver right-hand sides\<close>

text \<open>
  What the generator hands the solver. An edge or combine former takes its source
  as an address in the solver's own valuation space and its published slot as an
  explicit key, and produces a strategy program the solver can run: the tree
  reads what it needs, publishes what it must, and answers with a
  \<^type>\<open>dg_state\<close>. The formers only project and repack those two components,
  so their construction is independent of the concrete domains.

  \<^theory>\<open>Voblint_Framework.DG_State\<close> supplies the value type and its lattice;
  nothing here inspects a domain, a variable, or a global classifier.
\<close>

subsection \<open>Edge formers over a solution address\<close>

text \<open>
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

  \<^const>\<open>read_at\<close> itself (\<^theory>\<open>Voblint_Solver.Strategy_Tree_Combinators\<close>) is a
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
     do {
       d <- read_at src;
       g <- read_global gk;
       side_effect gk (DG bot (fst (step (locals d) (globs g))))
         (answer (DG (snd (step (locals d) (globs g))) bot))
     }"

definition dg_edge_contribution_tree_at ::
  "('dl::bounded_semilattice_sup_bot \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> 'x + 'k \<Rightarrow> 'k \<Rightarrow> ('x, 'k, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_edge_contribution_tree_at step src gk =
     do {
       d <- read_at src;
       g <- read_global gk;
       answer (DG (snd (step (locals d) (globs g))) (fst (step (locals d) (globs g))))
     }"

lemma traverse_dg_edge_tree_at:
  "traverse_rhs (dg_edge_tree_at step src gk) tau
   = DG (snd (step (locals (tau src)) (globs (tau (Inr gk))))) bot"
  unfolding dg_edge_tree_at_def by (cases src) simp_all

lemma sides_dg_edge_tree_at:
  "sides_of_rhs (dg_edge_tree_at step src gk) tau (Inr gk)
   = DG bot (fst (step (locals (tau src)) (globs (tau (Inr gk)))))"
  unfolding dg_edge_tree_at_def by (cases src) (simp_all add: Let_def)

lemma sides_dg_edge_tree_at_other:
  "k \<noteq> Inr gk \<Longrightarrow> sides_of_rhs (dg_edge_tree_at step src gk) tau k = bot"
  unfolding dg_edge_tree_at_def by (cases src) (simp_all add: Let_def)

lemma dep_aux_dg_edge_tree_at:
  "dep_aux tau (dg_edge_tree_at step src gk) = {src, Inr gk}"
  by (cases src) (simp_all add: dg_edge_tree_at_def)

lemma traverse_dg_edge_contribution_tree_at:
  "traverse_rhs (dg_edge_contribution_tree_at step src gk) tau
   = DG (snd (step (locals (tau src)) (globs (tau (Inr gk)))))
        (fst (step (locals (tau src)) (globs (tau (Inr gk)))))"
  unfolding dg_edge_contribution_tree_at_def by (cases src) simp_all

lemma sides_dg_edge_contribution_tree_at:
  "sides_of_rhs (dg_edge_contribution_tree_at step src gk) tau k = bot"
  unfolding dg_edge_contribution_tree_at_def
  by (cases src) (cases k; simp_all add: Let_def)+

lemma dep_aux_dg_edge_contribution_tree_at:
  "dep_aux tau (dg_edge_contribution_tree_at step src gk) = {src, Inr gk}"
  by (cases src) (simp_all add: dg_edge_contribution_tree_at_def)

subsection \<open>The heterogeneous framework edge shape\<close>

text \<open>
  Two independent opaque domains.  An analysis provides
  \<open>step : D \<Rightarrow> G \<Rightarrow> G \<times> D\<close> (transfer plus publication); the framework reads the
  local unknown's \<open>D\<close> and the global slot's \<open>G\<close>, and transports the step's
  \<open>Side : G\<close> and \<open>Answer : D\<close>.  Slot packing (\<open>DG _ bot\<close> / \<open>DG bot _\<close>) is the
  encoding of the two-typed unknown space into the solver's single value type;
  the framework never looks inside \<open>D\<close> or \<open>G\<close>.

  \<open>dg_edge_tree\<close> is the local-unknown specialization of
  \<^const>\<open>dg_edge_tree_at\<close>, fixing the source to \<^term>\<open>Inl u\<close> and the published
  slot to the \<^typ>\<open>unit\<close> key.
\<close>

definition dg_edge_tree ::
  "('dl::bounded_semilattice_sup_bot \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_edge_tree step u = dg_edge_tree_at step (Inl u) ()"

lemma dg_edge_tree_as_at:
  "dg_edge_tree step u = dg_edge_tree_at step (Inl u) ()"
  by (simp add: dg_edge_tree_def)

lemma traverse_dg_edge_tree:
  "traverse_rhs (dg_edge_tree step u) \<tau>
   = DG (snd (step (locals (\<tau> (Inl u))) (globs (\<tau> (Inr ()))))) bot"
  by (simp add: dg_edge_tree_def traverse_dg_edge_tree_at)

lemma sides_dg_edge_tree_Inr:
  "sides_of_rhs (dg_edge_tree step u) \<tau> (Inr ())
   = DG bot (fst (step (locals (\<tau> (Inl u))) (globs (\<tau> (Inr ())))))"
  by (simp add: dg_edge_tree_def sides_dg_edge_tree_at)

lemma sides_dg_edge_tree_Inl:
  "sides_of_rhs (dg_edge_tree step u) \<tau> (Inl v) = bot"
  by (simp add: dg_edge_tree_def sides_dg_edge_tree_at_other)

lemma dep_aux_dg_edge_tree:
  "dep_aux \<tau> (dg_edge_tree step u) = {Inl u, Inr ()}"
  by (simp add: dg_edge_tree_def dep_aux_dg_edge_tree_at)

text \<open>
  The framework boundary as theorems, for \<^emph>\<open>every\<close> analysis step and every
  assignment: Answers carry no \<open>G\<close>, Side publications carry no \<open>D\<close>.
\<close>

theorem dg_edge_tree_answer_pure_D:
  "globs (traverse_rhs (dg_edge_tree step u) \<tau>) = bot"
  by (simp add: traverse_dg_edge_tree)

theorem dg_edge_tree_side_pure_G:
  "locals (sides_of_rhs (dg_edge_tree step u) \<tau> (Inr ())) = bot"
  by (simp add: sides_dg_edge_tree_Inr)

subsection \<open>Side-free edge contribution, for buffered keyed generation\<close>

text \<open>
  \<open>dg_edge_tree\<close> publishes its \<open>G\<close> contribution as soon as it is evaluated
  (\<^const>\<open>side_effect\<close>). When \<open>side_cfg_T_eff_keyed_seed_dg\<close> (below) folds several such
  trees into one equation's RHS (several intra predecessors, or several return sites),
  each one's \<open>Side\<close> is published at a different moment within the same RHS evaluation:
  the vendored solver's warrowing/APINIS update rule gates convergence per \<^emph>\<open>origin\<close>, so
  repeated writes to the same key from the same origin can destabilize the equation's own
  dependency and never converge.

  \<open>dg_edge_contribution_tree\<close> is the Side-free analogue -- the local-unknown
  specialization of \<^const>\<open>dg_edge_contribution_tree_at\<close> -- it answers the
  \<^emph>\<open>unsplit\<close> \<open>(G, D)\<close> result as one \<open>dg_state\<close>, publishing nothing. A caller
  folds several contribution trees with \<^const>\<open>fold_rhs_trees\<close> (whose own
  \<^const>\<open>Side\<close> is empty, so no intermediate publication happens) and splits the
  aggregate once, after every contribution has been read -- reproducing
  \<^const>\<open>dg_edge_tree\<close>'s declarative \<^const>\<open>traverse_rhs\<close>/\<^const>\<open>sides_of_rhs\<close>
  value while emitting at most one \<open>Side\<close> per key per RHS evaluation.
\<close>

definition dg_edge_contribution_tree ::
  "('dl::bounded_semilattice_sup_bot \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_edge_contribution_tree step u = dg_edge_contribution_tree_at step (Inl u) ()"

lemma dg_edge_contribution_tree_as_at:
  "dg_edge_contribution_tree step u = dg_edge_contribution_tree_at step (Inl u) ()"
  by (simp add: dg_edge_contribution_tree_def)

lemma traverse_dg_edge_contribution_tree:
  "traverse_rhs (dg_edge_contribution_tree step u) \<tau>
   = DG (snd (step (locals (\<tau> (Inl u))) (globs (\<tau> (Inr ())))))
        (fst (step (locals (\<tau> (Inl u))) (globs (\<tau> (Inr ())))))"
  by (simp add: dg_edge_contribution_tree_def traverse_dg_edge_contribution_tree_at)

lemma sides_dg_edge_contribution_tree:
  "sides_of_rhs (dg_edge_contribution_tree step u) \<tau> k = bot"
  by (simp add: dg_edge_contribution_tree_def sides_dg_edge_contribution_tree_at)

lemma dep_aux_dg_edge_contribution_tree:
  "dep_aux \<tau> (dg_edge_contribution_tree step u) = {Inl u, Inr ()}"
  by (simp add: dg_edge_contribution_tree_def dep_aux_dg_edge_contribution_tree_at)

lemma dg_edge_contribution_tree_matches_local:
  "locals (traverse_rhs (dg_edge_contribution_tree step u) \<tau>)
     = locals (traverse_rhs (dg_edge_tree step u) \<tau>)"
  by (simp add: traverse_dg_edge_contribution_tree traverse_dg_edge_tree)

lemma dg_edge_contribution_tree_matches_global:
  "globs (traverse_rhs (dg_edge_contribution_tree step u) \<tau>)
     = globs (sides_of_rhs (dg_edge_tree step u) \<tau> (Inr ()))"
  by (simp add: traverse_dg_edge_contribution_tree sides_dg_edge_tree_Inr)

text \<open>
  Combine formers mirror the edge formers above: the address-parametric form
  is primary, taking each source as a solver address rather than fixing it to
  a local unknown, and reads two \<open>D\<close> inputs (caller, callee exit) plus one
  \<open>G\<close> instead of one \<open>D\<close>.
\<close>

definition dg_combine_tree_at ::
  "(call_info \<Rightarrow> 'dl::bounded_semilattice_sup_bot \<Rightarrow> 'dl \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> call_info \<Rightarrow> 'x + 'k \<Rightarrow> 'x + 'k \<Rightarrow> 'k \<Rightarrow> ('x, 'k, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_combine_tree_at comb ci src_cc src_ex gk =
     do {
       dc <- read_at src_cc;
       de <- read_at src_ex;
       g <- read_global gk;
       side_effect gk (DG bot (fst (comb ci (locals dc) (locals de) (globs g))))
         (answer (DG (snd (comb ci (locals dc) (locals de) (globs g))) bot))
     }"

lemma traverse_dg_combine_tree_at:
  "traverse_rhs (dg_combine_tree_at comb ci src_cc src_ex gk) tau
   = DG (snd (comb ci (locals (tau src_cc)) (locals (tau src_ex)) (globs (tau (Inr gk))))) bot"
  unfolding dg_combine_tree_at_def by (cases src_cc; cases src_ex) simp_all

lemma sides_dg_combine_tree_at:
  "sides_of_rhs (dg_combine_tree_at comb ci src_cc src_ex gk) tau (Inr gk)
   = DG bot (fst (comb ci (locals (tau src_cc)) (locals (tau src_ex)) (globs (tau (Inr gk)))))"
  unfolding dg_combine_tree_at_def by (cases src_cc; cases src_ex) (simp_all add: Let_def)

lemma sides_dg_combine_tree_at_other:
  "k \<noteq> Inr gk \<Longrightarrow> sides_of_rhs (dg_combine_tree_at comb ci src_cc src_ex gk) tau k = bot"
  unfolding dg_combine_tree_at_def by (cases src_cc; cases src_ex) (simp_all add: Let_def)

lemma dep_aux_dg_combine_tree_at:
  "dep_aux tau (dg_combine_tree_at comb ci src_cc src_ex gk) = {src_cc, src_ex, Inr gk}"
  by (cases src_cc; cases src_ex) (simp_all add: dg_combine_tree_at_def)

text \<open>Procedure-return combine: \<open>dg_combine_tree\<close> is the local-unknown
  specialization of \<^const>\<open>dg_combine_tree_at\<close>, fixing the caller and
  callee-exit sources to \<^term>\<open>Inl cc\<close>/\<^term>\<open>Inl ex\<close> and the published slot to
  the \<^typ>\<open>unit\<close> key.\<close>

definition dg_combine_tree ::
  "(call_info \<Rightarrow> 'dl::bounded_semilattice_sup_bot \<Rightarrow> 'dl \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> call_info \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_combine_tree comb ci cc ex = dg_combine_tree_at comb ci (Inl cc) (Inl ex) ()"

lemma dg_combine_tree_as_at:
  "dg_combine_tree comb ci cc ex = dg_combine_tree_at comb ci (Inl cc) (Inl ex) ()"
  by (simp add: dg_combine_tree_def)

lemma traverse_dg_combine_tree:
  "traverse_rhs (dg_combine_tree comb dst cc ex) \<tau>
   = DG (snd (comb dst (locals (\<tau> (Inl cc))) (locals (\<tau> (Inl ex))) (globs (\<tau> (Inr ()))))) bot"
  by (simp add: dg_combine_tree_def traverse_dg_combine_tree_at)

lemma sides_dg_combine_tree_Inr:
  "sides_of_rhs (dg_combine_tree comb dst cc ex) \<tau> (Inr ())
   = DG bot (fst (comb dst (locals (\<tau> (Inl cc))) (locals (\<tau> (Inl ex))) (globs (\<tau> (Inr ())))))"
  by (simp add: dg_combine_tree_def sides_dg_combine_tree_at)

lemma sides_dg_combine_tree_Inl:
  "sides_of_rhs (dg_combine_tree comb dst cc ex) \<tau> (Inl v) = bot"
  by (simp add: dg_combine_tree_def sides_dg_combine_tree_at_other)

lemma dep_aux_dg_combine_tree:
  "dep_aux \<tau> (dg_combine_tree comb dst cc ex) = {Inl cc, Inl ex, Inr ()}"
  by (simp add: dg_combine_tree_def dep_aux_dg_combine_tree_at)

subsection \<open>Monotonicity and static dependencies of the edge and combine tree shapes\<close>

text \<open>
  Both tree shapes above have a query structure --- \<open>u\<close>/\<open>()\<close> for the edge
  tree, \<open>cc\<close>/\<open>ex\<close>/\<open>()\<close> for the combine tree --- fixed independently of any
  environment value, so their dependency sets are trivially static: no
  analysis-supplied fact is needed. A jointly monotone \<open>step\<close>/\<open>comb\<close> lifts
  to a monotone tree the same way, independent of any particular domain
  --- an analysis only has to prove its own transfer/combine functions
  monotone, never re-derive tree monotonicity.
\<close>

lemma env_indep_deps_dg_edge_tree: "env_indep_deps (dg_edge_tree step u)"
  by (rule env_indep_depsI) (simp add: dep_aux_dg_edge_tree)

lemma env_indep_deps_dg_combine_tree: "env_indep_deps (dg_combine_tree comb dst cc ex)"
  by (rule env_indep_depsI) (simp add: dep_aux_dg_combine_tree)

lemma dg_edge_tree_mono:
  assumes step_mono_snd:
    "\<And>d1 d2 g1 g2. d1 \<le> d2 \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> snd (step d1 g1) \<le> snd (step d2 g2)"
    and le: "\<tau>1 \<le> \<tau>2"
  shows "traverse_rhs (dg_edge_tree step u) \<tau>1 \<le> traverse_rhs (dg_edge_tree step u) \<tau>2"
proof -
  have dl: "locals (\<tau>1 (Inl u)) \<le> locals (\<tau>2 (Inl u))"
    using le[THEN le_funD, of "Inl u"] by (simp add: less_eq_dg_state_def)
  have dgv: "globs (\<tau>1 (Inr ())) \<le> globs (\<tau>2 (Inr ()))"
    using le[THEN le_funD, of "Inr ()"] by (simp add: less_eq_dg_state_def)
  show ?thesis
    unfolding traverse_dg_edge_tree less_eq_dg_state_def
    using step_mono_snd[OF dl dgv] by simp
qed

lemma dg_edge_tree_sides_mono:
  assumes step_mono_fst:
    "\<And>d1 d2 g1 g2. d1 \<le> d2 \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> fst (step d1 g1) \<le> fst (step d2 g2)"
    and le: "\<tau>1 \<le> \<tau>2"
  shows "sides_of_rhs (dg_edge_tree step u) \<tau>1 \<le> sides_of_rhs (dg_edge_tree step u) \<tau>2"
proof (rule le_funI)
  fix k
  have dl: "locals (\<tau>1 (Inl u)) \<le> locals (\<tau>2 (Inl u))"
    using le[THEN le_funD, of "Inl u"] by (simp add: less_eq_dg_state_def)
  have dgv: "globs (\<tau>1 (Inr ())) \<le> globs (\<tau>2 (Inr ()))"
    using le[THEN le_funD, of "Inr ()"] by (simp add: less_eq_dg_state_def)
  show "sides_of_rhs (dg_edge_tree step u) \<tau>1 k \<le> sides_of_rhs (dg_edge_tree step u) \<tau>2 k"
    by (cases k) (simp_all add: sides_dg_edge_tree_Inl sides_dg_edge_tree_Inr
                                 less_eq_dg_state_def step_mono_fst[OF dl dgv])
qed

lemma dg_combine_tree_mono:
  assumes comb_mono_snd:
    "\<And>dc1 dc2 de1 de2 g1 g2. dc1 \<le> dc2 \<Longrightarrow> de1 \<le> de2 \<Longrightarrow> g1 \<le> g2
       \<Longrightarrow> snd (comb dst dc1 de1 g1) \<le> snd (comb dst dc2 de2 g2)"
    and le: "\<tau>1 \<le> \<tau>2"
  shows "traverse_rhs (dg_combine_tree comb dst cc ex) \<tau>1
           \<le> traverse_rhs (dg_combine_tree comb dst cc ex) \<tau>2"
proof -
  have dc: "locals (\<tau>1 (Inl cc)) \<le> locals (\<tau>2 (Inl cc))"
    using le[THEN le_funD, of "Inl cc"] by (simp add: less_eq_dg_state_def)
  have de: "locals (\<tau>1 (Inl ex)) \<le> locals (\<tau>2 (Inl ex))"
    using le[THEN le_funD, of "Inl ex"] by (simp add: less_eq_dg_state_def)
  have dgv: "globs (\<tau>1 (Inr ())) \<le> globs (\<tau>2 (Inr ()))"
    using le[THEN le_funD, of "Inr ()"] by (simp add: less_eq_dg_state_def)
  show ?thesis
    unfolding traverse_dg_combine_tree less_eq_dg_state_def
    using comb_mono_snd[OF dc de dgv] by simp
qed

lemma dg_combine_tree_sides_mono:
  assumes comb_mono_fst:
    "\<And>dc1 dc2 de1 de2 g1 g2. dc1 \<le> dc2 \<Longrightarrow> de1 \<le> de2 \<Longrightarrow> g1 \<le> g2
       \<Longrightarrow> fst (comb dst dc1 de1 g1) \<le> fst (comb dst dc2 de2 g2)"
    and le: "\<tau>1 \<le> \<tau>2"
  shows "sides_of_rhs (dg_combine_tree comb dst cc ex) \<tau>1
           \<le> sides_of_rhs (dg_combine_tree comb dst cc ex) \<tau>2"
proof (rule le_funI)
  fix k
  have dc: "locals (\<tau>1 (Inl cc)) \<le> locals (\<tau>2 (Inl cc))"
    using le[THEN le_funD, of "Inl cc"] by (simp add: less_eq_dg_state_def)
  have de: "locals (\<tau>1 (Inl ex)) \<le> locals (\<tau>2 (Inl ex))"
    using le[THEN le_funD, of "Inl ex"] by (simp add: less_eq_dg_state_def)
  have dgv: "globs (\<tau>1 (Inr ())) \<le> globs (\<tau>2 (Inr ()))"
    using le[THEN le_funD, of "Inr ()"] by (simp add: less_eq_dg_state_def)
  show "sides_of_rhs (dg_combine_tree comb dst cc ex) \<tau>1 k
          \<le> sides_of_rhs (dg_combine_tree comb dst cc ex) \<tau>2 k"
    by (cases k) (simp_all add: sides_dg_combine_tree_Inl sides_dg_combine_tree_Inr
                                 less_eq_dg_state_def comb_mono_fst[OF dc de dgv])
qed


subsection \<open>Folding a list of trees into one D/G value\<close>

fun side_rhs_fold_dg ::
  "'d::bounded_semilattice_sup_bot
   \<Rightarrow> ('x, 'g, ('d, 'h::bounded_semilattice_sup_bot) dg_state) strategy_tree list
   \<Rightarrow> ('x, 'g, ('d, 'h) dg_state) strategy_tree"
where
  "side_rhs_fold_dg acc [] = Answer (DG acc bot)"
| "side_rhs_fold_dg acc (t # ts) =
     t \<bind> (\<lambda>res. side_rhs_fold_dg (acc \<squnion> locals res) ts)"

fun side_acc_dg ::
  "'d::bounded_semilattice_sup_bot
   \<Rightarrow> ('x + 'g \<Rightarrow> ('d, 'h::bounded_semilattice_sup_bot) dg_state)
   \<Rightarrow> ('x, 'g, ('d, 'h) dg_state) strategy_tree list \<Rightarrow> 'd"
where
  "side_acc_dg acc \<tau> [] = acc"
| "side_acc_dg acc \<tau> (t # ts) =
     side_acc_dg (acc \<squnion> locals (traverse_rhs t \<tau>)) \<tau> ts"

lemma traverse_side_rhs_fold_dg:
  "traverse_rhs (side_rhs_fold_dg acc ts) \<tau> =
   DG (side_acc_dg acc \<tau> ts) bot"
  by (induction ts arbitrary: acc) (simp_all add: traverse_seqcomp)

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
   \<Longrightarrow> traverse_rhs (side_rhs_fold_dg acc1 ts) sigma \<le> traverse_rhs (side_rhs_fold_dg acc2 ts) sigma"
proof (induction ts arbitrary: acc1 acc2)
  case Nil
  then show ?case by (simp add: less_eq_dg_state_def)
next
  case (Cons t ts)
  from Cons.prems have "acc1 \<squnion> locals (traverse_rhs t sigma) \<le> acc2 \<squnion> locals (traverse_rhs t sigma)"
    by (rule sup_mono[OF _ order_refl])
  then show ?case
    using Cons.IH by (simp add: traverse_seqcomp)
qed

lemma dep_aux_side_rhs_fold_dg_acc_indep:
  "dep_aux sigma (side_rhs_fold_dg acc1 ts) = dep_aux sigma (side_rhs_fold_dg acc2 ts)"
proof (induction ts arbitrary: acc1 acc2)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  show ?case
    using Cons.IH[of "acc1 \<squnion> locals (traverse_rhs t sigma)" "acc2 \<squnion> locals (traverse_rhs t sigma)"]
    by (simp add: dep_aux_seqcomp)
qed

lemma dep_aux_side_rhs_fold_dg_char:
  "dep_aux sigma (side_rhs_fold_dg acc ts) = (\<Union>t\<in>set ts. dep_aux sigma t)"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have "dep_aux sigma (side_rhs_fold_dg acc (t # ts))
          = dep_aux sigma t \<union> dep_aux sigma (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t sigma)) ts)"
    by (simp add: dep_aux_seqcomp)
  also have "dep_aux sigma (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t sigma)) ts)
               = dep_aux sigma (side_rhs_fold_dg acc ts)"
    by (rule dep_aux_side_rhs_fold_dg_acc_indep)
  also have "\<dots> = (\<Union>t\<in>set ts. dep_aux sigma t)"
    by (rule Cons.IH)
  finally show ?case by simp
qed

lemma side_rhs_fold_dg_val_mono:
  "v1 \<le> v2
   \<Longrightarrow> traverse_rhs (side_rhs_fold_dg (acc \<squnion> locals v1) ts) sigma
         \<le> traverse_rhs (side_rhs_fold_dg (acc \<squnion> locals v2) ts) sigma"
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
  tail, so the only per-tree work @{thm seqcomp_mono} leaves is \<open>t_mono\<close>
  itself, supplied by the assumption.
\<close>

lemma side_rhs_fold_dg_mono:
  assumes tree_mono: "\<forall>t \<in> set ts. \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> traverse_rhs t s1 \<le> traverse_rhs t s2"
  shows "\<And>acc s1 s2. s1 \<le> s2 \<Longrightarrow>
           traverse_rhs (side_rhs_fold_dg acc ts) s1 \<le> traverse_rhs (side_rhs_fold_dg acc ts) s2"
using tree_mono proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have tail_mono: "\<forall>t' \<in> set ts. \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> traverse_rhs t' s1 \<le> traverse_rhs t' s2"
    using Cons.prems by simp
  note IH = Cons.IH[OF _ tail_mono]
  fix acc s1 s2
  show "s1 \<le> s2 \<Longrightarrow> traverse_rhs (side_rhs_fold_dg acc (t # ts)) s1
          \<le> traverse_rhs (side_rhs_fold_dg acc (t # ts)) s2"
  proof -
    assume le: "s1 \<le> s2"
    have t_mono: "\<And>s1 s2. s1 \<le> s2 \<Longrightarrow> traverse_rhs t s1 \<le> traverse_rhs t s2"
      using Cons.prems by simp
    have k_mono_env: "\<And>v s1 s2. s1 \<le> s2 \<Longrightarrow>
        traverse_rhs (side_rhs_fold_dg (acc \<squnion> locals v) ts) s1
          \<le> traverse_rhs (side_rhs_fold_dg (acc \<squnion> locals v) ts) s2"
      using IH by blast
    have k_mono_val: "\<And>s v1 v2. v1 \<le> v2 \<Longrightarrow>
        traverse_rhs (side_rhs_fold_dg (acc \<squnion> locals v1) ts) s
          \<le> traverse_rhs (side_rhs_fold_dg (acc \<squnion> locals v2) ts) s"
      by (rule side_rhs_fold_dg_val_mono)
    show "traverse_rhs (side_rhs_fold_dg acc (t # ts)) s1
            \<le> traverse_rhs (side_rhs_fold_dg acc (t # ts)) s2"
      using seqcomp_mono[OF t_mono k_mono_env k_mono_val le] by simp
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
  shows "env_indep_deps (side_rhs_fold_dg acc ts)"
  unfolding env_indep_deps_def
proof (intro allI)
  fix sigma1 sigma2
  show "dep_aux sigma1 (side_rhs_fold_dg acc ts) = dep_aux sigma2 (side_rhs_fold_dg acc ts)"
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
    have "dep_aux sigma1 (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t sigma1)) ts)
            = dep_aux sigma1 (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t sigma2)) ts)"
      by (rule dep_aux_side_rhs_fold_dg_acc_indep)
    also have "\<dots> = dep_aux sigma2 (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t sigma2)) ts)"
      using Cons.IH[OF tail_static] by simp
    finally show ?case
      by (simp add: dep_aux_seqcomp t_static)
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
  shows "mono_tree_deps (side_rhs_fold_dg acc ts)"
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
  "sides_of_rhs (side_rhs_fold_dg acc1 ts) sigma = sides_of_rhs (side_rhs_fold_dg acc2 ts) sigma"
proof (induction ts arbitrary: acc1 acc2)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  show ?case
    using Cons.IH[of "acc1 \<squnion> locals (traverse_rhs t sigma)" "acc2 \<squnion> locals (traverse_rhs t sigma)"]
    by (simp add: sides_of_rhs_seqcomp)
qed

text \<open>
  The declarative twin of \<^const>\<open>side_acc_dg\<close>: \<open>side_rhs_fold_dg\<close>'s side contribution
  at any one key is a plain fold over each element's own \<^const>\<open>sides_of_rhs\<close>, seeded at
  \<open>bot\<close> rather than the running local accumulator -- @{thm
  sides_of_rhs_side_rhs_fold_dg_acc_indep} already shows the accumulator never affects a
  side read, so unfolding \<^const>\<open>seqcomp_tree\<close>'s side equation and re-seeding at \<open>bot\<close>
  after each step is exact, not merely a bound.
\<close>

lemma sides_of_rhs_side_rhs_fold_dg_char:
  fixes ts :: "('x, 'k, ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state)
                 strategy_tree list"
  shows "sides_of_rhs (side_rhs_fold_dg acc ts) \<tau> z = foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') ts bot"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have "sides_of_rhs (side_rhs_fold_dg acc (t # ts)) \<tau> z
          = sides_of_rhs t \<tau> z \<squnion> sides_of_rhs (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t \<tau>)) ts) \<tau> z"
    by simp
  also have "sides_of_rhs (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t \<tau>)) ts) \<tau> z
               = sides_of_rhs (side_rhs_fold_dg acc ts) \<tau> z"
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
  "foldr (\<lambda>t a. locals (traverse_rhs t \<tau>) \<squnion> a) (map (side_rhs_fold_dg bot) tss) b
     = foldr (\<lambda>t a. locals (traverse_rhs t \<tau>) \<squnion> a) (concat tss) b"
  by (induction tss arbitrary: b)
     (simp_all add: traverse_side_rhs_fold_dg side_acc_dg_as_foldr foldr_sup_acc)

lemma foldr_sup_sides_map_fold:
  "foldr (\<lambda>t a. sides_of_rhs t \<tau> z \<squnion> a) (map (side_rhs_fold_dg bot) tss) b
     = foldr (\<lambda>t a. sides_of_rhs t \<tau> z \<squnion> a) (concat tss) b"
  by (induction tss arbitrary: b)
     (simp_all add: sides_of_rhs_side_rhs_fold_dg_char foldr_sup_acc)

lemma side_rhs_fold_dg_flat_cong:
  assumes eq: "set (concat tss) = set us"
  shows
    "traverse_rhs (side_rhs_fold_dg acc (xs @ map (side_rhs_fold_dg bot) tss @ zs)) \<tau>
       = traverse_rhs (side_rhs_fold_dg acc (xs @ us @ zs)) \<tau>"
    "sides_of_rhs (side_rhs_fold_dg acc (xs @ map (side_rhs_fold_dg bot) tss @ zs)) \<tau> z
       = sides_of_rhs (side_rhs_fold_dg acc (xs @ us @ zs)) \<tau> z"
    "dep_aux \<sigma> (side_rhs_fold_dg acc (xs @ map (side_rhs_fold_dg bot) tss @ zs))
       = dep_aux \<sigma> (side_rhs_fold_dg acc (xs @ us @ zs))"
proof -
  show "traverse_rhs (side_rhs_fold_dg acc (xs @ map (side_rhs_fold_dg bot) tss @ zs)) \<tau>
          = traverse_rhs (side_rhs_fold_dg acc (xs @ us @ zs)) \<tau>"
    by (simp add: traverse_side_rhs_fold_dg side_acc_dg_as_foldr
          foldr_sup_locals_map_fold foldr_sup_set_cong[OF eq])
next
  show "sides_of_rhs (side_rhs_fold_dg acc (xs @ map (side_rhs_fold_dg bot) tss @ zs)) \<tau> z
          = sides_of_rhs (side_rhs_fold_dg acc (xs @ us @ zs)) \<tau> z"
    by (simp add: sides_of_rhs_side_rhs_fold_dg_char
          foldr_sup_sides_map_fold foldr_sup_set_cong[OF eq])
next
  show "dep_aux \<sigma> (side_rhs_fold_dg acc (xs @ map (side_rhs_fold_dg bot) tss @ zs))
          = dep_aux \<sigma> (side_rhs_fold_dg acc (xs @ us @ zs))"
    by (auto simp add: dep_aux_side_rhs_fold_dg_char simp flip: eq)
qed

lemma side_rhs_fold_dg_sides_mono:
  assumes tree_sides_mono: "\<forall>t \<in> set ts. \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> sides_of_rhs t s1 \<le> sides_of_rhs t s2"
  shows "\<And>acc s1 s2. s1 \<le> s2 \<Longrightarrow>
           sides_of_rhs (side_rhs_fold_dg acc ts) s1 \<le> sides_of_rhs (side_rhs_fold_dg acc ts) s2"
using tree_sides_mono proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have tail_sides_mono: "\<forall>t' \<in> set ts. \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> sides_of_rhs t' s1 \<le> sides_of_rhs t' s2"
    using Cons.prems by simp
  note IH = Cons.IH[OF _ tail_sides_mono]
  fix acc s1 s2
  show "s1 \<le> s2 \<Longrightarrow> sides_of_rhs (side_rhs_fold_dg acc (t # ts)) s1
          \<le> sides_of_rhs (side_rhs_fold_dg acc (t # ts)) s2"
  proof -
    assume le: "s1 \<le> s2"
    have t_sides_mono: "sides_of_rhs t s1 \<le> sides_of_rhs t s2"
      using Cons.prems le by simp
    have tail_mono: "sides_of_rhs (side_rhs_fold_dg acc ts) s1
                        \<le> sides_of_rhs (side_rhs_fold_dg acc ts) s2"
      using IH le by blast
    have i1: "sides_of_rhs (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t s1)) ts) s1
                = sides_of_rhs (side_rhs_fold_dg acc ts) s1"
      by (rule sides_of_rhs_side_rhs_fold_dg_acc_indep)
    have i2: "sides_of_rhs (side_rhs_fold_dg (acc \<squnion> locals (traverse_rhs t s2)) ts) s2
                = sides_of_rhs (side_rhs_fold_dg acc ts) s2"
      by (rule sides_of_rhs_side_rhs_fold_dg_acc_indep)
    show "sides_of_rhs (side_rhs_fold_dg acc (t # ts)) s1
            \<le> sides_of_rhs (side_rhs_fold_dg acc (t # ts)) s2"
      using sup_mono[OF t_sides_mono tail_mono] by (simp add: sides_of_rhs_seqcomp i1 i2)
  qed
qed

end
