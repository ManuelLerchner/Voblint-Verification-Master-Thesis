theory DG_Framework
  imports State_Restriction Exec_Placement Solver_Mono Side_Buffering
    Strategy_Tree_Rhs Strategy_Tree_Relabel Strategy_Tree_Combinators
    "Voblint_CFG.CFG_Transfer"
begin

section \<open>The D/G framework core\<close>

text \<open>An analysis chooses a flow-sensitive answer domain \<open>D\<close> and a
  flow-insensitive side-effect domain \<open>G\<close>. The framework keeps them opaque and stores
  them in separate components of \<open>dg_state\<close>; it never copies a global component
  into a local answer.

  \<open>dg_edge_tree\<close> and \<open>dg_combine_tree\<close> only project and repack those
  components, so their construction is independent of the concrete domains.\<close>



definition unit_step_for ::
  "(vname => bool) =>
   ('a::bounded_semilattice_sup_bot abs_state => 'a abs_state)
   => 'a abs_state => 'a abs_state => 'a abs_state \<times> 'a abs_state"
where
  "unit_step_for gs f d g =
     (let res = f (combine_env_abs gs d g) in
      (restrict_global_for gs res, restrict_local_for gs res))"

subsection \<open>A structural-reachability unary step, staged ahead of \<^const>\<open>unit_step_for\<close>'s own migration (issue #123)\<close>

text \<open>
  \<^const>\<open>unit_step_for\<close> reconstructs a complete state, applies the raw transfer, and splits
  -- with no notion of an unreachable input or a semantically-bottom result. This is the DG
  analogue of the gap \<^theory>\<open>Voblint_Core.State_Restriction\<close>'s \<^const>\<open>res_edge\<close> closes
  for a single reassembled environment. \<^const>\<open>assemble_local_global\<close> itself is not the right reconstruction
  primitive here: its \<open>Lifted d, Lifted g\<close> case joins with \<open>\<squnion>\<close>, but \<^const>\<open>unit_step_for\<close>
  reconstructs with \<^const>\<open>combine_env_abs\<close>, a per-variable selector (\<open>\<lambda>x. if gs x then g x
  else d x\<close>), not a join. \<open>assemble_env_abs\<close> below keeps \<^const>\<open>assemble_local_global\<close>'s
  reachability rule (local \<^const>\<open>Bot\<close> dominates, global \<^const>\<open>Bot\<close> is neutral) while
  reconstructing content the way \<^const>\<open>unit_step_for\<close> actually does. Staged standalone ahead
  of \<^const>\<open>unit_step_for\<close>'s own retyping so the reachability discipline is proved once, in
  isolation, before the wider carrier migration propagates through its callers.
\<close>

text \<open>
  No separate \<open>g = Bot\<close> shortcut clause: \<^const>\<open>combine_env_abs\<close>'s neutral element at an
  unpublished global is \<open>bot\<close>, not an unconditional identity on \<open>d\<close> -- \<open>combine_env_abs gs d
  bot = d\<close> only when \<open>d\<close> is already \<open>gs\<close>-local-canonical (\<open>restrict_local_for gs d = d\<close>),
  which \<^const>\<open>restrict_local_for\<close>'s own definition (\<open>\<lambda>x. if gs x then bot else \<sigma> x\<close>) shows
  equals \<open>combine_env_abs gs d bot\<close> unconditionally. Always routing through \<^const>\<open>combine_env_abs\<close>
  keeps this function correct for every \<open>d\<close>, canonical or not, rather than silently assuming
  canonicality.
\<close>

fun assemble_env_abs ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state lifted
   => 'a abs_state lifted => 'a abs_state lifted"
where
  "assemble_env_abs gs Bot g = Bot"
| "assemble_env_abs gs (Lifted d) g =
     Lifted (combine_env_abs gs d (case g of Bot \<Rightarrow> bot | Lifted g0 \<Rightarrow> g0))"

definition unit_step_for_lifted ::
  "(vname => bool)
   => ('a::bounded_semilattice_sup_bot abs_state => bool)
   => ('a abs_state => 'a abs_state)
   => 'a abs_state lifted => 'a abs_state lifted
   => 'a abs_state lifted \<times> 'a abs_state lifted"
where
  "unit_step_for_lifted gs is_bot_pred f d g =
     (let res = transfer_lift is_bot_pred f (assemble_env_abs gs d g)
      in (map_lift (restrict_global_for gs) res, map_lift (restrict_local_for gs) res))"

lemma unit_step_for_lifted_Bot_dominates_local [simp]:
  "unit_step_for_lifted gs is_bot_pred f Bot g = (Bot, Bot)"
  unfolding unit_step_for_lifted_def by simp

lemma unit_step_for_lifted_global_bot:
  "unit_step_for_lifted gs is_bot_pred f (Lifted d) Bot =
     (let res = transfer_lift is_bot_pred f (Lifted (combine_env_abs gs d bot))
      in (map_lift (restrict_global_for gs) res, map_lift (restrict_local_for gs) res))"
  unfolding unit_step_for_lifted_def by simp

lemma unit_step_for_lifted_agrees:
  assumes "\<not> is_bot_pred (f (combine_env_abs gs d g))"
  shows "unit_step_for_lifted gs is_bot_pred f (Lifted d) (Lifted g) =
           (Lifted (fst (unit_step_for gs f d g)), Lifted (snd (unit_step_for gs f d g)))"
  using assms
  unfolding unit_step_for_lifted_def unit_step_for_def
  by (simp add: Let_def)

lemma unit_step_for_lifted_collapses_bot:
  assumes "is_bot_pred (f (combine_env_abs gs d g))"
  shows "unit_step_for_lifted gs is_bot_pred f (Lifted d) (Lifted g) = (Bot, Bot)"
  using assms
  unfolding unit_step_for_lifted_def
  by simp



definition unit_step_placed ::
  "(vname => bool) => (vname => bool) =>
   ('a::bounded_semilattice_sup_bot abs_state => 'a abs_state)
   => 'a abs_state => 'a abs_state => 'a abs_state \<times> 'a abs_state"
where
  "unit_step_placed keep_local publish_side f d g =
     (let res = f (d \<squnion> g) in
      (project_component publish_side res, project_component keep_local res))"



subsection \<open>A lattice copy type for D-times-G unknown values\<close>

text \<open>
  The solver's single value type must order local and global halves
  componentwise.  Raw pairs cannot: \<open>CFG_Def\<close> imports
  \<open>HOL-Library.Product_Lexorder\<close>, so \<open>'l \<times> 'g\<close> already carries the
  lexicographic order everywhere in this repository, and the componentwise
  \<open>HOL-Library.Product_Order\<close> instances clash with it.  \<open>dg_state\<close> is the
  componentwise-ordered copy of \<^typ>\<open>('l, 'g) split_state\<close>.
\<close>

datatype ('l, 'g) dg_state = DG (locals: 'l) (globs: 'g)

instantiation dg_state :: (ord, ord) ord
begin

definition less_eq_dg_state :: "('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> bool" where
  "less_eq_dg_state d1 d2 = (locals d1 \<le> locals d2 \<and> globs d1 \<le> globs d2)"

definition less_dg_state :: "('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> bool" where
  "less_dg_state d1 d2 = (d1 \<le> d2 \<and> \<not> d2 \<le> d1)"

instance ..

end

instance dg_state :: (order, order) order
proof intro_classes
  fix x y z :: "('a, 'b) dg_state"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by (simp add: less_dg_state_def)
  show "x \<le> x" by (simp add: less_eq_dg_state_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (auto simp: less_eq_dg_state_def intro: order_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (auto simp: less_eq_dg_state_def intro: dg_state.expand antisym)
qed

instantiation dg_state :: (semilattice_sup, semilattice_sup) semilattice_sup
begin

definition sup_dg_state :: "('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state" where
  "sup_dg_state d1 d2 = DG (locals d1 \<squnion> locals d2) (globs d1 \<squnion> globs d2)"

instance
  by standard (auto simp: less_eq_dg_state_def sup_dg_state_def)

end

instantiation dg_state :: (order_bot, order_bot) order_bot
begin

definition bot_dg_state :: "('a, 'b) dg_state" where
  "bot_dg_state = DG bot bot"

instance
  by standard (simp add: less_eq_dg_state_def bot_dg_state_def)

end

instance dg_state ::
  (bounded_semilattice_sup_bot, bounded_semilattice_sup_bot) bounded_semilattice_sup_bot ..

instantiation dg_state :: (bounded_warrowing, bounded_warrowing) bounded_warrowing
begin

definition widen_dg_state ::
  "('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state"
where
  "widen_dg_state a b = DG (widen (locals a) (locals b)) (widen (globs a) (globs b))"

definition narrow_dg_state ::
  "('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state"
where
  "narrow_dg_state a b = DG (narrow (locals a) (locals b)) (narrow (globs a) (globs b))"

instance
  by standard
    (simp_all add: less_eq_dg_state_def widen_dg_state_def narrow_dg_state_def
      narrowing_class.narrow_ge narrowing_class.narrow_le
      widening_class.widen_ge1 widening_class.widen_ge2)

end

text \<open>Conversions to the pair representation and the homogeneous state.\<close>

definition pair_of_dg ::
  "('l abs_state, 'g abs_state) dg_state \<Rightarrow> ('l, 'g) split_state"
where
  "pair_of_dg d = (locals d, globs d)"

definition dg_of_pair ::
  "('l, 'g) split_state \<Rightarrow> ('l abs_state, 'g abs_state) dg_state"
where
  "dg_of_pair p = DG (fst p) (snd p)"

lemma pair_of_dg_of_pair [simp]: "pair_of_dg (dg_of_pair p) = p"
  by (simp add: pair_of_dg_def dg_of_pair_def)

lemma dg_of_pair_of_dg [simp]: "dg_of_pair (pair_of_dg d) = d"
  by (simp add: pair_of_dg_def dg_of_pair_def)

definition merge_dg :: "(vname \<Rightarrow> bool) \<Rightarrow> ('a abs_state, 'a abs_state) dg_state \<Rightarrow> 'a abs_state" where
  "merge_dg gs d = merge_state gs (pair_of_dg d)"

definition split_dg :: "(vname \<Rightarrow> bool) \<Rightarrow> 'a::bot abs_state \<Rightarrow> ('a abs_state, 'a abs_state) dg_state" where
  "split_dg gs s = dg_of_pair (split_state gs s)"

lemma merge_split_dg [simp]: "merge_dg gs (split_dg gs s) = s"
  by (simp add: merge_dg_def split_dg_def)

lemma split_dg_bot [simp]:
  "split_dg gs (bot :: 'a::bounded_semilattice_sup_bot abs_state) = bot"
  by (simp add: split_dg_def dg_of_pair_def split_state_bot bot_dg_state_def)

lemma split_dg_sup [simp]:
  fixes a b :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "split_dg gs (a \<squnion> b) = split_dg gs a \<squnion> split_dg gs b"
proof -
  have sp: "split_state gs (a \<squnion> b) =
      (fst (split_state gs a) \<squnion> fst (split_state gs b),
       snd (split_state gs a) \<squnion> snd (split_state gs b))"
    by (rule split_state_sup)
  show ?thesis
    unfolding split_dg_def dg_of_pair_def sup_dg_state_def
    by (simp add: sp)
qed

lemma split_dg_le_iff [simp]:
  fixes a b :: "'a::order_bot abs_state"
  shows "split_dg gs a \<le> split_dg gs b \<longleftrightarrow> a \<le> b"
  by (auto simp: split_dg_def dg_of_pair_def split_state_def
        less_eq_dg_state_def le_fun_def split: if_splits)



subsection \<open>The heterogeneous framework edge shape\<close>

text \<open>
  Two independent opaque domains.  An analysis provides
  \<open>step : D \<Rightarrow> G \<Rightarrow> G \<times> D\<close> (transfer plus publication); the framework reads the
  local unknown's \<open>D\<close> and the global slot's \<open>G\<close>, and transports the step's
  \<open>Side : G\<close> and \<open>Answer : D\<close>.  Slot packing (\<open>DG _ bot\<close> / \<open>DG bot _\<close>) is the
  encoding of the two-typed unknown space into the solver's single value type;
  the framework never looks inside \<open>D\<close> or \<open>G\<close>.
\<close>

definition dg_edge_tree ::
  "('dl::bounded_semilattice_sup_bot \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_edge_tree step u =
     do {
       d <- read_local u;
       g <- read_global ();
       depend_on () (DG bot (fst (step (locals d) (globs g))))
         (answer (DG (snd (step (locals d) (globs g))) bot))
     }"

lemma traverse_dg_edge_tree:
  "traverse_rhs (dg_edge_tree step u) \<tau>
   = DG (snd (step (locals (\<tau> (Inl u))) (globs (\<tau> (Inr ()))))) bot"
  unfolding dg_edge_tree_def by simp

lemma sides_dg_edge_tree_Inr:
  "sides_of_rhs (dg_edge_tree step u) \<tau> (Inr ())
   = DG bot (fst (step (locals (\<tau> (Inl u))) (globs (\<tau> (Inr ())))))"
  unfolding dg_edge_tree_def by (simp add: Let_def)

lemma sides_dg_edge_tree_Inl:
  "sides_of_rhs (dg_edge_tree step u) \<tau> (Inl v) = bot"
  unfolding dg_edge_tree_def by (simp add: Let_def)

lemma dep_aux_dg_edge_tree:
  "dep_aux \<tau> (dg_edge_tree step u) = {Inl u, Inr ()}"
  by (simp add: dg_edge_tree_def dep_aux_def)

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

subsection \<open>Side-free edge contribution, for buffered keyed generation (issue #121, keyed)\<close>

text \<open>
  \<open>dg_edge_tree\<close> publishes its \<open>G\<close> contribution as soon as it is evaluated
  (\<^const>\<open>depend_on\<close>). When \<open>side_cfg_T_eff_keyed_seed_dg\<close> (below) folds several such
  trees into one equation's RHS (several intra predecessors, or several return sites),
  each one's \<open>Side\<close> is published at a different moment within the same RHS evaluation:
  the vendored solver's warrowing/APINIS update rule gates convergence per \<^emph>\<open>origin\<close>, so
  repeated writes to the same key from the same origin can destabilize the equation's own
  dependency and never converge (Voblint issue #121).

  \<open>dg_edge_contribution_tree\<close> is the Side-free analogue: it answers the \<^emph>\<open>unsplit\<close>
  \<open>(G, D)\<close> result as one \<open>dg_state\<close>, publishing nothing. A caller folds several
  contribution trees with \<^const>\<open>fold_rhs_trees\<close> (whose own \<^const>\<open>Side\<close> is empty, so no
  intermediate publication happens) and splits the aggregate once, after every
  contribution has been read -- reproducing \<^const>\<open>dg_edge_tree\<close>'s declarative
  \<^const>\<open>traverse_rhs\<close>/\<^const>\<open>sides_of_rhs\<close> value while emitting at most one \<open>Side\<close> per
  key per RHS evaluation.
\<close>

definition dg_edge_contribution_tree ::
  "('dl::bounded_semilattice_sup_bot \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_edge_contribution_tree step u =
     do {
       d \<leftarrow> read_local u;
       g \<leftarrow> read_global ();
       answer (DG (snd (step (locals d) (globs g))) (fst (step (locals d) (globs g))))
     }"

lemma traverse_dg_edge_contribution_tree:
  "traverse_rhs (dg_edge_contribution_tree step u) \<tau>
   = DG (snd (step (locals (\<tau> (Inl u))) (globs (\<tau> (Inr ())))))
        (fst (step (locals (\<tau> (Inl u))) (globs (\<tau> (Inr ())))))"
  unfolding dg_edge_contribution_tree_def by simp

lemma sides_dg_edge_contribution_tree:
  "sides_of_rhs (dg_edge_contribution_tree step u) \<tau> k = bot"
  unfolding dg_edge_contribution_tree_def by (cases k) (simp_all add: Let_def)

lemma dep_aux_dg_edge_contribution_tree:
  "dep_aux \<tau> (dg_edge_contribution_tree step u) = {Inl u, Inr ()}"
  by (simp add: dg_edge_contribution_tree_def dep_aux_def)

lemma dg_edge_contribution_tree_matches_local:
  "locals (traverse_rhs (dg_edge_contribution_tree step u) \<tau>)
     = locals (traverse_rhs (dg_edge_tree step u) \<tau>)"
  by (simp add: traverse_dg_edge_contribution_tree traverse_dg_edge_tree)

lemma dg_edge_contribution_tree_matches_global:
  "globs (traverse_rhs (dg_edge_contribution_tree step u) \<tau>)
     = globs (sides_of_rhs (dg_edge_tree step u) \<tau> (Inr ()))"
  by (simp add: traverse_dg_edge_contribution_tree sides_dg_edge_tree_Inr)

text \<open>Procedure-return combine: two \<open>D\<close> inputs (caller, callee exit), one \<open>G\<close>.\<close>

definition dg_combine_tree ::
  "(call_info \<Rightarrow> 'dl::bounded_semilattice_sup_bot \<Rightarrow> 'dl \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> call_info \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_combine_tree comb ci cc ex =
     do {
       dc <- read_local cc;
       de <- read_local ex;
       g <- read_global ();
       depend_on () (DG bot (fst (comb ci (locals dc) (locals de) (globs g))))
         (answer (DG (snd (comb ci (locals dc) (locals de) (globs g))) bot))
     }"

lemma traverse_dg_combine_tree:
  "traverse_rhs (dg_combine_tree comb dst cc ex) \<tau>
   = DG (snd (comb dst (locals (\<tau> (Inl cc))) (locals (\<tau> (Inl ex))) (globs (\<tau> (Inr ()))))) bot"
  unfolding dg_combine_tree_def by simp

lemma sides_dg_combine_tree_Inr:
  "sides_of_rhs (dg_combine_tree comb dst cc ex) \<tau> (Inr ())
   = DG bot (fst (comb dst (locals (\<tau> (Inl cc))) (locals (\<tau> (Inl ex))) (globs (\<tau> (Inr ())))))"
  unfolding dg_combine_tree_def by (simp add: Let_def)

lemma sides_dg_combine_tree_Inl:
  "sides_of_rhs (dg_combine_tree comb dst cc ex) \<tau> (Inl v) = bot"
  unfolding dg_combine_tree_def by (simp add: Let_def)

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

lemma static_deps_dg_edge_tree: "static_deps (dg_edge_tree step u)"
  by (rule static_depsI) (simp add: dg_edge_tree_def)

lemma static_deps_dg_combine_tree: "static_deps (dg_combine_tree comb dst cc ex)"
  by (rule static_depsI) (simp add: dg_combine_tree_def)

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

subsection \<open>The analysis interface\<close>

text \<open>An analysis supplies one answer-and-side-effect transfer per edge action
  and a separate procedure-return combine.\<close>

text \<open>
  Procedure-return combine is split the same way Goblint's \<open>Spec\<close> splits it:
  an environment merge (\<open>dgs_combine_env\<close>, caller-local + callee-exit-local +
  global, no destination) followed by a return-value assign
  (\<open>dgs_combine_assign\<close>, reads the callee-exit's return slot, writes the
  destination, and packages the two-typed \<open>('dg, 'dl)\<close> answer).  \<open>'dl\<close>/\<open>'dg\<close>
  stay fully opaque -- the framework does not assume either field can share
  a generic assign the way the flat layer's \<open>abs_state\<close>-typed
  \<open>combine_assign\<^sup>#\<close> can, so both halves are analysis-supplied.\<close>

record ('dl, 'dg) dg_spec =
  dgs_skip       :: "'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_assign     :: "vname \<Rightarrow> exp \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_special    :: "special_call \<Rightarrow> vname \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_branch     :: "exp \<Rightarrow> bool \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_body       :: "pname \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_return     :: "exp option \<Rightarrow> pname \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_enter      :: "vname list \<Rightarrow> exp list \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_event      :: "analysis_event \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_caller_cont    :: "call_info \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dl"
  dgs_combine_env    :: "call_info \<Rightarrow> 'dl \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_combine_assign :: "call_info \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl \<Rightarrow> 'dg \<times> 'dl"

text \<open>The composed combine, in the pre-split curried shape every existing
  caller already uses fully applied (\<open>dgs_combine S dst dc de g\<close>).  Kept as
  a plain definition, not a record field, so the split above is the single
  source of truth and this cannot drift out of sync with it.\<close>
definition dgs_combine ::
  "('dl, 'dg) dg_spec \<Rightarrow> call_info \<Rightarrow> 'dl \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
where
  "dgs_combine S ci dcont de g = dgs_combine_assign S ci de g (dgs_combine_env S ci dcont de g)"

text \<open>
  The caller half of Goblint's \<open>enter\<close>, which returns a pair: the state the caller
  resumes from and the state the callee starts in.  \<open>dgs_caller_cont\<close> over-approximates
  the pre-call concrete caller store, retaining only information intended to remain
  usable when the call returns; it may forget abstract facts invalidated by potential
  callee effects, which is what lets a relational carrier drop relations the callee
  can break.  It reads the global carrier because every other \<^typ>\<open>('dl, 'dg) dg_spec\<close>
  operation does, but it publishes no globals: \<open>dgs_enter\<close> already owns the call's
  global side effect.
\<close>
definition dgs_enter_pair ::
  "('dl, 'dg) dg_spec \<Rightarrow> call_info \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dl \<times> ('dg \<times> 'dl)"
where
  "dgs_enter_pair S ci dc g =
     (dgs_caller_cont S ci dc g,
      dgs_enter S (ci_formals ci) (ci_args ci) dc g)"

lemma fst_dgs_enter_pair [simp]:
  "fst (dgs_enter_pair S ci dc g) = dgs_caller_cont S ci dc g"
  by (simp add: dgs_enter_pair_def)

lemma snd_dgs_enter_pair [simp]:
  "snd (dgs_enter_pair S ci dc g) = dgs_enter S (ci_formals ci) (ci_args ci) dc g"
  by (simp add: dgs_enter_pair_def)

text \<open>
  \<open>EA_Check\<close> routes through \<^const>\<open>dgs_event\<close> here, matching \<^const>\<open>apply_tf\<close>'s
  own \<open>event\<^sup>#\<close> dispatch: a concrete \<open>dg_spec\<close> supplies the D/G split's own
  notion of a check event directly, the same way it already supplies
  \<^const>\<open>dgs_body\<close>/\<^const>\<open>dgs_return\<close>.
\<close>
fun dg_spec_step ::
  "('dl, 'dg, 'z) dg_spec_scheme \<Rightarrow> edge_action \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
where
  "dg_spec_step S EA_Nop           = dgs_skip S"
| "dg_spec_step S (EA_Assign x e)  = dgs_assign S x e"
| "dg_spec_step S (EA_Special sc x) = dgs_special S sc x"
| "dg_spec_step S (EA_Assume b)    = dgs_branch S b True"
| "dg_spec_step S (EA_AssumeNot b) = dgs_branch S b False"
| "dg_spec_step S (EA_Ret e p)     = dgs_return S e p"
| "dg_spec_step S (EA_Check cnd)   = dgs_event S (Check_Event cnd)"

definition apply_dg_spec ::
  "('dl::bounded_semilattice_sup_bot, 'dg::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "apply_dg_spec S a u = dg_edge_tree (dg_spec_step S a) u"

definition apply_dg_spec_contribution ::
  "('dl::bounded_semilattice_sup_bot, 'dg::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "apply_dg_spec_contribution S a u = dg_edge_contribution_tree (dg_spec_step S a) u"

lemma apply_dg_spec_contribution_matches_local:
  "locals (traverse_rhs (apply_dg_spec_contribution S a u) \<tau>)
     = locals (traverse_rhs (apply_dg_spec S a u) \<tau>)"
  unfolding apply_dg_spec_contribution_def apply_dg_spec_def
  by (rule dg_edge_contribution_tree_matches_local)

lemma apply_dg_spec_contribution_matches_global:
  "globs (traverse_rhs (apply_dg_spec_contribution S a u) \<tau>)
     = globs (sides_of_rhs (apply_dg_spec S a u) \<tau> (Inr ()))"
  unfolding apply_dg_spec_contribution_def apply_dg_spec_def
  by (rule dg_edge_contribution_tree_matches_global)

lemma apply_dg_spec_dep_aux:
  "dep_aux \<tau> (apply_dg_spec S a u) = {Inl u, Inr ()}"
  unfolding apply_dg_spec_def by (rule dep_aux_dg_edge_tree)

lemma apply_dg_spec_contribution_dep_aux:
  "dep_aux \<tau> (apply_dg_spec_contribution S a u) = {Inl u, Inr ()}"
  unfolding apply_dg_spec_contribution_def by (rule dep_aux_dg_edge_contribution_tree)

lemma apply_dg_spec_contribution_dep_aux_matches:
  "dep_aux \<tau> (apply_dg_spec_contribution S a u) = dep_aux \<tau> (apply_dg_spec S a u)"
  by (simp add: apply_dg_spec_contribution_dep_aux apply_dg_spec_dep_aux)

definition dg_spec_combine_tree ::
  "('dl::bounded_semilattice_sup_bot, 'dg::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> call_info \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_spec_combine_tree S ci cc ex =
     dg_combine_tree
       (\<lambda>ci' dc de g. dgs_combine S ci' (dgs_caller_cont S ci' dc g) de g) ci cc ex"

text \<open>
  \<^const>\<open>dg_combine_tree\<close> reads the caller unknown, which holds the raw pre-call
  state; the continuation is reconstructed here, at the boundary standing in for
  \<open>enter\<close>, so \<^const>\<open>dgs_combine\<close> still receives a continuation and never the raw
  caller.  This is the non-routed counterpart of what \<open>routed_cmb_g\<close> does, and
  \<open>combine_sound_at_call\<close> is what licenses both.
\<close>

subsection \<open>The homogeneous unit analysis\<close>

text \<open>
  The unit analysis chooses \<open>D = G = 'a abs_state\<close>.  Each step merges the
  local Answer with the shared Side fact, applies the ordinary transfer, then
  publishes the global restriction and returns the local restriction.
\<close>

text \<open>The unit env-merge/assign split (defined below as \<open>unit_combine_step_env_for\<close>/
  \<open>unit_combine_step_assign_for\<close>) computes the structural local/global
  merge and packages it the same way \<^const>\<open>unit_step_for\<close> packages every
  other edge, but writes no return value yet; the assign step reconstitutes
  the full state from that packaging, writes the callee-exit's return slot,
  and re-splits -- matching \<^const>\<open>combine_collect_abs\<close> exactly once
  composed.\<close>
definition unit_combine_step_assign_for ::
  "(vname => bool) =>
   call_info => 'a::bounded_semilattice_sup_bot abs_state
   => 'a abs_state => 'a abs_state \<times> 'a abs_state
   => 'a abs_state \<times> 'a abs_state"
where
  "unit_combine_step_assign_for gs ci de g merged =
     (let res = combine_assign\<^sup># (ci_dst ci) (de ret_var)
         (fst merged \<squnion> snd merged)
      in (restrict_global_for gs res, restrict_local_for gs res))"


definition unit_combine_step_env_for ::
  "(vname => bool) => call_info =>
   'a::bounded_semilattice_sup_bot abs_state => 'a abs_state
   => 'a abs_state => 'a abs_state \<times> 'a abs_state" where
  "unit_combine_step_env_for gs ci dc de g =
     (let m = combine_env_abs gs dc g
      in (restrict_global_for gs m, restrict_local_for gs m))"

text \<open>
  The two halves of the environment merge rejoin to the merge itself, so a
  consumer that only needs \<^const>\<open>dgs_combine_assign\<close>'s \<open>fst \<squnion> snd\<close> argument
  never has to reason about the split.  \<^const>\<open>unit_combine_step_assign_for\<close> is
  monotone in exactly that argument and in the callee exit, so an analysis that
  replaces \<^const>\<open>dgs_combine_env\<close> by any merge above this one inherits
  soundness from this one instead of re-proving the return assignment.
\<close>

lemma unit_combine_step_env_for_join:
  "fst (unit_combine_step_env_for gs ci dc de g)
     \<squnion> snd (unit_combine_step_env_for gs ci dc de g)
   = combine_env_abs gs dc g"
  unfolding unit_combine_step_env_for_def
  by (simp add: Let_def restrict_global_for_local_join)

lemma unit_combine_step_assign_for_mono:
  fixes de1 de2 :: "'a::bounded_semilattice_sup_bot abs_state"
  assumes de: "de1 \<le> de2"
    and m: "fst m1 \<squnion> snd m1 \<le> fst m2 \<squnion> snd m2"
  shows "fst (unit_combine_step_assign_for gs ci de1 g m1)
           \<le> fst (unit_combine_step_assign_for gs ci de2 g m2)"
    and "snd (unit_combine_step_assign_for gs ci de1 g m1)
           \<le> snd (unit_combine_step_assign_for gs ci de2 g m2)"
proof -
  have res: "combine_assign\<^sup># (ci_dst ci) (de1 ret_var) (fst m1 \<squnion> snd m1)
               \<le> combine_assign\<^sup># (ci_dst ci) (de2 ret_var) (fst m2 \<squnion> snd m2)"
    by (rule combine_assign_abs_mono[OF le_funD[OF de] m])
  show "fst (unit_combine_step_assign_for gs ci de1 g m1)
          \<le> fst (unit_combine_step_assign_for gs ci de2 g m2)"
    unfolding unit_combine_step_assign_for_def Let_def fst_conv
    by (rule restrict_global_for_mono[OF res])
  show "snd (unit_combine_step_assign_for gs ci de1 g m1)
          \<le> snd (unit_combine_step_assign_for gs ci de2 g m2)"
    unfolding unit_combine_step_assign_for_def Let_def snd_conv
    by (rule restrict_local_for_mono[OF res])
qed

subsection \<open>The lifted combine split, staged ahead of \<^const>\<open>unit_combine_step_env_for\<close>/\<^const>\<open>unit_combine_step_assign_for\<close>'s own migration (issue #123)\<close>

text \<open>
  The two combine stages have different reachability disciplines. \<^const>\<open>unit_combine_step_env_for\<close>
  applies no domain transfer at all -- its body never reads \<open>de\<close> -- so it is pure
  structure-preserving reconstruction/projection: \<open>assemble_env_abs\<close> preserves whatever
  \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> status \<open>d\<close>/\<open>g\<close> already carry, with no \<open>is_bot_pred\<close> parameter, matching
  \<^const>\<open>unit_step_for_lifted\<close>'s own env-only case (\<open>unit_step_for_lifted_global_bot\<close>).

  \<^const>\<open>unit_combine_step_assign_for\<close> is where the callee-exit's reachability actually matters:
  it reads \<open>de ret_var\<close> directly. The soundness obligation this approximates
  (\<open>combine_sound\<close> in the \<open>sound_dg_spec\<close> locale: \<open>s \<in> gammaDG dc g \<Longrightarrow> t \<in> gammaDG de g \<Longrightarrow>
  combine_collect gs dst s t \<in> ...\<close>) is conditioned on \<open>t \<in> gammaDG de g\<close>; when that set is
  empty (an unreachable callee exit) the obligation is vacuous and \<^const>\<open>Bot\<close> is the tightest
  sound choice -- independent of whether the caller side is itself reachable. \<^const>\<open>transfer_lift2\<close>
  already has exactly this dominance (\<^const>\<open>Bot\<close> in either argument propagates), so no bespoke
  ternary combinator is needed here: reconstruct \<open>de\<close> against the env stage's rejoined output
  (\<open>fst merged \<squnion> snd merged\<close>, itself \<^const>\<open>Bot\<close>-preserving since both halves come from the same
  \<^const>\<open>map_lift\<close>-derived source), then transfer and normalize once via \<^const>\<open>transfer_lift2\<close>.

  \<^const>\<open>dg_combine_tree\<close> calls the two stages composed as a single \<open>comb\<close> application
  (\<^const>\<open>dgs_combine\<close>) and only ever observes that composed result -- the env stage's
  intermediate pair is never independently published -- so it is safe for the env stage to
  ignore \<open>de\<close>'s reachability entirely: it is enforced once, at the assign stage, the only place
  that actually consumes the callee exit.
\<close>

definition unit_combine_step_env_for_lifted ::
  "(vname => bool) => call_info
   => 'a::bounded_semilattice_sup_bot abs_state lifted => 'a abs_state lifted
   => 'a abs_state lifted \<times> 'a abs_state lifted"
where
  "unit_combine_step_env_for_lifted gs ci d g =
     (let m = assemble_env_abs gs d g
      in (map_lift (restrict_global_for gs) m, map_lift (restrict_local_for gs) m))"

lemma unit_combine_step_env_for_lifted_Bot_dominates_local [simp]:
  "unit_combine_step_env_for_lifted gs ci Bot g = (Bot, Bot)"
  unfolding unit_combine_step_env_for_lifted_def by simp

lemma unit_combine_step_env_for_lifted_global_bot:
  "unit_combine_step_env_for_lifted gs ci (Lifted d) Bot =
     (Lifted (restrict_global_for gs (combine_env_abs gs d bot)),
      Lifted (restrict_local_for gs (combine_env_abs gs d bot)))"
  unfolding unit_combine_step_env_for_lifted_def by simp

lemma unit_combine_step_env_for_lifted_agrees:
  "unit_combine_step_env_for_lifted gs ci (Lifted d) (Lifted g) =
     (Lifted (fst (unit_combine_step_env_for gs ci d de g)),
      Lifted (snd (unit_combine_step_env_for gs ci d de g)))"
  unfolding unit_combine_step_env_for_lifted_def unit_combine_step_env_for_def
  by (simp add: Let_def)

definition unit_combine_step_assign_for_lifted ::
  "(vname => bool)
   => call_info
   => ('a::bounded_semilattice_sup_bot abs_state => bool)
   => 'a abs_state lifted
   => 'a abs_state lifted \<times> 'a abs_state lifted
   => 'a abs_state lifted \<times> 'a abs_state lifted"
where
  "unit_combine_step_assign_for_lifted gs ci is_bot_pred de merged =
     (let joined = fst merged \<squnion> snd merged;
          res = transfer_lift2 is_bot_pred
                  (\<lambda>de0 env0. combine_assign\<^sup># (ci_dst ci) (de0 ret_var) env0) de joined
      in (map_lift (restrict_global_for gs) res, map_lift (restrict_local_for gs) res))"

lemma unit_combine_step_assign_for_lifted_de_bot [simp]:
  "unit_combine_step_assign_for_lifted gs ci is_bot_pred Bot merged = (Bot, Bot)"
  unfolding unit_combine_step_assign_for_lifted_def by simp

lemma unit_combine_step_assign_for_lifted_merged_bot [simp]:
  "unit_combine_step_assign_for_lifted gs ci is_bot_pred (Lifted de0) (Bot, Bot) = (Bot, Bot)"
  unfolding unit_combine_step_assign_for_lifted_def by simp

lemma unit_combine_step_assign_for_lifted_agrees:
  assumes "\<not> is_bot_pred (combine_assign\<^sup># (ci_dst ci) (de0 ret_var) (env0a \<squnion> env0b))"
  shows "unit_combine_step_assign_for_lifted gs ci is_bot_pred (Lifted de0) (Lifted env0a, Lifted env0b) =
           (Lifted (fst (unit_combine_step_assign_for gs ci de0 g (env0a, env0b))),
            Lifted (snd (unit_combine_step_assign_for gs ci de0 g (env0a, env0b))))"
  using assms
  unfolding unit_combine_step_assign_for_lifted_def unit_combine_step_assign_for_def
  by (simp add: Let_def)

lemma unit_combine_step_assign_for_lifted_collapses_bot:
  assumes "is_bot_pred (combine_assign\<^sup># (ci_dst ci) (de0 ret_var) (env0a \<squnion> env0b))"
  shows "unit_combine_step_assign_for_lifted gs ci is_bot_pred (Lifted de0) (Lifted env0a, Lifted env0b) = (Bot, Bot)"
  using assms
  unfolding unit_combine_step_assign_for_lifted_def
  by simp



definition unit_combine_step_env_placed ::
  "(vname => bool) => (vname => bool) => (vname => bool) => call_info =>
   'a::bounded_semilattice_sup_bot abs_state => 'a abs_state =>
   'a abs_state => 'a abs_state \<times> 'a abs_state"
where
  "unit_combine_step_env_placed source_global keep_local publish_side ci dc de g =
     (let res = combine_env_abs source_global (dc \<squnion> g) (de \<squnion> g) in
      (project_component publish_side res, project_component keep_local res))"


definition unit_combine_step_assign_placed ::
  "(vname => bool) => (vname => bool) => call_info =>
   'a::bounded_semilattice_sup_bot abs_state => 'a abs_state =>
   'a abs_state \<times> 'a abs_state => 'a abs_state \<times> 'a abs_state"
where
  "unit_combine_step_assign_placed keep_local publish_side ci de g merged =
     (let res = combine_assign\<^sup># (ci_dst ci) ((de \<squnion> g) ret_var)
         (fst merged \<squnion> snd merged)
      in (project_component publish_side res, project_component keep_local res))"


definition unit_dg_spec_placed ::
  "(vname => bool) => (vname => bool) => (vname => bool) =>
   'a::sound_domain domain_transfer => ('a abs_state, 'a abs_state) dg_spec"
where
  "unit_dg_spec_placed source_global keep_local publish_side tf = \<lparr>
    dgs_skip       = unit_step_placed keep_local publish_side (apply_tf tf EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step_placed keep_local publish_side
      (apply_tf tf (EA_Assign x e))),
    dgs_special    = (\<lambda>sc x. unit_step_placed keep_local publish_side
      (apply_tf tf (EA_Special sc x))),
    dgs_branch     = (\<lambda>b pol. unit_step_placed keep_local publish_side
      (branch\<^sup># tf b pol)),
    dgs_body       = (\<lambda>p. unit_step_placed keep_local publish_side
      (body\<^sup># tf p)),
    dgs_return     = (\<lambda>e p. unit_step_placed keep_local publish_side
      (return\<^sup># tf e p)),
    dgs_enter      = (\<lambda>xs es. unit_step_placed keep_local publish_side
      (enter\<^sup># tf xs es)),
    dgs_event      = (\<lambda>ev. unit_step_placed keep_local publish_side
      (event\<^sup># tf ev)),
    dgs_caller_cont = (\<lambda>_ d _. d),
    dgs_combine_env = unit_combine_step_env_placed source_global keep_local publish_side,
    dgs_combine_assign = unit_combine_step_assign_placed keep_local publish_side
  \<rparr>"
lemma dg_spec_step_unit_placed:
  "dg_spec_step (unit_dg_spec_placed source_global keep_local publish_side tf) a =
    unit_step_placed keep_local publish_side (apply_tf tf a)"
  unfolding unit_dg_spec_placed_def
  by (cases a) simp_all

lemma dgs_enter_unit_dg_spec_placed:
  "dgs_enter (unit_dg_spec_placed source_global keep_local publish_side tf) fs as =
    unit_step_placed keep_local publish_side (enter\<^sup># tf fs as)"
  unfolding unit_dg_spec_placed_def
  by simp





definition unit_dg_spec_for ::
  "(vname => bool) => 'a::sound_domain domain_transfer
   => ('a abs_state, 'a abs_state) dg_spec"
where
  "unit_dg_spec_for gs tf = \<lparr>
    dgs_skip       = unit_step_for gs (apply_tf tf EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step_for gs (apply_tf tf (EA_Assign x e))),
    dgs_special    = (\<lambda>sc x. unit_step_for gs (apply_tf tf (EA_Special sc x))),
    dgs_branch     = (\<lambda>b pol. unit_step_for gs (branch\<^sup># tf b pol)),
    dgs_body       = (\<lambda>p. unit_step_for gs (body\<^sup># tf p)),
    dgs_return     = (\<lambda>e p. unit_step_for gs (return\<^sup># tf e p)),
    dgs_enter      = (\<lambda>xs es. unit_step_for gs (enter\<^sup># tf xs es)),
    dgs_event      = (\<lambda>ev. unit_step_for gs (event\<^sup># tf ev)),
    dgs_caller_cont    = (\<lambda>_ d _. d),
    dgs_combine_env    = unit_combine_step_env_for gs,
    dgs_combine_assign = unit_combine_step_assign_for gs
  \<rparr>"

text \<open>Unlike the plain collecting semantics' \<^const>\<open>combine_collect_abs\<close>, the
  D/G-split combine cannot read the return value and the global effects from the
  same argument: the return slot is a local name owned by the callee's exit
  state \<open>de\<close>, while every global name is owned by the freshly-queried \<open>g\<close>, not
  by \<open>de\<close>'s own (locally-restricted) copy of it. \<^const>\<open>combine_env_abs\<close> still
  supplies the ownership routing for the non-return names; \<open>de ret_var\<close> is
  read directly instead of routing it through that same combine.\<close>
lemma dgs_combine_unit_dg_spec_for:
  "dgs_combine (unit_dg_spec_for gs tf) ci dcont de g =
     (let res = combine_assign\<^sup># (ci_dst ci) (de ret_var) (combine_env_abs gs dcont g)
      in (restrict_global_for gs res, restrict_local_for gs res))"
  unfolding dgs_combine_def unit_dg_spec_for_def
    unit_combine_step_assign_for_def Let_def
  by (simp add: unit_combine_step_env_for_join)

lemma dg_spec_step_unit_for:
  "dg_spec_step (unit_dg_spec_for gs tf) a = unit_step_for gs (apply_tf tf a)"
  unfolding unit_dg_spec_for_def
  by (cases a) simp_all

lemma dgs_enter_unit_dg_spec_for:
  "dgs_enter (unit_dg_spec_for gs tf) fs as =
     unit_step_for gs (enter\<^sup># tf fs as)"
  unfolding unit_dg_spec_for_def
  by simp

subsection \<open>The complete lifted D/G specification, additive alongside \<^const>\<open>unit_dg_spec_for\<close> (issue #123)\<close>

text \<open>
  Assembles the three independently-validated lifted primitives into one \<^type>\<open>dg_spec\<close>
  record, additive so no existing consumer of \<^const>\<open>unit_dg_spec_for\<close> is affected.
  \<^const>\<open>dgs_combine_env\<close>/\<^const>\<open>dgs_combine_assign\<close> both formally take a \<open>de\<close>/\<open>g\<close> argument the
  record shape requires (\<^const>\<open>dgs_combine\<close> threads all four positionally); the env field
  drops \<open>de\<close> and the assign field drops \<open>g\<close>, exactly mirroring which parameters
  \<^const>\<open>unit_combine_step_env_for\<close>/\<^const>\<open>unit_combine_step_assign_for\<close> themselves leave unused.
\<close>

definition unit_dg_spec_for_lifted ::
  "(vname => bool)
   => ('a::sound_domain abs_state => bool)
   => 'a domain_transfer
   => ('a abs_state lifted, 'a abs_state lifted) dg_spec"
where
  "unit_dg_spec_for_lifted gs is_bot_pred tf = \<lparr>
    dgs_skip       = unit_step_for_lifted gs is_bot_pred (apply_tf tf EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step_for_lifted gs is_bot_pred (apply_tf tf (EA_Assign x e))),
    dgs_special    = (\<lambda>sc x. unit_step_for_lifted gs is_bot_pred (apply_tf tf (EA_Special sc x))),
    dgs_branch     = (\<lambda>b pol. unit_step_for_lifted gs is_bot_pred (branch\<^sup># tf b pol)),
    dgs_body       = (\<lambda>p. unit_step_for_lifted gs is_bot_pred (body\<^sup># tf p)),
    dgs_return     = (\<lambda>e p. unit_step_for_lifted gs is_bot_pred (return\<^sup># tf e p)),
    dgs_enter      = (\<lambda>xs es. unit_step_for_lifted gs is_bot_pred (enter\<^sup># tf xs es)),
    dgs_event      = (\<lambda>ev. unit_step_for_lifted gs is_bot_pred (event\<^sup># tf ev)),
    dgs_caller_cont    = (\<lambda>_ d _. d),
    dgs_combine_env    = (\<lambda>ci dc de g. unit_combine_step_env_for_lifted gs ci dc g),
    dgs_combine_assign = (\<lambda>ci de g merged. unit_combine_step_assign_for_lifted gs ci is_bot_pred de merged)
  \<rparr>"

text \<open>Gate 1 -- record-level type sanity: the generic \<^const>\<open>dg_spec_step\<close>/\<^const>\<open>dgs_combine\<close>
  machinery accepts a \<^type>\<open>dg_spec\<close> whose carriers are \<^type>\<open>lifted\<close> exactly as it accepts the
  raw carrier, and dispatches to the staged primitives with no further reasoning about \<open>gs\<close>.\<close>

lemma dg_spec_step_unit_for_lifted:
  "dg_spec_step (unit_dg_spec_for_lifted gs is_bot_pred tf) a =
     unit_step_for_lifted gs is_bot_pred (apply_tf tf a)"
  unfolding unit_dg_spec_for_lifted_def
  by (cases a) simp_all

lemma dgs_enter_unit_dg_spec_for_lifted:
  "dgs_enter (unit_dg_spec_for_lifted gs is_bot_pred tf) fs as =
     unit_step_for_lifted gs is_bot_pred (enter\<^sup># tf fs as)"
  unfolding unit_dg_spec_for_lifted_def by simp

lemma dgs_combine_unit_dg_spec_for_lifted:
  "dgs_combine (unit_dg_spec_for_lifted gs is_bot_pred tf) ci dc de g =
     unit_combine_step_assign_for_lifted gs ci is_bot_pred de
       (unit_combine_step_env_for_lifted gs ci dc g)"
  unfolding dgs_combine_def unit_dg_spec_for_lifted_def by simp

text \<open>Gate 2 -- whole-record agreement on reachable inputs whose transfer result is not itself
  witness-bottom: the lifted record reduces to \<^const>\<open>unit_dg_spec_for\<close>'s existing behaviour,
  wrapped in \<^const>\<open>Lifted\<close>.\<close>

lemma dg_spec_step_unit_for_lifted_agrees:
  assumes "\<not> is_bot_pred (apply_tf tf a (combine_env_abs gs d g))"
  shows "dg_spec_step (unit_dg_spec_for_lifted gs is_bot_pred tf) a (Lifted d) (Lifted g) =
           (Lifted (fst (dg_spec_step (unit_dg_spec_for gs tf) a d g)),
            Lifted (snd (dg_spec_step (unit_dg_spec_for gs tf) a d g)))"
  using assms
  unfolding dg_spec_step_unit_for_lifted dg_spec_step_unit_for
  by (rule unit_step_for_lifted_agrees)

lemma dgs_combine_unit_dg_spec_for_lifted_agrees:
  assumes "\<not> is_bot_pred (combine_assign\<^sup># (ci_dst ci) (de ret_var) (combine_env_abs gs dc g))"
  shows "dgs_combine (unit_dg_spec_for_lifted gs is_bot_pred tf) ci (Lifted dc) (Lifted de) (Lifted g) =
           (Lifted (fst (dgs_combine (unit_dg_spec_for gs tf) ci dc de g)),
            Lifted (snd (dgs_combine (unit_dg_spec_for gs tf) ci dc de g)))"
proof -
  have joined: "restrict_global_for gs (combine_env_abs gs dc g) \<squnion> restrict_local_for gs (combine_env_abs gs dc g)
                  = combine_env_abs gs dc g"
    by (rule restrict_global_for_local_join)
  show ?thesis
    unfolding dgs_combine_unit_dg_spec_for_lifted dgs_combine_unit_dg_spec_for
      unit_combine_step_env_for_lifted_def unit_combine_step_env_for_def
      unit_combine_step_assign_for_lifted_def unit_combine_step_assign_for_def
    using assms
    by (simp add: Let_def joined)
qed

text \<open>Gate 3 -- whole-record strictness: both the unary and the return/combine semantic-bottom
  cases collapse to structural \<^const>\<open>Bot\<close>, and callee-exit unreachability dominates the combine
  independent of the caller side's own reachability (including through the env stage, which by
  construction never inspects \<open>de\<close>).\<close>

lemma dg_spec_step_unit_for_lifted_collapses_bot:
  assumes "is_bot_pred (apply_tf tf a (combine_env_abs gs d g))"
  shows "dg_spec_step (unit_dg_spec_for_lifted gs is_bot_pred tf) a (Lifted d) (Lifted g) = (Bot, Bot)"
  using assms
  unfolding dg_spec_step_unit_for_lifted
  by (rule unit_step_for_lifted_collapses_bot)

lemma dgs_combine_unit_dg_spec_for_lifted_de_bot:
  "dgs_combine (unit_dg_spec_for_lifted gs is_bot_pred tf) ci dc Bot g = (Bot, Bot)"
  unfolding dgs_combine_unit_dg_spec_for_lifted by simp

lemma dgs_combine_unit_dg_spec_for_lifted_dc_bot:
  "dgs_combine (unit_dg_spec_for_lifted gs is_bot_pred tf) ci Bot (Lifted de) g = (Bot, Bot)"
  unfolding dgs_combine_unit_dg_spec_for_lifted by simp



fun side_rhs_fold_dg ::
  "'d::bounded_semilattice_sup_bot
   \<Rightarrow> ('x, 'g, ('d, 'h::bounded_semilattice_sup_bot) dg_state) strategy_tree list
   \<Rightarrow> ('x, 'g, ('d, 'h) dg_state) strategy_tree"
where
  "side_rhs_fold_dg acc [] = Answer (DG acc bot)"
| "side_rhs_fold_dg acc (t # ts) =
     seqcomp_tree t (\<lambda>res. side_rhs_fold_dg (acc \<squnion> locals res) ts)"

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

lemma side_rhs_fold_dg_static_deps:
  assumes tree_static: "\<forall>t \<in> set ts. static_deps t"
  shows "static_deps (side_rhs_fold_dg acc ts)"
  unfolding static_deps_def
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
      using Cons.prems unfolding static_deps_def by simp
    have tail_static: "\<forall>t' \<in> set ts. static_deps t'"
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



subsection \<open>The representation-neutral keyed generator\<close>

text \<open>The keyed generator constructs the equation shape from supplied tree hooks.  Each hook receives the CFG nodes that determine its source and destination; routing and representation choices remain outside the generator.\<close>

definition side_cfg_T_eff_keyed_seed_trees ::
  "(cfg => pp => (pp \<times> edge_action) list)
   => ('c => 'k)
   => ('c => pp => edge_action => pp
        => (pp \<times> 'c, 'k, ('d::bounded_semilattice_sup_bot,
          'h::bounded_semilattice_sup_bot) dg_state) strategy_tree)
   => ('c => pp => call_action => pp => pp
        => (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree)
   => ('c => pp => call_action => pp
        => (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree)
   => cfg => 'd => 'd => 'h
   => (pp \<times> 'c, 'k, ('d, 'h) dg_state) eqsT"
where
  "side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
      g bot0 s0d s0g =
    (\<lambda>(v, ctx).
      let acc0 = (if v = cfg_entry g then bot0 \<squnion> s0d else bot0);
          intra = map (\<lambda>(u, action). edge_tree ctx u action v) (pred_sel g v);
          combine = map (\<lambda>(call, action, exit). combine_tree ctx call action exit v)
            (return_call_action_list g v);
          enter = map (\<lambda>(call, action). enter_tree ctx call action v)
            (entry_call_list g v);
          tree = side_rhs_fold_dg acc0 (intra @ combine @ enter)
      in if v = cfg_entry g then depend_on (gkey ctx) (DG bot s0g) tree else tree)"

lemma eq_side_cfg_T_eff_keyed_seed_trees:
  "eq (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
      g bot0 s0d s0g) (v, ctx) sigma =
    DG (side_acc_dg (if v = cfg_entry g then bot0 \<squnion> s0d else bot0) sigma
      (map (\<lambda>(u, action). edge_tree ctx u action v) (pred_sel g v)
       @ map (\<lambda>(call, action, exit). combine_tree ctx call action exit v)
           (return_call_action_list g v)
       @ map (\<lambda>(call, action). enter_tree ctx call action v)
           (entry_call_list g v))) bot"
  by (simp add: side_cfg_T_eff_keyed_seed_trees_def Let_def
    traverse_side_rhs_fold_dg)

text \<open>
  Every node of a CFG has at most one incoming hook tree per predecessor
  kind, and a typical node has exactly one incoming tree overall (a single
  intra predecessor, a single call return, or a single call entry, with the
  other two kinds empty). These four lemmas reduce the generator to that one
  tree directly, so an instance proves per-node soundness or refinement
  against the named tree constructor instead of re-deriving the fold's
  single-element degeneracy at every call site. They are stated for
  \<^const>\<open>side_cfg_T_eff_keyed_seed_trees\<close> itself, so they specialize to any
  concrete generator built from it -- the hook-parametric \<open>hook_gen\<close> and the
  executable/abstract \<open>placed_dg_gen_of_strict\<close>/\<open>placed_abs_dg_gen_of\<close> alike --
  without re-unfolding \<open>side_cfg_T_eff_keyed_seed_trees_def\<close> at each one.
\<close>

lemma side_cfg_T_eff_keyed_seed_trees_single_edge:
  fixes bot0 :: "'d::bounded_semilattice_sup_bot"
  assumes not_entry: "v \<noteq> cfg_entry g"
    and pred: "pred_sel g v = [(u, a)]"
    and no_combine: "return_call_action_list g v = []"
    and no_enter: "entry_call_list g v = []"
    and bot0: "bot0 = bot"
  shows
    "eq (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
        g bot0 s0d s0g) (v, ctx) sigma =
       DG (locals (traverse_rhs (edge_tree ctx u a v) sigma)) bot"
    "sides_of_rhs
       (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
         g bot0 s0d s0g (v, ctx)) sigma (Inr (gkey ctx)) =
       sides_of_rhs (edge_tree ctx u a v) sigma (Inr (gkey ctx))"
  unfolding side_cfg_T_eff_keyed_seed_trees_def
  by (simp_all add: not_entry pred no_combine no_enter bot0
    Let_def sides_of_rhs_seqcomp traverse_seqcomp)

lemma side_cfg_T_eff_keyed_seed_trees_single_enter:
  fixes bot0 :: "'d::bounded_semilattice_sup_bot"
  assumes not_entry: "v \<noteq> cfg_entry g"
    and no_edge: "pred_sel g v = []"
    and no_combine: "return_call_action_list g v = []"
    and pred: "entry_call_list g v = [(caller, action)]"
    and bot0: "bot0 = bot"
  shows
    "eq (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
        g bot0 s0d s0g) (v, ctx) sigma =
       DG (locals (traverse_rhs (enter_tree ctx caller action v) sigma)) bot"
    "sides_of_rhs
       (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
         g bot0 s0d s0g (v, ctx)) sigma (Inr (gkey ctx)) =
       sides_of_rhs (enter_tree ctx caller action v) sigma (Inr (gkey ctx))"
  unfolding side_cfg_T_eff_keyed_seed_trees_def
  by (simp_all add: not_entry no_edge no_combine pred bot0
    Let_def sides_of_rhs_seqcomp traverse_seqcomp)

lemma side_cfg_T_eff_keyed_seed_trees_single_combine:
  fixes bot0 :: "'d::bounded_semilattice_sup_bot"
  assumes not_entry: "v \<noteq> cfg_entry g"
    and no_edge: "pred_sel g v = []"
    and pred: "return_call_action_list g v = [(caller, action, callee_exit)]"
    and no_enter: "entry_call_list g v = []"
    and bot0: "bot0 = bot"
  shows
    "eq (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
        g bot0 s0d s0g) (v, ctx) sigma =
       DG (locals (traverse_rhs (combine_tree ctx caller action callee_exit v) sigma)) bot"
    "sides_of_rhs
       (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
         g bot0 s0d s0g (v, ctx)) sigma (Inr (gkey ctx)) =
       sides_of_rhs (combine_tree ctx caller action callee_exit v) sigma (Inr (gkey ctx))"
  unfolding side_cfg_T_eff_keyed_seed_trees_def
  by (simp_all add: not_entry no_edge pred no_enter bot0
    Let_def sides_of_rhs_seqcomp traverse_seqcomp)

lemma side_cfg_T_eff_keyed_seed_trees_entry:
  fixes bot0 :: "'d::bounded_semilattice_sup_bot"
  assumes no_edge: "pred_sel g (cfg_entry g) = []"
    and no_combine: "return_call_action_list g (cfg_entry g) = []"
    and no_enter: "entry_call_list g (cfg_entry g) = []"
    and bot0: "bot0 = bot"
  shows
    "eq (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
        g bot0 s0d s0g) (cfg_entry g, ctx) sigma = DG s0d bot"
    "sides_of_rhs
       (side_cfg_T_eff_keyed_seed_trees pred_sel gkey edge_tree combine_tree enter_tree
         g bot0 s0d s0g (cfg_entry g, ctx)) sigma (Inr (gkey ctx)) = DG bot s0g"
  unfolding side_cfg_T_eff_keyed_seed_trees_def
  by (simp_all add: no_edge no_combine no_enter bot0 Let_def)

subsection \<open>The heterogeneous seeded keyed generator\<close>

text \<open>
  The one context-generic generator.  Enter handling is routed by three hooks so
  that a monovariant and a context-sensitive analysis are both instances:

  \<^item> \<open>pred_sel\<close> selects the intra predecessors folded as Answers into a node.  The
    monovariant instance uses \<^const>\<open>intra_predecessor_list\<close> over \<^const>\<open>intra\<close>; a
    callee entry over \<^const>\<open>calls\<close> merges into the single callee context, while the
    context-sensitive instance instead publishes routed callee seeds.
  \<^item> \<open>cmb\<close> is the procedure-return combine tree (already fully abstract: the
    context-sensitive instance reads the callee exit under the routed context).
  \<^item> \<open>extra c v\<close> supplies additional per-node trees folded after the intra and
    combine trees.  Their Answers add to the node's local accumulator and their
    \<^const>\<open>Side\<close> effects are collected --- this is where a frame-entry seed
    \<^emph>\<open>read\<close> (a \<^const>\<open>QueryG\<close> of the incoming seed slot) and the caller-side
    call-entry \<^emph>\<open>publication\<close> (a routed \<^const>\<open>Side\<close> to the callee seed
    slot) live.  The monovariant instance supplies \<open>\<lambda>_ _. []\<close>.
\<close>

definition side_cfg_T_eff_keyed_seed_dg ::
  "(cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action) list)
   \<Rightarrow> ('c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> ((pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
        \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree)
   \<Rightarrow> ((pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> pp
        \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree list)
   \<Rightarrow> cfg
   \<Rightarrow> ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'h
   \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) eqsT"
where
  "side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0 \<squnion> s0d else bot0);
            intra = map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c)
                            (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u)))
                        (pred_sel g v);
            comb = map (\<lambda>(cc, ca, ex). cmb route c ca cc ex)
                       (return_call_action_list g v);
            t = side_rhs_fold_dg acc0 (intra @ comb @ extra route c v)
        in if v = cfg_entry g then depend_on (gkey c) (DG bot s0g) t else t)"

lemma eq_side_cfg_T_eff_keyed_seed_dg:
  "eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g)
      (v, ctx) \<tau> =
   DG (side_acc_dg
     (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)
     \<tau>
     (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u)))
           (pred_sel g v)
      @ map (\<lambda>(cc, ca, ex). cmb route ctx ca cc ex)
            (return_call_action_list g v)
      @ extra route ctx v)) bot"
  by (simp add: side_cfg_T_eff_keyed_seed_dg_def Let_def
        traverse_side_rhs_fold_dg)

lemma sides_side_cfg_T_eff_keyed_seed_dg:
  "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g
      (v, ctx)) \<tau> (Inr (gkey ctx)) =
   (if v = cfg_entry g then DG bot s0g else bot)
   \<squnion> foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
       (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u)))
          (pred_sel g v)
        @ map (\<lambda>(cc, ca, ex). cmb route ctx ca cc ex) (return_call_action_list g v)
        @ extra route ctx v) bot"
  by (simp add: side_cfg_T_eff_keyed_seed_dg_def Let_def sides_of_rhs_side_rhs_fold_dg_char
        bot_dg_state_def[symmetric] ac_simps)

subsection \<open>Buffered generator: fold Side-free contributions, publish once\<close>

text \<open>
  \<^const>\<open>side_cfg_T_eff_keyed_seed_dg\<close> writes a node's own key once per contribution: a
  merge node with several intra predecessors, or several return call actions, each
  independently publishes a \<open>Side (gkey c) ...\<close> via \<^const>\<open>dg_edge_tree\<close>/\<open>routed_cmb_g\<close>'s
  own \<^const>\<open>depend_on\<close>, so several writes to the same \<open>gkey c\<close> land in one RHS
  evaluation. \<open>side_cfg_T_eff_keyed_seed_dg_buffered\<close> folds Side-free contribution trees
  (\<^const>\<open>apply_dg_spec_contribution\<close> for \<open>intra\<close>; the caller's own Side-free \<open>cmb_c\<close> for
  \<open>comb\<close>) with \<^const>\<open>fold_rhs_trees\<close> and publishes \<open>gkey c\<close> once, after every
  contribution has been read.

  That fold shapes the node's \<^emph>\<open>own\<close> key, but \<open>extra route c v\<close> stays a list of
  independent trees, and a caller node's extras publish one routed callee seed per call
  action. Two call sites resuming at the same node therefore still name one seed key
  twice. \<^const>\<open>buffer_sides\<close> closes that case for every key uniformly, so
  \<open>distinct_side_path_buffer_sides\<close> --- not an argument about which keys the hooks
  happen to choose --- is what establishes at most one \<^const>\<open>Side\<close> per key per RHS
  evaluation. It preserves the declarative
  \<^const>\<open>traverse_rhs\<close>/\<^const>\<open>sides_of_rhs\<close> value, so the correspondence with the
  unbuffered generator below is unaffected.
\<close>

definition side_cfg_T_eff_keyed_seed_dg_buffered ::
  "(cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action) list)
   \<Rightarrow> ('c \<Rightarrow> 'k)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> ((pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
        \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree)
   \<Rightarrow> ((pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> pp
        \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree list)
   \<Rightarrow> cfg
   \<Rightarrow> ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'h
   \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) eqsT"
where
  "side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then DG (bot0 \<squnion> s0d) s0g else DG bot0 bot);
            intra = map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c)
                            (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec_contribution S a u)))
                        (pred_sel g v);
            comb = map (\<lambda>(cc, ca, ex). cmb_c route c ca cc ex) (return_call_action_list g v);
            t = fold_rhs_trees acc0 (intra @ comb @ extra route c v)
        in buffer_sides (do {
          res \<leftarrow> t;
          depend_on (gkey c) (DG bot (globs res)) (answer (DG (locals res) bot))
        }))"

lemma eq_side_cfg_T_eff_keyed_seed_dg_buffered:
  "eq (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g)
      (v, ctx) \<tau> =
   DG (locals (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc')
     (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec_contribution S a u))) (pred_sel g v)
      @ map (\<lambda>(cc, ca, ex). cmb_c route ctx ca cc ex) (return_call_action_list g v)
      @ extra route ctx v)
     (if v = cfg_entry g then DG (bot0 \<squnion> s0d) s0g else DG bot0 bot))) bot"
  by (simp add: side_cfg_T_eff_keyed_seed_dg_buffered_def Let_def traverse_fold_rhs_trees_char)

lemma sides_dg_edge_contribution_tree_relabeled:
  "sides_of_rhs (map_gtree r (map_ltree h (dg_edge_contribution_tree step u))) \<tau> z = bot"
  by (cases z) (simp_all add: dg_edge_contribution_tree_def Let_def)

lemma sides_apply_dg_spec_contribution_relabeled:
  "sides_of_rhs (map_gtree r (map_ltree h (apply_dg_spec_contribution S a u))) \<tau> z = bot"
  unfolding apply_dg_spec_contribution_def by (rule sides_dg_edge_contribution_tree_relabeled)

lemma foldr_sup_bot_of_all_bot:
  fixes L :: "'a list" and h :: "'a \<Rightarrow> 'b::bounded_semilattice_sup_bot"
  assumes "\<And>x. x \<in> set L \<Longrightarrow> h x = bot"
  shows "foldr (\<lambda>x acc'. h x \<squnion> acc') L bot = bot"
  using assms by (induction L) simp_all

lemma sides_side_cfg_T_eff_keyed_seed_dg_buffered:
  assumes comb_free_at_key: "\<And>c' ca cc ex \<sigma>. sides_of_rhs (cmb_c route c' ca cc ex) \<sigma> (Inr (gkey c')) = bot"
    and extra_free: "\<And>c' w \<sigma> z x. x \<in> set (extra route c' w) \<Longrightarrow> sides_of_rhs x \<sigma> z = bot"
  shows "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
      (v, ctx)) \<tau> (Inr (gkey ctx)) =
   DG bot (globs (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc')
     (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec_contribution S a u))) (pred_sel g v)
      @ map (\<lambda>(cc, ca, ex). cmb_c route ctx ca cc ex) (return_call_action_list g v)
      @ extra route ctx v)
     (if v = cfg_entry g then DG (bot0 \<squnion> s0d) s0g else DG bot0 bot)))"
proof -
  have free: "\<And>w \<sigma> x. x \<in> set (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                    (map_ltree (\<lambda>w'. (w', ctx)) (apply_dg_spec_contribution S a u))) (pred_sel g w)
      @ map (\<lambda>(cc, ca, ex). cmb_c route ctx ca cc ex) (return_call_action_list g w)
      @ extra route ctx w) \<Longrightarrow> sides_of_rhs x \<sigma> (Inr (gkey ctx)) = bot"
    using comb_free_at_key extra_free sides_apply_dg_spec_contribution_relabeled
    by fastforce
  show ?thesis
  proof (cases "v = cfg_entry g")
    case True
    have z0: "sides_of_rhs (fold_rhs_trees (DG (bot0 \<squnion> s0d) s0g)
        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                 (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec_contribution S a u))) (pred_sel g (cfg_entry g))
         @ map (\<lambda>(cc, ca, ex). cmb_c route ctx ca cc ex) (return_call_action_list g (cfg_entry g))
         @ extra route ctx (cfg_entry g))) \<tau> (Inr (gkey ctx)) = bot"
      by (simp only: sides_of_rhs_fold_rhs_trees_char
          foldr_sup_bot_of_all_bot[OF free[where w = "cfg_entry g"]])
    from True show ?thesis
      by (simp add: side_cfg_T_eff_keyed_seed_dg_buffered_def Let_def traverse_fold_rhs_trees_char
          bot_dg_state_def sup_dg_state_def z0)
  next
    case False
    have z0: "sides_of_rhs (fold_rhs_trees (DG bot0 bot)
        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                 (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec_contribution S a u))) (pred_sel g v)
         @ map (\<lambda>(cc, ca, ex). cmb_c route ctx ca cc ex) (return_call_action_list g v)
         @ extra route ctx v)) \<tau> (Inr (gkey ctx)) = bot"
      by (simp only: sides_of_rhs_fold_rhs_trees_char
          foldr_sup_bot_of_all_bot[OF free[where w = v]])
    from False show ?thesis
      by (simp add: side_cfg_T_eff_keyed_seed_dg_buffered_def Let_def traverse_fold_rhs_trees_char
          bot_dg_state_def sup_dg_state_def z0)
  qed
qed

subsection \<open>Correspondence: the buffered generator matches the original\<close>

lemma apply_dg_spec_contribution_matches_local_relabeled:
  "locals (traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
       (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec_contribution S a u))) \<tau>)
     = locals (traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
       (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))) \<tau>)"
  by (simp add: traverse_intra_keyed apply_dg_spec_contribution_matches_local)

lemma apply_dg_spec_contribution_matches_global_relabeled:
  "globs (traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
       (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec_contribution S a u))) \<tau>)
     = globs (sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
       (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))) \<tau> (Inr (gkey ctx)))"
proof -
  have step1: "sides_of_rhs
        (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))) \<tau> (Inr (gkey ctx))
      = sides_of_rhs (apply_dg_spec S a u) (\<lambda>z. \<tau> (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. gkey ctx) z)) (Inr ())"
  proof -
    have "sides_of_rhs
            (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))) \<tau>
            (Inr ((\<lambda>_. gkey ctx) ()))
        = sides_of_rhs (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))
            (\<lambda>z. \<tau> (map_sum id (\<lambda>_. gkey ctx) z)) (Inr ())"
      by (rule sides_map_gtree_unit)
    thus ?thesis by (simp add: sides_map_ltree_Inr sum.map_comp o_def)
  qed
  show ?thesis
    by (simp add: traverse_intra_keyed apply_dg_spec_contribution_matches_global step1)
qed

lemma apply_dg_spec_contribution_dep_aux_relabeled:
  "dep_aux \<tau> (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec_contribution S a u)))
     = dep_aux \<tau> (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u)))"
  by (simp add: dep_aux_map_gtree dep_aux_map_ltree
        apply_dg_spec_contribution_dep_aux apply_dg_spec_dep_aux)

lemma side_acc_dg_eq_foldr:
  "side_acc_dg acc \<tau> ts = foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc') ts acc"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  have "foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc') ts (acc \<squnion> locals (traverse_rhs a \<tau>))
      = locals (traverse_rhs a \<tau>) \<squnion> foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc') ts acc"
    by (simp add: sup_commute[of acc] foldr_sup_seed_swap)
  then show ?case using Cons.IH by simp
qed

text \<open>
  A pointwise correspondence between two parallel contribution lists -- one Side-free
  (feeding \<^const>\<open>fold_rhs_trees\<close>), one Side-emitting (feeding \<^const>\<open>side_rhs_fold_dg\<close>)
  -- lifts to their whole-list fold, in both the local-answer and global-side
  components. This is the list-level engine behind
  \<open>side_cfg_T_eff_keyed_seed_dg_buffered_correspondence\<close>: each of \<open>intra\<close>, \<open>comb\<close>, and
  \<open>extra\<close> instantiates it once, and \<open>foldr_append\<close> combines the three.
\<close>

lemma fold_rhs_trees_side_rhs_fold_dg_local_char:
  assumes h: "list_all2 (\<lambda>t_new t_old. locals (traverse_rhs t_new \<tau>) = locals (traverse_rhs t_old \<tau>))
                L_new L_old"
  shows "foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc') L_new (acc::'d::bounded_semilattice_sup_bot)
       = foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc') L_old acc"
  using h by (induction rule: list_all2_induct) simp_all

lemma foldr_globs_sides_char:
  fixes L :: "('x, 'k, ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state)
                strategy_tree list"
  shows "foldr (\<lambda>t acc'. globs (sides_of_rhs t \<tau> z) \<squnion> acc') L bot
       = globs (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') L bot)"
  by (induction L) (simp_all add: bot_dg_state_def sup_dg_state_def)

lemma DG_sup_bot_left:
  "DG (bot::'d::bounded_semilattice_sup_bot) a \<squnion> DG bot b = DG bot (a \<squnion> b)"
  by (simp add: sup_dg_state_def bot_dg_state_def)

lemma foldr_sides_locals_bot:
  fixes L :: "('x, 'k, ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state)
                strategy_tree list"
  assumes "\<And>t. t \<in> set L \<Longrightarrow> locals (sides_of_rhs t \<tau> z) = bot"
  shows "locals (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') L bot) = bot"
  using assms
proof (induction L)
  case Nil
  then show ?case by (simp add: bot_dg_state_def)
next
  case (Cons t ts)
  then show ?case by (simp add: sup_dg_state_def)
qed

lemma list_all2_map_diag:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P (f x) (g x)) \<Longrightarrow> list_all2 P (map f xs) (map g xs)"
  by (induction xs) simp_all

lemma sides_of_rhs_Inl_bot:
  "sides_of_rhs T \<sigma> (Inl x) = bot"
  by (induction T arbitrary: \<sigma>) (auto simp: Let_def)

lemma list_all2_Union_eq:
  assumes "list_all2 (\<lambda>a b. f a = g b) xs ys"
  shows "(\<Union>x\<in>set xs. f x) = (\<Union>y\<in>set ys. g y)"
  using assms by (induction rule: list_all2_induct) auto

lemma locals_foldr_generic:
  "locals (foldr (\<lambda>t acc'. h t \<squnion> acc') L
      (acc::('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state))
     = foldr (\<lambda>t acc'. locals (h t) \<squnion> acc') L (locals acc)"
  by (induction L) (simp_all add: sup_dg_state_def)

lemma globs_foldr_generic:
  "globs (foldr (\<lambda>t acc'. h t \<squnion> acc') L
      (acc::('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state))
     = foldr (\<lambda>t acc'. globs (h t) \<squnion> acc') L (globs acc)"
  by (induction L) (simp_all add: sup_dg_state_def)

lemma foldr_join_seed_out:
  "foldr (\<lambda>t acc'. h t \<squnion> acc') ts (a::'a::bounded_semilattice_sup_bot)
     = a \<squnion> foldr (\<lambda>t acc'. h t \<squnion> acc') ts bot"
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  then show ?case by (simp add: ac_simps)
qed

lemma fold_rhs_trees_side_rhs_fold_dg_global_char:
  assumes h: "list_all2 (\<lambda>t_new t_old. globs (traverse_rhs t_new \<tau>) = globs (sides_of_rhs t_old \<tau> z))
                L_new L_old"
  shows "foldr (\<lambda>t acc'. globs (traverse_rhs t \<tau>) \<squnion> acc') L_new (acc::'h::bounded_semilattice_sup_bot)
       = foldr (\<lambda>t acc'. globs (sides_of_rhs t \<tau> z) \<squnion> acc') L_old acc"
  using h by (induction rule: list_all2_induct) simp_all

text \<open>
  \<open>side_cfg_T_eff_keyed_seed_dg_buffered\<close>'s declarative value matches
  \<open>side_cfg_T_eff_keyed_seed_dg\<close>'s, given that \<open>cmb_c\<close> is the Side-free contribution
  analogue of \<open>cmb\<close> at the SAME \<open>gkey ctx\<close> slot (\<open>comb_t\<close>/\<open>comb_s\<close>/\<open>comb_free\<close> --
  \<open>routed_cmb_g_contribution\<close>/\<open>routed_cmb_g\<close> discharge these, per
  \<open>routed_cmb_g_contribution_matches_local\<close>/\<open>_global\<close> in \<open>Routed_Context\<close>) and \<open>extra\<close> is
  Side-free and answers only its local slot (\<open>extra_free\<close>/\<open>extra_local_only\<close> --
  \<open>routed_extra_g\<close> discharges both by direct inspection, since it answers via
  \<open>answer_local\<close> and issues no \<open>Side\<close>). \<open>intra\<close> needs no hypothesis:
  \<^const>\<open>apply_dg_spec_contribution\<close> vs \<^const>\<open>apply_dg_spec\<close> match unconditionally, for
  any \<open>dg_spec\<close>.
\<close>

lemma apply_dg_spec_side_pure_relabeled:
  "locals (sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
       (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))) \<tau> (Inr (gkey ctx))) = bot"
proof -
  have "sides_of_rhs
          (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))) \<tau>
          (Inr ((\<lambda>_. gkey ctx) ()))
      = sides_of_rhs (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))
          (\<lambda>z. \<tau> (map_sum id (\<lambda>_. gkey ctx) z)) (Inr ())"
    by (rule sides_map_gtree_unit)
  then have "sides_of_rhs
      (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))) \<tau> (Inr (gkey ctx))
      = sides_of_rhs (apply_dg_spec S a u)
          (\<lambda>z. \<tau> (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. gkey ctx) z)) (Inr ())"
    by (simp add: sides_map_ltree_Inr sum.map_comp o_def)
  then show ?thesis
    unfolding apply_dg_spec_def by (simp add: dg_edge_tree_side_pure_G)
qed

lemma side_cfg_T_eff_keyed_seed_dg_buffered_correspondence:
  fixes cmb cmb_c ::
    "(pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
       \<Rightarrow> (pp \<times> 'c, 'k, ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state)
            strategy_tree"
  assumes comb_t: "\<And>c' ca cc ex \<tau>. locals (traverse_rhs (cmb_c route c' ca cc ex) \<tau>)
                     = locals (traverse_rhs (cmb route c' ca cc ex) \<tau>)"
    and comb_side_pure: "\<And>c' ca cc ex \<tau>. locals (sides_of_rhs (cmb route c' ca cc ex) \<tau> (Inr (gkey c'))) = bot"
    and comb_s: "\<And>c' ca cc ex \<tau>. globs (traverse_rhs (cmb_c route c' ca cc ex) \<tau>)
                     = globs (sides_of_rhs (cmb route c' ca cc ex) \<tau> (Inr (gkey c')))"
    and comb_free_at_key: "\<And>c' ca cc ex \<tau>. sides_of_rhs (cmb_c route c' ca cc ex) \<tau> (Inr (gkey c')) = bot"
    and comb_sides_off_key: "\<And>c' ca cc ex \<tau> z. z \<noteq> Inr (gkey c')
                     \<Longrightarrow> sides_of_rhs (cmb_c route c' ca cc ex) \<tau> z = sides_of_rhs (cmb route c' ca cc ex) \<tau> z"
    and comb_dep: "\<And>c' ca cc ex \<tau>. dep_aux \<tau> (cmb_c route c' ca cc ex) = dep_aux \<tau> (cmb route c' ca cc ex)"
    and extra_free: "\<And>c' w \<tau> z x. x \<in> set (extra route c' w) \<Longrightarrow> sides_of_rhs x \<tau> z = bot"
    and extra_local_only: "\<And>c' w \<tau> x. x \<in> set (extra route c' w) \<Longrightarrow> globs (traverse_rhs x \<tau>) = bot"
  shows "traverse_rhs
           (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
             (v, ctx)) \<tau>
         = traverse_rhs
           (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>"
    (is ?T)
    and "dep_aux \<tau>
           (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g (v, ctx))
         = dep_aux \<tau>
           (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx))"
    (is ?D)
    and "sides_of_rhs
           (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
             (v, ctx)) \<tau>
         = sides_of_rhs
           (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>"
    (is ?S)
proof -
  let ?intra_new = "map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                       (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec_contribution S a u))) (pred_sel g v)"
  let ?intra_old = "map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                       (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))) (pred_sel g v)"
  let ?comb_new = "map (\<lambda>(cc, ca, ex). cmb_c route ctx ca cc ex) (return_call_action_list g v)"
  let ?comb_old = "map (\<lambda>(cc, ca, ex). cmb route ctx ca cc ex) (return_call_action_list g v)"
  let ?extra = "extra route ctx v"
  let ?acc0 = "if v = cfg_entry g then DG (bot0 \<squnion> s0d) s0g else DG bot0 bot"
  have intra_local: "list_all2 (\<lambda>t_new t_old. locals (traverse_rhs t_new \<tau>) = locals (traverse_rhs t_old \<tau>))
      ?intra_new ?intra_old"
    by (rule list_all2_map_diag) (auto simp: apply_dg_spec_contribution_matches_local_relabeled)
  have intra_global: "list_all2 (\<lambda>t_new t_old. globs (traverse_rhs t_new \<tau>)
                                    = globs (sides_of_rhs t_old \<tau> (Inr (gkey ctx)))) ?intra_new ?intra_old"
    by (rule list_all2_map_diag) (auto simp: apply_dg_spec_contribution_matches_global_relabeled)
  have comb_local: "list_all2 (\<lambda>t_new t_old. locals (traverse_rhs t_new \<tau>) = locals (traverse_rhs t_old \<tau>))
      ?comb_new ?comb_old"
    by (rule list_all2_map_diag) (auto simp: comb_t)
  have comb_global: "list_all2 (\<lambda>t_new t_old. globs (traverse_rhs t_new \<tau>)
                                   = globs (sides_of_rhs t_old \<tau> (Inr (gkey ctx)))) ?comb_new ?comb_old"
    by (rule list_all2_map_diag) (auto simp: comb_s)
  have extra_local: "list_all2 (\<lambda>t_new t_old. locals (traverse_rhs t_new \<tau>) = locals (traverse_rhs t_old \<tau>))
      ?extra ?extra"
    by (rule list.rel_refl_strong) simp
  have extra_global: "list_all2 (\<lambda>t_new t_old. globs (traverse_rhs t_new \<tau>)
                                    = globs (sides_of_rhs t_old \<tau> (Inr (gkey ctx)))) ?extra ?extra"
    by (rule list.rel_refl_strong) (simp add: extra_free extra_local_only bot_dg_state_def)
  have local_list: "list_all2 (\<lambda>t_new t_old. locals (traverse_rhs t_new \<tau>) = locals (traverse_rhs t_old \<tau>))
      (?intra_new @ ?comb_new @ ?extra) (?intra_old @ ?comb_old @ ?extra)"
    using intra_local comb_local extra_local by (intro list_all2_appendI)
  have global_list: "list_all2 (\<lambda>t_new t_old. globs (traverse_rhs t_new \<tau>)
                                   = globs (sides_of_rhs t_old \<tau> (Inr (gkey ctx))))
      (?intra_new @ ?comb_new @ ?extra) (?intra_old @ ?comb_old @ ?extra)"
    using intra_global comb_global extra_global by (intro list_all2_appendI)
  show ?T
  proof -
    have "traverse_rhs
        (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
          (v, ctx)) \<tau>
        = DG (locals (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) ?acc0)) bot"
      by (rule eq_side_cfg_T_eff_keyed_seed_dg_buffered)
    also have "\<dots> = DG (foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc')
                     (?intra_new @ ?comb_new @ ?extra) (locals ?acc0)) bot"
      by (simp add: locals_foldr_generic)
    also have "\<dots> = DG (foldr (\<lambda>t acc'. locals (traverse_rhs t \<tau>) \<squnion> acc')
                     (?intra_old @ ?comb_old @ ?extra) (locals ?acc0)) bot"
      by (simp only: fold_rhs_trees_side_rhs_fold_dg_local_char[OF local_list])
    also have "\<dots> = DG (side_acc_dg (locals ?acc0) \<tau> (?intra_old @ ?comb_old @ ?extra)) bot"
      by (simp add: side_acc_dg_eq_foldr)
    also have "\<dots> = traverse_rhs
        (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>"
      by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
    finally show ?thesis .
  qed
  have global_new: "sides_of_rhs
      (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
        (v, ctx)) \<tau> (Inr (gkey ctx))
      = DG bot (globs (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) ?acc0))"
    by (intro sides_side_cfg_T_eff_keyed_seed_dg_buffered) (use comb_free_at_key extra_free in blast)+
  have globs_new_char: "globs (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) ?acc0)
      = globs ?acc0
        \<squnion> foldr (\<lambda>t acc'. globs (sides_of_rhs t \<tau> (Inr (gkey ctx))) \<squnion> acc') (?intra_old @ ?comb_old @ ?extra) bot"
  proof -
    have "globs (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) ?acc0)
        = foldr (\<lambda>t acc'. globs (traverse_rhs t \<tau>) \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) (globs ?acc0)"
      by (rule globs_foldr_generic)
    also have "\<dots> = foldr (\<lambda>t acc'. globs (sides_of_rhs t \<tau> (Inr (gkey ctx))) \<squnion> acc')
                     (?intra_old @ ?comb_old @ ?extra) (globs ?acc0)"
      by (simp only: fold_rhs_trees_side_rhs_fold_dg_global_char[OF global_list])
    also have "\<dots> = globs ?acc0
                     \<squnion> foldr (\<lambda>t acc'. globs (sides_of_rhs t \<tau> (Inr (gkey ctx))) \<squnion> acc')
                         (?intra_old @ ?comb_old @ ?extra) bot"
      by (rule foldr_join_seed_out)
    finally show ?thesis .
  qed
  have old_elem_side_pure: "\<And>t. t \<in> set (?intra_old @ ?comb_old @ ?extra)
      \<Longrightarrow> locals (sides_of_rhs t \<tau> (Inr (gkey ctx))) = bot"
    using comb_side_pure extra_free
    by (auto simp: apply_dg_spec_side_pure_relabeled bot_dg_state_def split: prod.splits)
  have old_fold_side_pure: "locals
      (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc') (?intra_old @ ?comb_old @ ?extra) bot)
      = bot"
    by (rule foldr_sides_locals_bot) (rule old_elem_side_pure)
  have old_fold_collapse: "foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
      (?intra_old @ ?comb_old @ ?extra) bot
      = DG bot (globs (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
           (?intra_old @ ?comb_old @ ?extra) bot))"
    using old_fold_side_pure by (cases "foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
           (?intra_old @ ?comb_old @ ?extra) bot") simp
  have old_sides: "sides_of_rhs
      (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>
      (Inr (gkey ctx))
      = DG bot (globs ?acc0
                \<squnion> globs (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
                     (?intra_old @ ?comb_old @ ?extra) bot))"
  proof -
    have "sides_of_rhs
        (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>
        (Inr (gkey ctx))
        = (if v = cfg_entry g then DG bot s0g else bot)
          \<squnion> foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
              (?intra_old @ ?comb_old @ ?extra) bot"
      by (rule sides_side_cfg_T_eff_keyed_seed_dg)
    also have "\<dots> = DG bot (globs ?acc0
          \<squnion> globs (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
              (?intra_old @ ?comb_old @ ?extra) bot))"
      by (subst old_fold_collapse) (cases "v = cfg_entry g", simp_all add: DG_sup_bot_left bot_dg_state_def)
    finally show ?thesis .
  qed
  have S_at_key: "sides_of_rhs
      (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
        (v, ctx)) \<tau> (Inr (gkey ctx))
      = sides_of_rhs
        (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>
        (Inr (gkey ctx))"
  proof -
    have "sides_of_rhs
        (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
          (v, ctx)) \<tau> (Inr (gkey ctx))
        = DG bot (globs (foldr (\<lambda>t acc'. traverse_rhs t \<tau> \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) ?acc0))"
      by (rule global_new)
    also have "\<dots> = DG bot (globs ?acc0
        \<squnion> globs (foldr (\<lambda>t acc'. sides_of_rhs t \<tau> (Inr (gkey ctx)) \<squnion> acc')
             (?intra_old @ ?comb_old @ ?extra) bot))"
      by (simp only: globs_new_char foldr_globs_sides_char)
    also have "\<dots> = sides_of_rhs
        (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau>
        (Inr (gkey ctx))"
      by (rule old_sides[symmetric])
    finally show ?thesis .
  qed
  have intra_dep: "list_all2 (\<lambda>t_new t_old. dep_aux \<tau> t_new = dep_aux \<tau> t_old) ?intra_new ?intra_old"
    by (rule list_all2_map_diag) (auto simp: apply_dg_spec_contribution_dep_aux_relabeled)
  have comb_dep_list: "list_all2 (\<lambda>t_new t_old. dep_aux \<tau> t_new = dep_aux \<tau> t_old) ?comb_new ?comb_old"
    by (rule list_all2_map_diag) (auto simp: comb_dep)
  have extra_dep: "list_all2 (\<lambda>t_new t_old. dep_aux \<tau> t_new = dep_aux \<tau> t_old) ?extra ?extra"
    by (rule list.rel_refl_strong) simp
  have dep_list: "list_all2 (\<lambda>t_new t_old. dep_aux \<tau> t_new = dep_aux \<tau> t_old)
      (?intra_new @ ?comb_new @ ?extra) (?intra_old @ ?comb_old @ ?extra)"
    using intra_dep comb_dep_list extra_dep by (intro list_all2_appendI)
  show ?D
  proof -
    have "dep_aux \<tau>
        (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g (v, ctx))
        = (\<Union>t\<in>set (?intra_new @ ?comb_new @ ?extra). dep_aux \<tau> t)"
      by (simp add: side_cfg_T_eff_keyed_seed_dg_buffered_def Let_def dep_aux_seqcomp
          dep_aux_fold_rhs_trees_char)
    also have "\<dots> = (\<Union>t\<in>set (?intra_old @ ?comb_old @ ?extra). dep_aux \<tau> t)"
      by (rule list_all2_Union_eq[OF dep_list])
    also have "\<dots> = dep_aux \<tau>
        (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx))"
      by (simp add: side_cfg_T_eff_keyed_seed_dg_def Let_def dep_aux_seqcomp
          dep_aux_side_rhs_fold_dg_char)
    finally show ?thesis .
  qed
  have intra_sides_off: "\<And>z. z \<noteq> Inr (gkey ctx)
      \<Longrightarrow> list_all2 (\<lambda>t_new t_old. sides_of_rhs t_new \<tau> z = sides_of_rhs t_old \<tau> z) ?intra_new ?intra_old"
  proof -
    fix z :: "cfg_node \<times> 'c + 'k"
    assume z: "z \<noteq> Inr (gkey ctx)"
    have old_bot: "\<And>u a. sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
        (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))) \<tau> z = bot"
    proof -
      fix u a
      show "sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
          (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))) \<tau> z = bot"
      proof (cases z)
        case (Inl xx)
        then show ?thesis by (simp add: sides_of_rhs_Inl_bot)
      next
        case (Inr k)
        with z have "k \<noteq> gkey ctx" by simp
        then have "k \<notin> range (\<lambda>_::'c. gkey ctx)" by auto
        with Inr show ?thesis by (simp add: sides_map_gtree_off)
      qed
    qed
    show "list_all2 (\<lambda>t_new t_old. sides_of_rhs t_new \<tau> z = sides_of_rhs t_old \<tau> z) ?intra_new ?intra_old"
      by (rule list_all2_map_diag)
         (auto simp: sides_apply_dg_spec_contribution_relabeled old_bot)
  qed
  have comb_sides_off: "\<And>z. z \<noteq> Inr (gkey ctx)
      \<Longrightarrow> list_all2 (\<lambda>t_new t_old. sides_of_rhs t_new \<tau> z = sides_of_rhs t_old \<tau> z) ?comb_new ?comb_old"
    by (rule list_all2_map_diag) (auto simp: comb_sides_off_key)
  have extra_sides_off: "\<And>z. list_all2 (\<lambda>t_new t_old. sides_of_rhs t_new \<tau> z = sides_of_rhs t_old \<tau> z)
      ?extra ?extra"
    by (rule list.rel_refl_strong) simp
  have sides_list_off: "\<And>z. z \<noteq> Inr (gkey ctx)
      \<Longrightarrow> list_all2 (\<lambda>t_new t_old. sides_of_rhs t_new \<tau> z = sides_of_rhs t_old \<tau> z)
          (?intra_new @ ?comb_new @ ?extra) (?intra_old @ ?comb_old @ ?extra)"
    using intra_sides_off comb_sides_off extra_sides_off by (intro list_all2_appendI)
  have fold_sides_off: "\<And>z. z \<noteq> Inr (gkey ctx) \<Longrightarrow>
      foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) bot
        = foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') (?intra_old @ ?comb_old @ ?extra) bot"
  proof -
    fix z :: "cfg_node \<times> 'c + 'k"
    assume z: "z \<noteq> Inr (gkey ctx)"
    show "foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) bot
        = foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') (?intra_old @ ?comb_old @ ?extra) bot"
      using sides_list_off[OF z] by (induction rule: list_all2_induct) simp_all
  qed
  show ?S
  proof (rule ext)
    fix z
    show "sides_of_rhs
        (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
          (v, ctx)) \<tau> z
      = sides_of_rhs
        (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau> z"
    proof (cases "z = Inr (gkey ctx)")
      case True
      with S_at_key show ?thesis by simp
    next
      case False
      have new_off: "sides_of_rhs
          (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g
            (v, ctx)) \<tau> z
        = foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') (?intra_new @ ?comb_new @ ?extra) bot"
        using False
        by (simp add: side_cfg_T_eff_keyed_seed_dg_buffered_def Let_def sides_of_rhs_seqcomp
            sides_of_rhs_fold_rhs_trees_char bot_dg_state_def[symmetric])
      have old_off: "sides_of_rhs
          (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, ctx)) \<tau> z
        = foldr (\<lambda>t acc'. sides_of_rhs t \<tau> z \<squnion> acc') (?intra_old @ ?comb_old @ ?extra) bot"
        using False
        by (simp add: side_cfg_T_eff_keyed_seed_dg_def Let_def sides_of_rhs_fold_rhs_trees_char
            sides_of_rhs_side_rhs_fold_dg_char)
      from new_off old_off fold_sides_off[OF False] show ?thesis by simp
    qed
  qed
qed

text \<open>
  The observational interface \<^const>\<open>part_post_solution\<close> actually consumes: given the
  correspondence, a buffered post-solution is also an unbuffered one. Callers only need
  this fact, never the tree-shape argument behind \<open>side_cfg_T_eff_keyed_seed_dg_buffered_correspondence\<close>
  itself -- \<^const>\<open>part_post_solution\<close>'s three conjuncts (\<open>dep\<^sub>L\<close>, \<open>eq\<close>, \<open>sides_of_rhs\<close>) are
  exactly \<open>?D\<close>/\<open>?T\<close>/\<open>?S\<close>, read pointwise at each \<open>u \<in> vars\<close>.
\<close>

lemma part_post_solution_seed_dg_buffered_to_old:
  fixes cmb cmb_c ::
    "(pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
       \<Rightarrow> (pp \<times> 'c, 'k, ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_state)
            strategy_tree"
  assumes comb_t: "\<And>c' ca cc ex \<tau>. locals (traverse_rhs (cmb_c route c' ca cc ex) \<tau>)
                     = locals (traverse_rhs (cmb route c' ca cc ex) \<tau>)"
    and comb_side_pure: "\<And>c' ca cc ex \<tau>. locals (sides_of_rhs (cmb route c' ca cc ex) \<tau> (Inr (gkey c'))) = bot"
    and comb_s: "\<And>c' ca cc ex \<tau>. globs (traverse_rhs (cmb_c route c' ca cc ex) \<tau>)
                     = globs (sides_of_rhs (cmb route c' ca cc ex) \<tau> (Inr (gkey c')))"
    and comb_free_at_key: "\<And>c' ca cc ex \<tau>. sides_of_rhs (cmb_c route c' ca cc ex) \<tau> (Inr (gkey c')) = bot"
    and comb_sides_off_key: "\<And>c' ca cc ex \<tau> z. z \<noteq> Inr (gkey c')
                     \<Longrightarrow> sides_of_rhs (cmb_c route c' ca cc ex) \<tau> z = sides_of_rhs (cmb route c' ca cc ex) \<tau> z"
    and comb_dep: "\<And>c' ca cc ex \<tau>. dep_aux \<tau> (cmb_c route c' ca cc ex) = dep_aux \<tau> (cmb route c' ca cc ex)"
    and extra_free: "\<And>c' w \<tau> z x. x \<in> set (extra route c' w) \<Longrightarrow> sides_of_rhs x \<tau> z = bot"
    and extra_local_only: "\<And>c' w \<tau> x. x \<in> set (extra route c' w) \<Longrightarrow> globs (traverse_rhs x \<tau>) = bot"
    and pp_buf: "part_post_solution
        (side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g)
        x sigma vars"
  shows "part_post_solution
      (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) x sigma vars"
proof -
  let ?Tbuf = "side_cfg_T_eff_keyed_seed_dg_buffered pred_sel gkey route cmb_c extra g S bot0 s0d s0g"
  let ?Told = "side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g"
  have corr: "\<And>u. traverse_rhs (?Tbuf u) sigma = traverse_rhs (?Told u) sigma
      \<and> dep_aux sigma (?Tbuf u) = dep_aux sigma (?Told u)
      \<and> sides_of_rhs (?Tbuf u) sigma = sides_of_rhs (?Told u) sigma"
  proof -
    fix u :: "pp \<times> 'c"
    obtain v ctx where u: "u = (v, ctx)" by (cases u) auto
    show "traverse_rhs (?Tbuf u) sigma = traverse_rhs (?Told u) sigma
        \<and> dep_aux sigma (?Tbuf u) = dep_aux sigma (?Told u)
        \<and> sides_of_rhs (?Tbuf u) sigma = sides_of_rhs (?Told u) sigma"
      unfolding u
      using side_cfg_T_eff_keyed_seed_dg_buffered_correspondence
              [where cmb = cmb and cmb_c = cmb_c and route = route and gkey = gkey,
               OF comb_t comb_side_pure comb_s comb_free_at_key comb_sides_off_key comb_dep
                  extra_free extra_local_only]
      by simp
  qed
  from pp_buf have x_in: "x \<in> vars" by simp
  have "\<forall>u\<in>vars. dep\<^sub>L ?Told sigma u \<subseteq> vars \<and> eq ?Told u sigma \<le> sigma (Inl u)
      \<and> sides_of_rhs (?Told u) sigma \<le> sigma"
  proof
    fix u assume uv: "u \<in> vars"
    with pp_buf have buf: "dep\<^sub>L ?Tbuf sigma u \<subseteq> vars" "eq ?Tbuf u sigma \<le> sigma (Inl u)"
        "sides_of_rhs (?Tbuf u) sigma \<le> sigma"
      by auto
    have dL: "dep\<^sub>L ?Told sigma u = dep\<^sub>L ?Tbuf sigma u"
      using corr[of u] unfolding dep\<^sub>L_def dep_def by simp
    have eqv: "eq ?Told u sigma = eq ?Tbuf u sigma"
      using corr[of u] by simp
    have sv: "sides_of_rhs (?Told u) sigma = sides_of_rhs (?Tbuf u) sigma"
      using corr[of u] by simp
    show "dep\<^sub>L ?Told sigma u \<subseteq> vars \<and> eq ?Told u sigma \<le> sigma (Inl u) \<and> sides_of_rhs (?Told u) sigma \<le> sigma"
      unfolding dL eqv sv using buf by simp
  qed
  with x_in show ?thesis by simp
qed

subsection \<open>Threefold monotonicity for an arbitrary generator instance\<close>

text \<open>
  The three
  @{const TD_side_mono} preconditions reduce to a per-tree contract on the
  intra, combine, and extra hooks, discharged once here and reusable at every
  routing policy --- a routed context policy is then a second interpretation
  of this reduction, not a second monotonicity proof. The outer @{const Side}
  wrapper at @{term "cfg_entry g"} is invisible to @{const traverse_rhs} and
  @{const dep_aux} (a \<^const>\<open>Side\<close> node only ever repackages, never queries);
  it only has to be threaded through the @{const sides_of_rhs} case via
  @{thm fun_upd_sup_mono}.
\<close>

lemma side_cfg_T_eff_keyed_seed_dg_is_mono_eq_gen:
  fixes g :: cfg
    and S :: "('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_spec"
  assumes intra_mono: "\<forall>v c u a s1 s2. (u, a) \<in> set (pred_sel g v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      traverse_rhs (map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u))) s1
        \<le> traverse_rhs (map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u))) s2"
  assumes comb_mono: "\<forall>v c cc ca ex s1 s2. (cc, ca, ex) \<in> set (return_call_action_list g v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      traverse_rhs (cmb route c ca cc ex) s1 \<le> traverse_rhs (cmb route c ca cc ex) s2"
  assumes extra_mono: "\<forall>v c t s1 s2. t \<in> set (extra route c v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      traverse_rhs t s1 \<le> traverse_rhs t s2"
  shows "is_mono_eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g)"
proof -
  have key: "\<And>v c s1 s2. s1 \<le> s2 \<Longrightarrow>
      eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) (v, c) s1
        \<le> eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) (v, c) s2"
  proof -
    fix v c s1 s2
    show "s1 \<le> s2 \<Longrightarrow>
        eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) (v, c) s1
          \<le> eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) (v, c) s2"
    proof -
      assume le: "s1 \<le> s2"
      have tree_mono: "\<forall>t \<in> set (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u)))
                                  (pred_sel g v)
                            @ map (\<lambda>(cc, ca, ex). cmb route c ca cc ex) (return_call_action_list g v)
                            @ extra route c v).
                         \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> traverse_rhs t s1 \<le> traverse_rhs t s2"
        using intra_mono comb_mono extra_mono by auto
      have step: "traverse_rhs (side_rhs_fold_dg (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)
                     (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u)))
                          (pred_sel g v)
                       @ map (\<lambda>(cc, ca, ex). cmb route c ca cc ex) (return_call_action_list g v)
                       @ extra route c v)) s1
                  \<le> traverse_rhs (side_rhs_fold_dg (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)
                     (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u)))
                          (pred_sel g v)
                       @ map (\<lambda>(cc, ca, ex). cmb route c ca cc ex) (return_call_action_list g v)
                       @ extra route c v)) s2"
        by (rule side_rhs_fold_dg_mono[OF tree_mono le])
      show "eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) (v, c) s1
            \<le> eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) (v, c) s2"
        unfolding eq_side_cfg_T_eff_keyed_seed_dg using step
        by (simp add: traverse_side_rhs_fold_dg)
    qed
  qed
  show ?thesis
    unfolding is_mono_eq_def using key by fastforce
qed

lemma side_cfg_T_eff_keyed_seed_dg_mono_sides_gen:
  fixes g :: cfg
    and S :: "('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_spec"
  assumes intra_sides_mono: "\<forall>v c u a s1 s2. (u, a) \<in> set (pred_sel g v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      sides_of_rhs (map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u))) s1
        \<le> sides_of_rhs (map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u))) s2"
  assumes comb_sides_mono: "\<forall>v c cc ca ex s1 s2. (cc, ca, ex) \<in> set (return_call_action_list g v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      sides_of_rhs (cmb route c ca cc ex) s1 \<le> sides_of_rhs (cmb route c ca cc ex) s2"
  assumes extra_sides_mono: "\<forall>v c t s1 s2. t \<in> set (extra route c v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      sides_of_rhs t s1 \<le> sides_of_rhs t s2"
  shows "mono_sides (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g)"
proof -
  have key: "\<And>v c s1 s2. s1 \<le> s2 \<Longrightarrow>
      sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, c)) s1
        \<le> sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, c)) s2"
  proof -
    fix v c s1 s2
    show "s1 \<le> s2 \<Longrightarrow>
        sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, c)) s1
          \<le> sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, c)) s2"
    proof -
      assume le: "s1 \<le> s2"
      have tree_sides_mono: "\<And>w. \<forall>t \<in> set (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w'. (w', c)) (apply_dg_spec S a u)))
                                  (pred_sel g w)
                            @ map (\<lambda>(cc, ca, ex). cmb route c ca cc ex) (return_call_action_list g w)
                            @ extra route c w).
                         \<forall>s1 s2. s1 \<le> s2 \<longrightarrow> sides_of_rhs t s1 \<le> sides_of_rhs t s2"
        using intra_sides_mono comb_sides_mono extra_sides_mono by auto
      have fold_le: "\<And>acc w. sides_of_rhs (side_rhs_fold_dg acc
                        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w'. (w', c)) (apply_dg_spec S a u)))
                            (pred_sel g w)
                          @ map (\<lambda>(cc, ca, ex). cmb route c ca cc ex) (return_call_action_list g w)
                          @ extra route c w)) s1
                    \<le> sides_of_rhs (side_rhs_fold_dg acc
                        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w'. (w', c)) (apply_dg_spec S a u)))
                            (pred_sel g w)
                          @ map (\<lambda>(cc, ca, ex). cmb route c ca cc ex) (return_call_action_list g w)
                          @ extra route c w)) s2"
        by (rule side_rhs_fold_dg_sides_mono[OF tree_sides_mono le])
      show "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, c)) s1
            \<le> sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g (v, c)) s2"
        unfolding side_cfg_T_eff_keyed_seed_dg_def
        by (simp add: Let_def fold_le fun_upd_sup_mono[OF fold_le] split: if_splits)
    qed
  qed
  show ?thesis
    unfolding mono_sides_def using key by fastforce
qed

lemma side_cfg_T_eff_keyed_seed_dg_mono_deps_gen:
  fixes g :: cfg
    and S :: "('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_spec"
  assumes intra_static: "\<forall>v c u a. (u, a) \<in> set (pred_sel g v) \<longrightarrow>
      static_deps (map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u)))"
  assumes comb_static: "\<forall>v c cc ca ex. (cc, ca, ex) \<in> set (return_call_action_list g v) \<longrightarrow>
      static_deps (cmb route c ca cc ex)"
  assumes extra_static: "\<forall>v c t. t \<in> set (extra route c v) \<longrightarrow> static_deps t"
  shows "mono_deps (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g)"
proof -
  have key: "\<And>v c s1 s2.
      dep (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) s1 (v, c)
        \<subseteq> dep (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) s2 (v, c)"
  proof -
    fix v c s1 s2
    have tree_static: "\<And>w. \<forall>t \<in> set (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w'. (w', c)) (apply_dg_spec S a u)))
                                (pred_sel g w)
                          @ map (\<lambda>(cc, ca, ex). cmb route c ca cc ex) (return_call_action_list g w)
                          @ extra route c w).
                       static_deps t"
      using intra_static comb_static extra_static by auto
    have fold_static: "\<And>acc w. static_deps (side_rhs_fold_dg acc
                      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w'. (w', c)) (apply_dg_spec S a u)))
                          (pred_sel g w)
                        @ map (\<lambda>(cc, ca, ex). cmb route c ca cc ex) (return_call_action_list g w)
                        @ extra route c w))"      by (rule side_rhs_fold_dg_static_deps[OF tree_static])
    have deq: "\<And>acc w. dep_aux s1 (side_rhs_fold_dg acc
                  (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w'. (w', c)) (apply_dg_spec S a u)))
                      (pred_sel g w)
                    @ map (\<lambda>(cc, ca, ex). cmb route c ca cc ex) (return_call_action_list g w)
                    @ extra route c w))
                = dep_aux s2 (side_rhs_fold_dg acc
                  (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w'. (w', c)) (apply_dg_spec S a u)))
                      (pred_sel g w)
                    @ map (\<lambda>(cc, ca, ex). cmb route c ca cc ex) (return_call_action_list g w)
                    @ extra route c w))"
      using fold_static[unfolded static_deps_def] by blast
    show "dep (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) s1 (v, c)
            \<subseteq> dep (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g) s2 (v, c)"
      unfolding dep_def side_cfg_T_eff_keyed_seed_dg_def
      by (simp add: Let_def deq split: if_splits)
    qed
  show ?thesis
    unfolding mono_deps_def using key by fastforce
qed

lemma side_cfg_T_eff_keyed_seed_dg_threefold_mono:
  assumes "is_mono_eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g)"
      and "mono_sides (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g)"
      and "mono_deps (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g)"
  shows "threefold_mono (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g)"
  unfolding threefold_mono_def using assms by blast

subsection \<open>TD_side_mono interpretation for an arbitrary generator instance\<close>

text \<open>
  Bundling the nine primitive obligations from the three
  \<open>..._gen\<close> lemmas above as locale assumptions gives a mechanical
  @{locale TD_side_mono} interpretation, hence a least partial post-solution,
  for any @{const side_cfg_T_eff_keyed_seed_dg} instance --- no per-instance
  monotonicity proof is needed, only the nine primitive obligations on the
  concrete \<open>pred_sel\<close>/\<open>cmb\<close>/\<open>extra\<close> hooks.
\<close>

locale td_cfg_side_solver_dg =
  fixes pred_sel :: "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action) list"
    and gkey :: "'c \<Rightarrow> 'k"
    and route :: "pp \<Rightarrow> 'c \<Rightarrow> 'd::bounded_semilattice_sup_bot \<Rightarrow> call_action \<Rightarrow> 'c"
    and cmb :: "(pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
                  \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h::bounded_semilattice_sup_bot) dg_state) strategy_tree"
    and extra :: "(pp \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> pp
                  \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree list"
    and g :: cfg
    and S :: "('d, 'h) dg_spec"
    and bot0 s0d :: 'd and s0g :: 'h
  assumes intra_mono: "\<forall>v c u a s1 s2. (u, a) \<in> set (pred_sel g v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      traverse_rhs (map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u))) s1
        \<le> traverse_rhs (map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u))) s2"
    and comb_mono: "\<forall>v c cc ca ex s1 s2. (cc, ca, ex) \<in> set (return_call_action_list g v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      traverse_rhs (cmb route c ca cc ex) s1 \<le> traverse_rhs (cmb route c ca cc ex) s2"
    and extra_mono: "\<forall>v c t s1 s2. t \<in> set (extra route c v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      traverse_rhs t s1 \<le> traverse_rhs t s2"
    and intra_sides_mono: "\<forall>v c u a s1 s2. (u, a) \<in> set (pred_sel g v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      sides_of_rhs (map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u))) s1
        \<le> sides_of_rhs (map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u))) s2"
    and comb_sides_mono: "\<forall>v c cc ca ex s1 s2. (cc, ca, ex) \<in> set (return_call_action_list g v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      sides_of_rhs (cmb route c ca cc ex) s1 \<le> sides_of_rhs (cmb route c ca cc ex) s2"
    and extra_sides_mono: "\<forall>v c t s1 s2. t \<in> set (extra route c v) \<longrightarrow> s1 \<le> s2 \<longrightarrow>
      sides_of_rhs t s1 \<le> sides_of_rhs t s2"
    and intra_static[intro]: "\<forall>v c u a. (u, a) \<in> set (pred_sel g v) \<longrightarrow>
      static_deps (map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u)))"
    and comb_static[intro]: "\<forall>v c cc ca ex. (cc, ca, ex) \<in> set (return_call_action_list g v) \<longrightarrow>
      static_deps (cmb route c ca cc ex)"
    and extra_static[intro]: "\<forall>v c t. t \<in> set (extra route c v) \<longrightarrow> static_deps t"
begin

definition cfg_pkg_dg :: "(pp \<times> 'c, 'k, ('d, 'h) dg_state) eqsT"
  where "cfg_pkg_dg = side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g"

lemma cfg_pkg_dg_eq[simp]:
  "cfg_pkg_dg = side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g S bot0 s0d s0g"
  unfolding cfg_pkg_dg_def by rule

lemma cfg_pkg_dg_threefold_mono: "threefold_mono cfg_pkg_dg"
proof -
  have eq: "is_mono_eq cfg_pkg_dg"
    unfolding cfg_pkg_dg_def
    apply (rule side_cfg_T_eff_keyed_seed_dg_is_mono_eq_gen)
    apply (rule intra_mono)
    apply (rule comb_mono)
    apply (rule extra_mono)
    done
  have sides: "mono_sides cfg_pkg_dg"
    unfolding cfg_pkg_dg_def
    apply (rule side_cfg_T_eff_keyed_seed_dg_mono_sides_gen)
    apply (rule intra_sides_mono)
    apply (rule comb_sides_mono)
    apply (rule extra_sides_mono)
    done
  have deps: "mono_deps cfg_pkg_dg"
    unfolding cfg_pkg_dg_def
    apply (rule side_cfg_T_eff_keyed_seed_dg_mono_deps_gen)
    apply (rule intra_static)
    apply (rule comb_static)
    apply (rule extra_static)
    done
  show ?thesis
    unfolding threefold_mono_def using eq sides deps by blast
qed

interpretation side: TD_side_mono cfg_pkg_dg
proof (unfold_locales)
  show "is_mono_eq cfg_pkg_dg" using cfg_pkg_dg_threefold_mono unfolding threefold_mono_def by blast
  show "mono_sides cfg_pkg_dg" using cfg_pkg_dg_threefold_mono unfolding threefold_mono_def by blast
  show "mono_deps cfg_pkg_dg" using cfg_pkg_dg_threefold_mono unfolding threefold_mono_def by blast
qed

definition stabl_at :: "pp \<times> 'c \<Rightarrow> (pp \<times> 'c) set"
  where "stabl_at x = fst (side.solve x)"

definition nu_at :: "pp \<times> 'c \<Rightarrow> pp \<times> 'c + 'k \<Rightarrow> ('d, 'h) dg_state"
  where "nu_at x = snd (side.solve x)"

lemma solve_prod: "side.solve x = (stabl_at x, nu_at x)"
  unfolding stabl_at_def nu_at_def by (rule prod_eqI) simp_all

lemma part_post_at:
  assumes dom: "side.solve_dom x"
  shows "part_post_solution cfg_pkg_dg x (nu_at x) (stabl_at x)"
  using side.least_partial_post_solution[OF dom solve_prod] by simp

lemma least_part_post_at:
  assumes dom: "side.solve_dom x"
  shows "least_part_post_solution cfg_pkg_dg x (nu_at x) (stabl_at x)"
  using side.least_partial_post_solution[OF dom solve_prod] by blast

end

text \<open>
  The homogeneous interfaces \\\<^typ>\<open>('g, 'd) edge_tf_tree\<close>,
  \\\<^typ>\<open>('g, 'd) combine_tf_tree\<close>, and
  \\\<^typ>\<open>('g, 'd) effectful_domain_transfer\<close> remain for the homogeneous
  soundness and executable spines.  The heterogeneous generator consumes
  \\\<^typ>\<open>('d, 'h) dg_spec\<close> directly: Answers carry \<open>D\<close>, Side
  publications carry \<open>G\<close>, and only \\\<^typ>\<open>('d, 'h) dg_state\<close> packs
  them for the vendor solver's single value parameter.
\<close>

end
