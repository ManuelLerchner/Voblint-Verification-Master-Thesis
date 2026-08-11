theory DG_Framework
  imports Exec_Bridge TD_Side_Eff_Keyed_Gen
    TD_Side_Eff_Pipeline
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
     (let res = f (combine_env\<^sup># gs d g) in
      (restrict_global_for gs res, restrict_local_for gs res))"

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
     QueryL u (\<lambda>d. QueryG () (\<lambda>g.
       Side () (DG bot (fst (step (locals d) (globs g))))
         (Answer (DG (snd (step (locals d) (globs g)))  bot))))"

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

text \<open>Procedure-return combine: two \<open>D\<close> inputs (caller, callee exit), one \<open>G\<close>.\<close>

definition dg_combine_tree ::
  "(vname option \<Rightarrow> 'dl::bounded_semilattice_sup_bot \<Rightarrow> 'dl \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_combine_tree comb dst cc ex =
     QueryL cc (\<lambda>dc. QueryL ex (\<lambda>de. QueryG () (\<lambda>g.
       Side () (DG bot (fst (comb dst (locals dc) (locals de) (globs g))))
         (Answer (DG (snd (comb dst (locals dc) (locals de) (globs g))) bot)))))"

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
  dgs_nop        :: "'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_assign     :: "vname \<Rightarrow> aexp \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_random     :: "vname \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_assume     :: "bexp \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_assume_not :: "bexp \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_enter      :: "vname list \<Rightarrow> aexp list \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_combine_env    :: "'dl \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_combine_assign :: "vname option \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl \<Rightarrow> 'dg \<times> 'dl"

text \<open>The composed combine, in the pre-split curried shape every existing
  caller already uses fully applied (\<open>dgs_combine S dst dc de g\<close>).  Kept as
  a plain definition, not a record field, so the split above is the single
  source of truth and this cannot drift out of sync with it.\<close>
definition dgs_combine ::
  "('dl, 'dg) dg_spec \<Rightarrow> vname option \<Rightarrow> 'dl \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
where
  "dgs_combine S dst dc de g = dgs_combine_assign S dst de g (dgs_combine_env S dc de g)"

fun dg_spec_step ::
  "('dl, 'dg, 'z) dg_spec_scheme \<Rightarrow> edge_action \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
where
  "dg_spec_step S EA_Nop           = dgs_nop S"
| "dg_spec_step S (EA_Assign x e)  = dgs_assign S x e"
| "dg_spec_step S (EA_Random x)    = dgs_random S x"
| "dg_spec_step S (EA_Assume b)    = dgs_assume S b"
| "dg_spec_step S (EA_AssumeNot b) = dgs_assume_not S b"
| "dg_spec_step S (EA_Ret e p) =
     (case e of None \<Rightarrow> dgs_nop S | Some a \<Rightarrow> dgs_assign S ret_var a)"
| "dg_spec_step S (EA_Check cnd) = dgs_nop S"

definition apply_dg_spec ::
  "('dl::bounded_semilattice_sup_bot, 'dg::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "apply_dg_spec S a u = dg_edge_tree (dg_spec_step S a) u"

definition dg_spec_combine_tree ::
  "('dl::bounded_semilattice_sup_bot, 'dg::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_spec_combine_tree S dst cc ex = dg_combine_tree (dgs_combine S) dst cc ex"

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
   vname option => 'a::bounded_semilattice_sup_bot abs_state
   => 'a abs_state => 'a abs_state \<times> 'a abs_state
   => 'a abs_state \<times> 'a abs_state"
where
  "unit_combine_step_assign_for gs dst de g merged =
     (let res = combine_assign\<^sup># dst (de ret_var)
         (fst merged \<squnion> snd merged)
      in (restrict_global_for gs res, restrict_local_for gs res))"


definition unit_combine_step_env_for ::
  "(vname => bool) =>
   'a::bounded_semilattice_sup_bot abs_state => 'a abs_state
   => 'a abs_state => 'a abs_state \<times> 'a abs_state" where
  "unit_combine_step_env_for gs dc de g =
     (let m = combine_env\<^sup># gs dc g
      in (restrict_global_for gs m, restrict_local_for gs m))"

definition unit_combine_step_env_placed ::
  "(vname => bool) => (vname => bool) => (vname => bool) =>
   'a::bounded_semilattice_sup_bot abs_state => 'a abs_state =>
   'a abs_state => 'a abs_state \<times> 'a abs_state"
where
  "unit_combine_step_env_placed source_global keep_local publish_side dc de g =
     (let res = combine_env\<^sup># source_global (dc \<squnion> g) (de \<squnion> g) in
      (project_component publish_side res, project_component keep_local res))"


definition unit_combine_step_assign_placed ::
  "(vname => bool) => (vname => bool) => vname option =>
   'a::bounded_semilattice_sup_bot abs_state => 'a abs_state =>
   'a abs_state \<times> 'a abs_state => 'a abs_state \<times> 'a abs_state"
where
  "unit_combine_step_assign_placed keep_local publish_side dst de g merged =
     (let res = combine_assign\<^sup># dst ((de \<squnion> g) ret_var)
         (fst merged \<squnion> snd merged)
      in (project_component publish_side res, project_component keep_local res))"


definition unit_dg_spec_placed ::
  "(vname => bool) => (vname => bool) => (vname => bool) =>
   'a::sound_domain domain_transfer => ('a abs_state, 'a abs_state) dg_spec"
where
  "unit_dg_spec_placed source_global keep_local publish_side tf = \<lparr>
    dgs_nop        = unit_step_placed keep_local publish_side (apply_tf tf EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step_placed keep_local publish_side
      (apply_tf tf (EA_Assign x e))),
    dgs_random     = (\<lambda>x. unit_step_placed keep_local publish_side
      (apply_tf tf (EA_Random x))),
    dgs_assume     = (\<lambda>b. unit_step_placed keep_local publish_side
      (apply_tf tf (EA_Assume b))),
    dgs_assume_not = (\<lambda>b. unit_step_placed keep_local publish_side
      (apply_tf tf (EA_AssumeNot b))),
    dgs_enter      = (\<lambda>xs es. unit_step_placed keep_local publish_side
      (enter\<^sup># tf xs es)),
    dgs_combine_env = unit_combine_step_env_placed source_global keep_local publish_side,
    dgs_combine_assign = unit_combine_step_assign_placed keep_local publish_side
  \<rparr>"
lemma dg_spec_step_unit_placed:
  "dg_spec_step (unit_dg_spec_placed source_global keep_local publish_side tf) a =
    unit_step_placed keep_local publish_side (apply_tf tf a)"
  unfolding unit_dg_spec_placed_def
  by (cases a)
     (simp_all add: apply_tf_EA_Ret_None apply_tf_EA_Ret_Some apply_tf_EA_Check
       split: option.splits)

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
    dgs_nop        = unit_step_for gs (apply_tf tf EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step_for gs (apply_tf tf (EA_Assign x e))),
    dgs_random     = (\<lambda>x. unit_step_for gs (apply_tf tf (EA_Random x))),
    dgs_assume     = (\<lambda>b. unit_step_for gs (apply_tf tf (EA_Assume b))),
    dgs_assume_not = (\<lambda>b. unit_step_for gs (apply_tf tf (EA_AssumeNot b))),
    dgs_enter      = (\<lambda>xs es. unit_step_for gs (enter\<^sup># tf xs es)),
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
  "dgs_combine (unit_dg_spec_for gs tf) dst dc de g =
     (let res = combine_assign\<^sup># dst (de ret_var) (combine_env\<^sup># gs dc g)
      in (restrict_global_for gs res, restrict_local_for gs res))"
proof -
  have env:
    "fst (unit_combine_step_env_for gs dc de g) \<squnion>
       snd (unit_combine_step_env_for gs dc de g) =
     combine_env\<^sup># gs dc g"
    unfolding unit_combine_step_env_for_def
    by (simp add: Let_def restrict_global_for_local_join)
  show ?thesis
    unfolding dgs_combine_def unit_dg_spec_for_def
      unit_combine_step_assign_for_def Let_def
    by (simp add: env)
qed

lemma dg_spec_step_unit_for:
  "dg_spec_step (unit_dg_spec_for gs tf) a =
     unit_step_for gs (apply_tf tf a)"
  unfolding unit_dg_spec_for_def
  by (cases a)
     (simp_all add: apply_tf_EA_Ret_None apply_tf_EA_Ret_Some apply_tf_EA_Check
       split: option.splits)

lemma dgs_enter_unit_dg_spec_for:
  "dgs_enter (unit_dg_spec_for gs tf) fs as =
     unit_step_for gs (enter\<^sup># tf fs as)"
  unfolding unit_dg_spec_for_def
  by simp


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
      in if v = cfg_entry g then Side (gkey ctx) (DG bot s0g) tree else tree)"

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
        in if v = cfg_entry g then Side (gkey c) (DG bot s0g) t else t)"

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

subsection \<open>Threefold monotonicity for an arbitrary generator instance\<close>

text \<open>
  Mirrors @{thm td_cfg_side_solver_eff_gen} for the flat generator: the three
  @{const TD_side_mono} preconditions reduce to a per-tree contract on the
  intra, combine, and extra hooks, discharged once here and reusable at every
  routing policy --- a routed context policy is then a second interpretation
  of this reduction, not a second monotonicity proof. The outer @{const Side}
  wrapper at @{term "cfg_entry g"} is invisible to @{const traverse_rhs} and
  @{const dep_aux} (a \<^const>\<open>Side\<close> node only ever repackages, never queries);
  it only has to be threaded through the @{const sides_of_rhs} case via
  @{thm fun_upd_sup_mono}, mirroring @{thm side_cfg_T_eff_mono_sides_gen}.
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
  Mirrors @{const td_cfg_side_solver_eff} (\<^theory>\<open>Voblint_Core.TD_Side_Eff_Interface\<close>)
  for the flat generator: bundling the nine primitive obligations from the three
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
