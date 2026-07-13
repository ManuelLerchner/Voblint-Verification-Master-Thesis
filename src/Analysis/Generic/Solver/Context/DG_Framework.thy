theory DG_Framework
  imports Split_Cmp_Gen
begin

section \<open>The D/G framework core\<close>

text \<open>
  The analysis-agnostic framework boundary, matching Goblint's
  (\<open>analyses.ml\<close>, \<open>module type Spec\<close>): an analysis chooses a flow-sensitive
  local domain \<open>D\<close> and a flow-insensitive global domain \<open>G\<close>; the framework
  transports \<open>Answer : D\<close> and \<open>Side : G\<close> and never copies \<open>G\<close> into \<open>D\<close>.

  Two layers.  \<open>step_edge_tree\<close> is the homogeneous shape (one opaque unknown
  value type), enough to factor the legacy trees into framework shape plus
  analysis step.  \<open>dg_edge_tree\<close> / \<open>dg_combine_tree\<close> are the heterogeneous
  shape: \<open>D\<close> and \<open>G\<close> are two independent opaque types, packed into the one
  solver value type through the componentwise copy lattice \<open>dg_state\<close>
  (local unknowns use the \<open>locals\<close> field, global slots the \<open>globs\<close> field).
  The framework only projects and re-packs these slot fields; it never
  inspects \<open>D\<close> or \<open>G\<close> themselves.
\<close>

subsection \<open>The homogeneous framework edge shape\<close>

text \<open>
  The framework's whole edge obligation.  \<open>'d\<close> is opaque: the tree never inspects
  it, never restricts it, and never copies the global read into the Answer ---
  everything domain-shaped happens inside the analysis's \<open>step\<close>.
\<close>

definition step_edge_tree ::
  "('d \<Rightarrow> 'd \<Rightarrow> 'd \<times> 'd) \<Rightarrow> pp \<Rightarrow> (pp, unit, 'd) strategy_tree"
where
  "step_edge_tree step u =
     QueryL u (\<lambda>d. QueryG () (\<lambda>g.
       Side () (fst (step d g)) (Answer (snd (step d g)))))"

lemma traverse_step_edge_tree:
  "traverse_rhs (step_edge_tree step u) \<sigma> = snd (step (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
  unfolding step_edge_tree_def by simp

lemma sides_step_edge_tree_Inr:
  "sides_of_rhs (step_edge_tree step u) \<sigma> (Inr ()) = fst (step (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
  unfolding step_edge_tree_def by (simp add: Let_def)

lemma sides_step_edge_tree_Inl:
  "sides_of_rhs (step_edge_tree step u) \<sigma> (Inl v) = bot"
  unfolding step_edge_tree_def by (simp add: Let_def)

text \<open>
  The legacy unit tree factors through the framework shape: \<open>unit_step\<close> is the
  base analysis's step (restrict to publish, restrict to answer), and the
  equality is definitional.
\<close>

definition unit_step ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<times> 'a abs_state"
where
  "unit_step f d g = (let res = f (d \<squnion> g) in (restrict_global res, restrict_local res))"

theorem step_edge_tree_unit:
  "step_edge_tree (unit_step f) u = unit_edge_tree f u"
  unfolding step_edge_tree_def unit_step_def unit_edge_tree_def
  by (simp add: Let_def)

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
proof
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

text \<open>Conversions to the Stage-1A pair representation and the homogeneous state.\<close>

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

definition merge_dg :: "('a abs_state, 'a abs_state) dg_state \<Rightarrow> 'a abs_state" where
  "merge_dg d = merge_state (pair_of_dg d)"

definition split_dg :: "'a::bot abs_state \<Rightarrow> ('a abs_state, 'a abs_state) dg_state" where
  "split_dg s = dg_of_pair (split_state s)"

lemma merge_split_dg [simp]: "merge_dg (split_dg s) = s"
  by (simp add: merge_dg_def split_dg_def)

definition wf_dg :: "('l::bot abs_state, 'g::bot abs_state) dg_state \<Rightarrow> bool" where
  "wf_dg d = wf_split (pair_of_dg d)"

lemma wf_dg_split_dg: "wf_dg (split_dg s)"
  by (simp add: wf_dg_def split_dg_def wf_split_split_state)

text \<open>Global slots carry a pure-\<open>G\<close> value embedded with a \<^const>\<open>bot\<close> local part.\<close>

definition emb_glob :: "'g \<Rightarrow> ('l::bot, 'g) dg_state" where
  "emb_glob g = DG bot g"

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
  "('dl::bounded_semilattice_sup_bot \<Rightarrow> 'dl \<Rightarrow> 'dg::bounded_semilattice_sup_bot \<Rightarrow> 'dg \<times> 'dl)
   \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_combine_tree comb cc ex =
     QueryL cc (\<lambda>dc. QueryL ex (\<lambda>de. QueryG () (\<lambda>g.
       Side () (DG bot (fst (comb (locals dc) (locals de) (globs g))))
         (Answer (DG (snd (comb (locals dc) (locals de) (globs g))) bot)))))"

lemma traverse_dg_combine_tree:
  "traverse_rhs (dg_combine_tree comb cc ex) \<tau>
   = DG (snd (comb (locals (\<tau> (Inl cc))) (locals (\<tau> (Inl ex))) (globs (\<tau> (Inr ()))))) bot"
  unfolding dg_combine_tree_def by simp

lemma sides_dg_combine_tree_Inr:
  "sides_of_rhs (dg_combine_tree comb cc ex) \<tau> (Inr ())
   = DG bot (fst (comb (locals (\<tau> (Inl cc))) (locals (\<tau> (Inl ex))) (globs (\<tau> (Inr ())))))"
  unfolding dg_combine_tree_def by (simp add: Let_def)

subsection \<open>The analysis interface: a Goblint-Spec-shaped record\<close>

text \<open>
  What an analysis supplies: one \<open>D \<Rightarrow> G \<Rightarrow> G \<times> D\<close> step per edge action, plus the
  procedure-return combine.  Mirrors Goblint's per-\<open>Spec\<close> transfer functions over
  the analysis's own \<open>D\<close> and \<open>G\<close>.
\<close>

record ('dl, 'dg) dg_spec =
  dgs_nop        :: "'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_assign     :: "vname \<Rightarrow> aexp \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_assume     :: "bexp \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_assume_not :: "bexp \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_enter      :: "'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_combine    :: "'dl \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"

fun dg_spec_step ::
  "('dl, 'dg, 'z) dg_spec_scheme \<Rightarrow> edge_action \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
where
  "dg_spec_step S EA_Nop           = dgs_nop S"
| "dg_spec_step S (EA_Assign x e)  = dgs_assign S x e"
| "dg_spec_step S (EA_Assume b)    = dgs_assume S b"
| "dg_spec_step S (EA_AssumeNot b) = dgs_assume_not S b"
| "dg_spec_step S EA_Enter         = dgs_enter S"

definition apply_dg_spec ::
  "('dl::bounded_semilattice_sup_bot, 'dg::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "apply_dg_spec S a u = dg_edge_tree (dg_spec_step S a) u"

definition dg_spec_combine_tree ::
  "('dl::bounded_semilattice_sup_bot, 'dg::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp, unit, ('dl, 'dg) dg_state) strategy_tree"
where
  "dg_spec_combine_tree S cc ex = dg_combine_tree (dgs_combine S) cc ex"

subsection \<open>Compatibility: the unit analysis on the heterogeneous framework\<close>

text \<open>
  The base (unit) analysis chooses \<open>D = G = 'a abs_state\<close>.  Its spec on the
  heterogeneous framework reproduces the legacy homogeneous trees exactly, under
  the slot embedding \<open>dg_rep_flat\<close> (locals into the \<open>locals\<close> field, the global
  slot into the \<open>globs\<close> field).
\<close>

definition unit_combine_step ::
  "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state
   \<Rightarrow> 'a abs_state \<times> 'a abs_state"
where
  "unit_combine_step dc de g =
     (let res = restrict_local (dc \<squnion> g) \<squnion> restrict_global (de \<squnion> g)
      in (restrict_global res, restrict_local res))"

definition unit_dg_spec ::
  "'a::sound_domain domain_transfer \<Rightarrow> ('a abs_state, 'a abs_state) dg_spec"
where
  "unit_dg_spec tf = \<lparr>
    dgs_nop        = unit_step (apply_tf tf EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step (apply_tf tf (EA_Assign x e))),
    dgs_assume     = (\<lambda>b. unit_step (apply_tf tf (EA_Assume b))),
    dgs_assume_not = (\<lambda>b. unit_step (apply_tf tf (EA_AssumeNot b))),
    dgs_enter      = unit_step (apply_tf tf EA_Enter),
    dgs_combine    = unit_combine_step
  \<rparr>"

lemma dg_spec_step_unit:
  "dg_spec_step (unit_dg_spec tf) a = unit_step (apply_tf tf a)"
  unfolding unit_dg_spec_def by (cases a) simp_all

definition dg_rep_flat ::
  "(pp + unit \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
   \<Rightarrow> pp + unit \<Rightarrow> ('a abs_state, 'a abs_state) dg_state"
where
  "dg_rep_flat \<sigma> =
     (\<lambda>k. case k of Inl v \<Rightarrow> DG (\<sigma> (Inl v)) bot | Inr g \<Rightarrow> emb_glob (\<sigma> (Inr g)))"

theorem unit_dg_spec_traverse:
  "traverse_rhs (apply_dg_spec (unit_dg_spec tf) a u) (dg_rep_flat \<sigma>)
   = DG (traverse_rhs (apply_etf (unit_etf_of_transfer tf) a u) \<sigma>) bot"
  unfolding apply_dg_spec_def dg_rep_flat_def emb_glob_def
  by (simp add: traverse_dg_edge_tree dg_spec_step_unit unit_step_def
        apply_etf_unit_of_transfer traverse_unit_edge_tree Let_def)

theorem unit_dg_spec_sides:
  "sides_of_rhs (apply_dg_spec (unit_dg_spec tf) a u) (dg_rep_flat \<sigma>) (Inr ())
   = emb_glob (sides_of_rhs (apply_etf (unit_etf_of_transfer tf) a u) \<sigma> (Inr ()))"
  unfolding apply_dg_spec_def dg_rep_flat_def emb_glob_def
  by (simp add: sides_dg_edge_tree_Inr dg_spec_step_unit unit_step_def
        apply_etf_unit_of_transfer sides_unit_edge_tree_Inr Let_def)

theorem unit_dg_spec_combine_traverse:
  "traverse_rhs (dg_spec_combine_tree (unit_dg_spec tf) cc ex) (dg_rep_flat \<sigma>)
   = DG (traverse_rhs (unit_combine_tree cc ex) \<sigma>) bot"
  unfolding dg_spec_combine_tree_def unit_dg_spec_def dg_rep_flat_def emb_glob_def
  by (simp add: traverse_dg_combine_tree unit_combine_step_def
        traverse_unit_combine_tree Let_def restrict_local_combine_eq)

theorem unit_dg_spec_combine_sides:
  "sides_of_rhs (dg_spec_combine_tree (unit_dg_spec tf) cc ex) (dg_rep_flat \<sigma>) (Inr ())
   = emb_glob (sides_of_rhs (unit_combine_tree cc ex) \<sigma> (Inr ()))"
  unfolding dg_spec_combine_tree_def unit_dg_spec_def dg_rep_flat_def emb_glob_def
  by (simp add: sides_dg_combine_tree_Inr unit_combine_step_def
        sides_unit_combine_tree_Inr Let_def restrict_global_combine_eq)

text \<open>
  The heterogeneous generator (threading \<^const>\<open>apply_dg_spec\<close> /
  \<^const>\<open>dg_spec_combine_tree\<close> through \<^const>\<open>side_cfg_T_eff_cmp\<close>-style equation
  systems) is the remaining Stage-1D work: \<^typ>\<open>('g, 'd) edge_tf_tree\<close> and the
  \<^typ>\<open>('g, 'd) effectful_domain_transfer\<close> record bake the value type
  \<open>'d abs_state\<close>, so the record-consuming generator layer needs its value type
  generalized before dg-valued trees can drive it.  The tree layer above is
  value-generic already.
\<close>

end
