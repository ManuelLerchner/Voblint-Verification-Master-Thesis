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

lemma split_dg_bot [simp]:
  "split_dg (bot :: 'a::bounded_semilattice_sup_bot abs_state) = bot"
  by (simp add: split_dg_def dg_of_pair_def split_state_bot bot_dg_state_def)

lemma split_dg_sup [simp]:
  fixes a b :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "split_dg (a \<squnion> b) = split_dg a \<squnion> split_dg b"
proof -
  have sp: "split_state (a \<squnion> b) =
      (fst (split_state a) \<squnion> fst (split_state b),
       snd (split_state a) \<squnion> snd (split_state b))"
    by (rule split_state_sup)
  show ?thesis
    unfolding split_dg_def dg_of_pair_def sup_dg_state_def
    by (simp add: sp)
qed

lemma split_dg_le_iff [simp]:
  fixes a b :: "'a::order_bot abs_state"
  shows "split_dg a \<le> split_dg b \<longleftrightarrow> a \<le> b"
  by (auto simp: split_dg_def dg_of_pair_def split_state_def
        less_eq_dg_state_def le_fun_def split: if_splits)

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

subsection \<open>Tree packing and homogeneous compatibility\<close>

definition dg_env ::
  "('x + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot)
   \<Rightarrow> 'x + 'g \<Rightarrow> ('a, 'a) dg_state"
where
  "dg_env \<sigma> =
     (\<lambda>k. case k of Inl x \<Rightarrow> DG (\<sigma> (Inl x)) bot
                      | Inr g \<Rightarrow> DG bot (\<sigma> (Inr g)))"

primrec pack_dg_tree ::
  "('x, 'g, 'a::bounded_semilattice_sup_bot) strategy_tree
   \<Rightarrow> ('x, 'g, ('a, 'a) dg_state) strategy_tree"
where
  "pack_dg_tree (Answer d) = Answer (DG d bot)"
| "pack_dg_tree (QueryL x f) =
     QueryL x (\<lambda>d. pack_dg_tree (f (locals d)))"
| "pack_dg_tree (QueryG g f) =
     QueryG g (\<lambda>d. pack_dg_tree (f (globs d)))"
| "pack_dg_tree (Side g d t) =
     Side g (DG bot d) (pack_dg_tree t)"

lemma dg_env_Inl [simp]: "dg_env \<sigma> (Inl x) = DG (\<sigma> (Inl x)) bot"
  by (simp add: dg_env_def)

lemma dg_env_Inr [simp]: "dg_env \<sigma> (Inr g) = DG bot (\<sigma> (Inr g))"
  by (simp add: dg_env_def)

lemma DG_local_le_iff [simp]:
  "DG a (bot :: 'g::order_bot) \<le> DG b bot \<longleftrightarrow> a \<le> b"
  by (simp add: less_eq_dg_state_def)

lemma dg_env_le_iff [simp]:
  "dg_env \<sigma> \<le> dg_env \<tau> \<longleftrightarrow> \<sigma> \<le> \<tau>"
proof
  assume le: "dg_env \<sigma> \<le> dg_env \<tau>"
  show "\<sigma> \<le> \<tau>"
  proof (unfold le_fun_def, intro allI)
    fix x
    have "dg_env \<sigma> x \<le> dg_env \<tau> x"
      using le unfolding le_fun_def by blast
    then show "\<sigma> x \<le> \<tau> x"
      by (cases x) (simp_all add: less_eq_dg_state_def)
  qed
next
  assume le: "\<sigma> \<le> \<tau>"
  show "dg_env \<sigma> \<le> dg_env \<tau>"
  proof (unfold le_fun_def, intro allI)
    fix x
    have "\<sigma> x \<le> \<tau> x" using le unfolding le_fun_def by blast
    then show "dg_env \<sigma> x \<le> dg_env \<tau> x"
      by (cases x) (simp_all add: less_eq_dg_state_def)
  qed
qed

lemma pack_dg_tree_seqcomp:
  "pack_dg_tree (seqcomp_tree t f) =
   seqcomp_tree (pack_dg_tree t) (\<lambda>d. pack_dg_tree (f (locals d)))"
  by (induction t arbitrary: f) simp_all

lemma pack_dg_tree_map_ltree:
  "pack_dg_tree (map_ltree h t) = map_ltree h (pack_dg_tree t)"
  by (induction t) simp_all

lemma pack_dg_tree_map_gtree:
  "pack_dg_tree (map_gtree h t) = map_gtree h (pack_dg_tree t)"
  by (induction t) simp_all

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

lemma pack_dg_tree_fold:
  "pack_dg_tree (side_rhs_fold_ctx acc ts) =
   side_rhs_fold_dg acc (map pack_dg_tree ts)"
  by (induction ts arbitrary: acc) (simp_all add: pack_dg_tree_seqcomp)

lemma traverse_rhs_pack_dg_tree:
  "traverse_rhs (pack_dg_tree t) (dg_env \<sigma>) =
   DG (traverse_rhs t \<sigma>) bot"
  by (induction t) simp_all

lemma sides_of_rhs_Inl_any [simp]:
  "sides_of_rhs t \<sigma> (Inl x) = bot"
  by (induction t) (simp_all add: Let_def)

lemma locals_sides_of_rhs_pack_dg_tree [simp]:
  "locals (sides_of_rhs (pack_dg_tree t) (dg_env \<sigma>) k) = bot"
  by (induction t arbitrary: k)
    (auto simp: Let_def sup_dg_state_def bot_dg_state_def split: sum.splits)

lemma globs_sides_of_rhs_pack_dg_tree [simp]:
  "globs (sides_of_rhs (pack_dg_tree t) (dg_env \<sigma>) k) =
   sides_of_rhs t \<sigma> k"
  by (induction t arbitrary: k)
    (auto simp: Let_def sup_dg_state_def bot_dg_state_def split: sum.splits)

lemma sides_of_rhs_pack_dg_tree:
  "sides_of_rhs (pack_dg_tree t) (dg_env \<sigma>) =
   dg_env (sides_of_rhs t \<sigma>)"
  unfolding fun_eq_iff
proof (intro allI)
  fix k
  show "sides_of_rhs (pack_dg_tree t) (dg_env \<sigma>) k =
        dg_env (sides_of_rhs t \<sigma>) k"
    by (cases k; rule dg_state.expand)
      (simp_all add: bot_dg_state_def)
qed

lemma dep_aux_pack_dg_tree:
  "dep_aux (dg_env \<sigma>) (pack_dg_tree t) = dep_aux \<sigma> t"
  by (induction t) simp_all

lemma part_post_solution_pack_dg_iff:
  "part_post_solution (\<lambda>x. pack_dg_tree (T x)) x (dg_env \<sigma>) vars
   \<longleftrightarrow> part_post_solution T x \<sigma> vars"
  by (simp add: dep_aux_pack_dg_tree traverse_rhs_pack_dg_tree
        sides_of_rhs_pack_dg_tree dep\<^sub>L_def dep_def)

lemma part_solution_pack_dg_iff:
  "part_solution (\<lambda>x. pack_dg_tree (T x)) x (dg_env \<sigma>) vars
   \<longleftrightarrow> part_solution T x \<sigma> vars"
  by (simp add: dep_aux_pack_dg_tree traverse_rhs_pack_dg_tree
        sides_of_rhs_pack_dg_tree dep\<^sub>L_def dep_def)

subsection \<open>The heterogeneous seeded CMP generator\<close>

definition side_cfg_T_eff_cmp_seed_dg ::
  "('c \<Rightarrow> 'k)
   \<Rightarrow> ('c \<Rightarrow> pp \<Rightarrow> pp
        \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) strategy_tree)
   \<Rightarrow> ('c \<Rightarrow> 'd)
   \<Rightarrow> cfg
   \<Rightarrow> ('d::bounded_semilattice_sup_bot, 'h::bounded_semilattice_sup_bot) dg_spec
   \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'h
   \<Rightarrow> (pp \<times> 'c, 'k, ('d, 'h) dg_state) eqsT"
where
  "side_cfg_T_eff_cmp_seed_dg gkey cmb frame_seed g S bot0 s0d s0g =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)
                   \<squnion> (if is_frame_entry g v then frame_seed c else bot);
            intra = map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c)
                            (map_ltree (\<lambda>w. (w, c)) (apply_dg_spec S a u)))
                        (non_enter_predecessor_list g v);
            comb = map (\<lambda>(cc, ex). cmb c cc ex)
                       (combine_predecessor_list g v);
            t = side_rhs_fold_dg acc0 (intra @ comb)
        in if v = cfg_entry g then Side (gkey c) (DG bot s0g) t else t)"

lemma eq_side_cfg_T_eff_cmp_seed_dg:
  "eq (side_cfg_T_eff_cmp_seed_dg gkey cmb frame_seed g S bot0 s0d s0g)
      (v, ctx) \<tau> =
   DG (side_acc_dg
     ((if v = cfg_entry g then bot0 \<squnion> s0d else bot0)
      \<squnion> (if is_frame_entry g v then frame_seed ctx else bot))
     \<tau>
     (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u)))
           (non_enter_predecessor_list g v)
      @ map (\<lambda>(cc, ex). cmb ctx cc ex)
            (combine_predecessor_list g v))) bot"
  by (simp add: side_cfg_T_eff_cmp_seed_dg_def Let_def
        traverse_side_rhs_fold_dg)

lemma apply_unit_dg_spec_pack:
  "apply_dg_spec (unit_dg_spec tf) a u =
   pack_dg_tree (apply_etf (unit_etf_of_transfer tf) a u)"
  unfolding apply_dg_spec_def apply_etf_unit_of_transfer
    dg_spec_step_unit dg_edge_tree_def unit_step_def unit_edge_tree_def
  by (simp add: Let_def fun_eq_iff)

lemma combine_unit_dg_spec_pack:
  "dg_spec_combine_tree (unit_dg_spec tf) cc ex =
   pack_dg_tree (unit_combine_tree cc ex)"
  unfolding dg_spec_combine_tree_def unit_dg_spec_def dg_combine_tree_def
    unit_combine_step_def unit_combine_tree_def
  by (simp add: Let_def fun_eq_iff)

lemma map_pack_dg_tree_routed:
  "map (\<lambda>(u, a). map_gtree gh (map_ltree lh (pack_dg_tree (et a u)))) xs =
   map pack_dg_tree
     (map (\<lambda>(u, a). map_gtree gh (map_ltree lh (et a u))) xs)"
  by (induction xs)
    (auto simp: pack_dg_tree_map_ltree pack_dg_tree_map_gtree split: prod.splits)

lemma map_pack_dg_tree_combine:
  "map (\<lambda>(cc, ex). pack_dg_tree (cmb cc ex)) xs =
   map pack_dg_tree (map (\<lambda>(cc, ex). cmb cc ex) xs)"
  by (induction xs) (auto split: prod.splits)
theorem side_cfg_T_eff_cmp_seed_dg_unit:
  assumes cmb:
    "\<And>c cc ex. cmb_dg c cc ex = pack_dg_tree (cmb c cc ex)"
  shows
    "side_cfg_T_eff_cmp_seed_dg gkey cmb_dg frame_seed g
       (unit_dg_spec tf) bot0 (restrict_local s0) (restrict_global s0)
     = (\<lambda>x. pack_dg_tree
          (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g
             (unit_etf_of_transfer tf) bot0 s0 x))"
  unfolding fun_eq_iff
  apply (intro allI)
  subgoal for x
    by (cases x)
      (simp add: side_cfg_T_eff_cmp_seed_dg_def side_cfg_T_eff_cmp_seed_def
        Let_def apply_unit_dg_spec_pack cmb pack_dg_tree_fold
        map_pack_dg_tree_routed map_pack_dg_tree_combine
        split: prod.splits)
  done

corollary part_post_solution_dg_unit_iff:
  assumes cmb:
    "\<And>c cc ex. cmb_dg c cc ex = pack_dg_tree (cmb c cc ex)"
  shows
    "part_post_solution
       (side_cfg_T_eff_cmp_seed_dg gkey cmb_dg frame_seed g
          (unit_dg_spec tf) bot0 (restrict_local s0) (restrict_global s0))
       x (dg_env \<sigma>) vars
     \<longleftrightarrow>
     part_post_solution
       (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g
          (unit_etf_of_transfer tf) bot0 s0)
       x \<sigma> vars"
proof -
  note gen = side_cfg_T_eff_cmp_seed_dg_unit[OF cmb]
  show ?thesis
    unfolding gen
    by (rule part_post_solution_pack_dg_iff)
qed

text \<open>
  The legacy aliases \\\<^typ>\<open>('g, 'd) edge_tf_tree\<close>,
  \\\<^typ>\<open>('g, 'd) combine_tf_tree\<close>, and
  \\\<^typ>\<open>('g, 'd) effectful_domain_transfer\<close> remain for the homogeneous
  soundness and executable spines.  The heterogeneous generator consumes
  \\\<^typ>\<open>('d, 'h) dg_spec\<close> directly: Answers carry \<open>D\<close>, Side
  publications carry \<open>G\<close>, and only \\\<^typ>\<open>('d, 'h) dg_state\<close> packs
  them for the vendor solver's single value parameter.
\<close>

end
