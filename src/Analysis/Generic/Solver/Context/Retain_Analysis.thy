theory Retain_Analysis
  imports Split_Cmp_Gen
begin

section \<open>Retain as an analysis, not a framework strategy\<close>

text \<open>
  Goblint's framework (\<open>analyses.ml\<close>, \<open>module type Spec\<close>) exposes two
  analysis-chosen domains: the flow-sensitive local domain \<open>D\<close> and the
  flow-insensitive global domain \<open>G\<close> (read via \<open>ctx.global\<close>, written via
  \<open>ctx.sideg\<close>).  The framework transports \<open>Answer : D\<close> and \<open>Side : G\<close> and never
  copies \<open>G\<close> into \<open>D\<close>; an analysis that wants a flow-sensitive snapshot of
  global information stores that snapshot inside its own \<open>D\<close>.

  This theory realizes that boundary.  \<^emph>\<open>Framework\<close>: \<open>step_edge_tree\<close> is the
  value-opaque edge shape --- query the local unknown and the global slot, hand
  both to an analysis-provided step function, transport its Side publication and
  its Answer.  \<^emph>\<open>Analyses\<close>: \<open>unit_step\<close> and \<open>retain_step\<close> recover
  \<^const>\<open>unit_edge_tree\<close> and \<^const>\<open>retain_edge_tree\<close> as two step functions ---
  retain is an analysis choice of what its Answer carries, not a framework
  strategy.  The Goblint-faithful retain analysis then chooses
  \<open>D = locals \<times> global snapshot\<close> (\<open>retain_dg_step\<close> over \<open>dg_state\<close>); the
  Stage-1A isomorphism proves it reproduces the homogeneous retain semantics
  unchanged.
\<close>

subsection \<open>The framework edge shape\<close>

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

subsection \<open>Unit and retain as analysis steps\<close>

text \<open>
  The same framework tree, two analysis steps.  The steps differ only in what the
  analysis decides its Answer carries: \<open>unit_step\<close> answers the local restriction,
  \<open>retain_step\<close> answers the full result (its \<open>D\<close> keeps the written globals).
\<close>

definition unit_step ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<times> 'a abs_state"
where
  "unit_step f d g = (let res = f (d \<squnion> g) in (restrict_global res, restrict_local res))"

definition retain_step ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<times> 'a abs_state"
where
  "retain_step f d g = (let res = f (d \<squnion> g) in (restrict_global res, res))"

theorem step_edge_tree_unit:
  "step_edge_tree (unit_step f) u = unit_edge_tree f u"
  unfolding step_edge_tree_def unit_step_def unit_edge_tree_def
  by (simp add: Let_def)

theorem step_edge_tree_retain:
  "step_edge_tree (retain_step f) u = retain_edge_tree f u"
  unfolding step_edge_tree_def retain_step_def retain_edge_tree_def
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

subsection \<open>The Goblint-faithful retain analysis: D = locals x snapshot\<close>

text \<open>
  The retain analysis's own domain choice: \<open>D = ('a abs_state, 'a abs_state) dg_state\<close>,
  locals in the first component, the flow-sensitive global snapshot in the
  second.  Global slots carry a pure-\<open>G\<close> value embedded with a \<^const>\<open>bot\<close>
  local part.
\<close>

definition emb_glob :: "'g \<Rightarrow> ('l::bot, 'g) dg_state" where
  "emb_glob g = DG bot g"

text \<open>
  The analysis step: read the snapshot-carrying \<open>D\<close> and the global slot, run the
  transfer on their join, publish the global restriction, answer the split result
  --- the snapshot in the Answer is written by the analysis itself, not by the
  framework.
\<close>

definition retain_dg_step ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> ('a abs_state, 'a abs_state) dg_state
   \<Rightarrow> ('a abs_state, 'a abs_state) dg_state
   \<Rightarrow> ('a abs_state, 'a abs_state) dg_state \<times> ('a abs_state, 'a abs_state) dg_state"
where
  "retain_dg_step f d g =
     (let res = f (merge_dg d \<squnion> globs g)
      in (emb_glob (restrict_global res), split_dg res))"

definition retain_dg_edge_tree ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> pp \<Rightarrow> (pp, unit, ('a abs_state, 'a abs_state) dg_state) strategy_tree"
where
  "retain_dg_edge_tree f u = step_edge_tree (retain_dg_step f) u"

text \<open>Slot discipline, for every assignment: Answers are well-split, Side
  publications carry no local part.  The analysis cannot smuggle locals into
  \<open>G\<close> or mislabel its own slots.\<close>

lemma retain_dg_traverse_wf:
  "wf_dg (traverse_rhs (retain_dg_edge_tree f u) \<tau>)"
  unfolding retain_dg_edge_tree_def retain_dg_step_def
  by (simp add: traverse_step_edge_tree Let_def wf_dg_split_dg)

lemma retain_dg_sides_locals_bot:
  "locals (sides_of_rhs (retain_dg_edge_tree f u) \<tau> (Inr ())) = bot"
  unfolding retain_dg_edge_tree_def retain_dg_step_def emb_glob_def
  by (simp add: sides_step_edge_tree_Inr Let_def)

subsection \<open>The retain analysis reproduces the homogeneous retain semantics\<close>

text \<open>
  Assignments of the homogeneous retain system map to \<open>dg_state\<close> assignments by
  splitting local unknowns and embedding the global slot.
\<close>

definition dg_rep ::
  "(pp + unit \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
   \<Rightarrow> pp + unit \<Rightarrow> ('a abs_state, 'a abs_state) dg_state"
where
  "dg_rep \<sigma> =
     (\<lambda>k. case k of Inl v \<Rightarrow> split_dg (\<sigma> (Inl v)) | Inr g \<Rightarrow> emb_glob (\<sigma> (Inr g)))"

theorem retain_dg_traverse:
  "traverse_rhs (retain_dg_edge_tree f u) (dg_rep \<sigma>)
   = split_dg (traverse_rhs (retain_edge_tree f u) \<sigma>)"
  unfolding retain_dg_edge_tree_def retain_dg_step_def dg_rep_def emb_glob_def
  by (simp add: traverse_step_edge_tree traverse_retain_edge_tree Let_def)

corollary retain_dg_traverse_merge:
  "merge_dg (traverse_rhs (retain_dg_edge_tree f u) (dg_rep \<sigma>))
   = traverse_rhs (retain_edge_tree f u) \<sigma>"
  by (simp add: retain_dg_traverse)

theorem retain_dg_sides_Inr:
  "sides_of_rhs (retain_dg_edge_tree f u) (dg_rep \<sigma>) (Inr ())
   = emb_glob (sides_of_rhs (retain_edge_tree f u) \<sigma> (Inr ()))"
  unfolding retain_dg_edge_tree_def retain_dg_step_def dg_rep_def emb_glob_def
  by (simp add: sides_step_edge_tree_Inr sides_retain_edge_tree_Inr Let_def)

corollary retain_dg_sides_Inr_globs:
  "globs (sides_of_rhs (retain_dg_edge_tree f u) (dg_rep \<sigma>) (Inr ()))
   = sides_of_rhs (retain_edge_tree f u) \<sigma> (Inr ())"
  by (simp add: retain_dg_sides_Inr emb_glob_def)

text \<open>
  Together: under the Stage-1A isomorphism the \<open>dg_state\<close> retain analysis and the
  homogeneous \<^const>\<open>retain_edge_tree\<close> have identical evaluation and identical
  global publications.  Retiring the generic retain tree is therefore a typing
  migration (this analysis's \<open>D\<close> instead of \<open>'a abs_state\<close> unknowns), not a
  semantic change; the sequencing lives in \<open>docs/SPLIT_STATE_MIGRATION.md\<close>.
\<close>

end
