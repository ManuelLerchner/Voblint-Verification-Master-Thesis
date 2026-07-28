theory DG_Framework
  imports "Voblint_Analysis.Exec_Bridge" "Voblint_Analysis.TD_Side_Eff_Keyed_Gen"
begin

section \<open>The D/G framework core\<close>

text \<open>An analysis chooses a flow-sensitive answer domain \<open>D\<close> and a
  flow-insensitive side-effect domain \<open>G\<close>. The framework keeps them opaque and stores
  them in separate components of \<open>dg_state\<close>; it never copies a global component
  into a local answer.

  \<open>dg_edge_tree\<close> and \<open>dg_combine_tree\<close> only project and repack those
  components, so their construction is independent of the concrete domains.\<close>



definition unit_step ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<times> 'a abs_state"
where
  "unit_step f d g = (let res = f (d \<squnion> g) in (restrict_global res, restrict_local res))"



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
    (auto simp: widen_dg_state_def narrow_dg_state_def less_eq_dg_state_def
      intro: widen_ge1 widen_ge2 narrow_ge narrow_le)

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
  \<open>combine_assign_abs\<close> can, so both halves are analysis-supplied.\<close>

record ('dl, 'dg) dg_spec =
  dgs_nop        :: "'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
  dgs_assign     :: "vname \<Rightarrow> aexp \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl"
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
| "dg_spec_step S (EA_Assume b)    = dgs_assume S b"
| "dg_spec_step S (EA_AssumeNot b) = dgs_assume_not S b"
| "dg_spec_step S (EA_Ret e p) =
     (case e of None \<Rightarrow> dgs_nop S | Some a \<Rightarrow> dgs_assign S ret_var a)"

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

text \<open>The unit env-merge computes the structural local/global merge and
  packages it the same way \<^const>\<open>unit_step\<close> packages every other edge, but
  writes no return value yet.  The unit assign reconstitutes the full state
  from that packaging, writes the callee-exit's return slot, and re-splits --
  matching \<^const>\<open>combine_collect_abs\<close> exactly once composed.\<close>
definition unit_combine_step_env ::
  "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state
   \<Rightarrow> 'a abs_state \<times> 'a abs_state"
where
  "unit_combine_step_env dc de g =
     (let m = combine_abs (dc \<squnion> g) (de \<squnion> g) in (restrict_global m, restrict_local m))"

definition unit_combine_step_assign ::
  "vname option \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state
   \<Rightarrow> 'a abs_state \<times> 'a abs_state \<Rightarrow> 'a abs_state \<times> 'a abs_state"
where
  "unit_combine_step_assign dst de g merged =
     (let res = combine_assign_abs dst ((de \<squnion> g) ret_var) (fst merged \<squnion> snd merged)
      in (restrict_global res, restrict_local res))"

definition unit_dg_spec ::
  "'a::sound_domain domain_transfer \<Rightarrow> ('a abs_state, 'a abs_state) dg_spec"
where
  "unit_dg_spec tf = \<lparr>
    dgs_nop        = unit_step (apply_tf tf EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step (apply_tf tf (EA_Assign x e))),
    dgs_assume     = (\<lambda>b. unit_step (apply_tf tf (EA_Assume b))),
    dgs_assume_not = (\<lambda>b. unit_step (apply_tf tf (EA_AssumeNot b))),
    dgs_enter      = (\<lambda>xs es. unit_step (tf_enter tf xs es)),
    dgs_combine_env    = unit_combine_step_env,
    dgs_combine_assign = unit_combine_step_assign
  \<rparr>"

text \<open>The pre-split combine value is recovered by composition, matching
  \<^const>\<open>combine_collect_abs\<close> exactly -- the split changes packaging, not
  the computed answer.\<close>
lemma dgs_combine_unit_dg_spec:
  "dgs_combine (unit_dg_spec tf) dst dc de g =
     (let res = combine_collect_abs dst (dc \<squnion> g) (de \<squnion> g)
      in (restrict_global res, restrict_local res))"
proof -
  have join_back: "restrict_global \<langle>dc \<squnion> g|de \<squnion> g\<rangle> \<squnion> restrict_local \<langle>dc \<squnion> g|de \<squnion> g\<rangle>
                    = \<langle>dc \<squnion> g|de \<squnion> g\<rangle>"
    using restrict_local_global_join by (simp add: sup.commute)
  show ?thesis
    unfolding dgs_combine_def unit_dg_spec_def unit_combine_step_env_def
      unit_combine_step_assign_def combine_collect_abs_def Let_def
    by (simp add: join_back)
qed

lemma dg_spec_step_unit:
  "dg_spec_step (unit_dg_spec tf) a = unit_step (apply_tf tf a)"
  unfolding unit_dg_spec_def
  by (cases a)
     (simp_all add: apply_tf_EA_Ret_None apply_tf_EA_Ret_Some split: option.splits)



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
