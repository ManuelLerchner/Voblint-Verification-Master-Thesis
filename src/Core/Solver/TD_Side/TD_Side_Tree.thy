theory TD_Side_Tree
  imports TD_Side_CFG "Voblint_CFG.CFG_Transfer" Strategy_Tree_Monad
begin

section \<open>Side IP solver: constraint system construction and denotation\<close>

text \<open>
  Each equation right-hand side folds three contribution families: ordinary
  CFG edges, procedure-entry transfers, and return/combine transfers.  The
  accumulator joins their local results, while each strategy tree may emit
  side contributions to named global slots.

  A return/combine tree joins caller locals with callee-exit globals.  Its local
  result flows to the resume point, and its global result flows through side
  effects.
\<close>

subsection \<open>Effectful fold over contribution trees\<close>

text \<open>
  The generic fold composes a list of contribution trees with
  @{const seqcomp_tree}.  \<open>side_contribution_trees\<close> assembles the three
  source families in their executable order; both construction and denotation
  use that same list.
\<close>

fun fold_rhs_trees ::
  "'a::bounded_semilattice_sup_bot
   \<Rightarrow> ('k, 'g, 'a) strategy_tree list
   \<Rightarrow> ('k, 'g, 'a) strategy_tree"
where
  "fold_rhs_trees acc [] = Answer acc"
| "fold_rhs_trees acc (t # ts) =
     seqcomp_tree t (\<lambda>res. fold_rhs_trees (acc \<squnion> res) ts)"

definition side_contribution_trees ::
  "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> vname list \<times> aexp list) list
   \<Rightarrow> (pp \<times> vname option \<times> pp) list
   \<Rightarrow> (pp, 'g, 'a abs_state) strategy_tree list"
where
  "side_contribution_trees etf es ens cs =
     map (\<lambda>(u, a). apply_etf etf a u) es @
     map (\<lambda>(cl, fs, as). etf_enter etf fs as cl) ens @
     map (\<lambda>(cc, dst, ex). etf_combine etf dst cc ex) cs"

definition side_rhs_fold_eff ::
  "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> vname list \<times> aexp list) list
   \<Rightarrow> (pp \<times> vname option \<times> pp) list
   \<Rightarrow> (pp, 'g, 'a abs_state) strategy_tree"
where
  "side_rhs_fold_eff etf acc es ens cs =
     fold_rhs_trees acc (side_contribution_trees etf es ens cs)"

lemma side_rhs_fold_eff_Nil [simp]:
  "side_rhs_fold_eff etf acc [] [] [] = Answer acc"
  by (simp add: side_rhs_fold_eff_def side_contribution_trees_def)

lemma side_rhs_fold_eff_edge [simp]:
  "side_rhs_fold_eff etf acc ((u, a) # es) ens cs =
   seqcomp_tree (apply_etf etf a u)
     (\<lambda>res. side_rhs_fold_eff etf (acc \<squnion> res) es ens cs)"
  by (simp add: side_rhs_fold_eff_def side_contribution_trees_def)

lemma side_rhs_fold_eff_entry [simp]:
  "side_rhs_fold_eff etf acc [] ((cl, fs, as) # ens) cs =
   seqcomp_tree (etf_enter etf fs as cl)
     (\<lambda>res. side_rhs_fold_eff etf (acc \<squnion> res) [] ens cs)"
  by (simp add: side_rhs_fold_eff_def side_contribution_trees_def)

lemma side_rhs_fold_eff_combine [simp]:
  "side_rhs_fold_eff etf acc [] [] ((cc, dst, ex) # cs) =
   seqcomp_tree (etf_combine etf dst cc ex)
     (\<lambda>res. side_rhs_fold_eff etf (acc \<squnion> res) [] [] cs)"
  by (simp add: side_rhs_fold_eff_def side_contribution_trees_def)

lemmas side_rhs_fold_eff_simps =
  side_rhs_fold_eff_Nil side_rhs_fold_eff_edge
  side_rhs_fold_eff_entry side_rhs_fold_eff_combine

text \<open>The callee-entry seed list: each incoming call at callee entry \<open>v\<close> contributes its
  formals/actuals so the fold can invoke \<^const>\<open>etf_enter\<close> on the caller state.\<close>
definition entry_seed_list :: "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> vname list \<times> aexp list) list" where
  "entry_seed_list g v =
     map (\<lambda>(c, ca). case ca of CallEdge dst fs as \<Rightarrow> (c, fs, as)) (entry_call_list g v)"

definition make_side_rhs_tree_eff ::
  "cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'a abs_state) strategy_tree"
where
  "make_side_rhs_tree_eff g etf bot0 s0 gseed v =
     (let acc0 = (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0);
          t    = side_rhs_fold_eff etf acc0
                   (intra_predecessor_list g v) (entry_seed_list g v)
                   (return_call_list g v)
      in if v = cfg_entry g then Side gseed (restrict_global s0) t else t)"

definition side_cfg_T_eff ::
  "cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g
   \<Rightarrow> (pp, 'g, 'a abs_state) eqsT"
where
  "side_cfg_T_eff g etf bot0 s0 gseed = make_side_rhs_tree_eff g etf bot0 s0 gseed"

subsection \<open>Denotation of the effectful fold\<close>

fun fold_rhs_values ::
  "'a::bounded_semilattice_sup_bot
   \<Rightarrow> ('k + 'g \<Rightarrow> 'a)
   \<Rightarrow> ('k, 'g, 'a) strategy_tree list
   \<Rightarrow> 'a"
where
  "fold_rhs_values acc \<sigma> [] = acc"
| "fold_rhs_values acc \<sigma> (t # ts) =
     fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>) \<sigma> ts"

definition side_acc_eff ::
  "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp + 'g \<Rightarrow> 'a abs_state)
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> vname list \<times> aexp list) list
   \<Rightarrow> (pp \<times> vname option \<times> pp) list \<Rightarrow> 'a abs_state"
where
  "side_acc_eff etf acc \<sigma> es ens cs =
     fold_rhs_values acc \<sigma> (side_contribution_trees etf es ens cs)"

lemma side_acc_eff_Nil [simp]:
  "side_acc_eff etf acc \<sigma> [] [] [] = acc"
  by (simp add: side_acc_eff_def side_contribution_trees_def)

lemma side_acc_eff_edge [simp]:
  "side_acc_eff etf acc \<sigma> ((u, a) # es) ens cs =
   side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) \<sigma> es ens cs"
  by (simp add: side_acc_eff_def side_contribution_trees_def)

lemma side_acc_eff_entry [simp]:
  "side_acc_eff etf acc \<sigma> [] ((cl, fs, as) # ens) cs =
   side_acc_eff etf (acc \<squnion> traverse_rhs (etf_enter etf fs as cl) \<sigma>) \<sigma> [] ens cs"
  by (simp add: side_acc_eff_def side_contribution_trees_def)

lemma side_acc_eff_combine [simp]:
  "side_acc_eff etf acc \<sigma> [] [] ((cc, dst, ex) # cs) =
   side_acc_eff etf
     (acc \<squnion> traverse_rhs (etf_combine etf dst cc ex) \<sigma>) \<sigma> [] [] cs"
  by (simp add: side_acc_eff_def side_contribution_trees_def)

lemma traverse_fold_rhs_trees:
  "traverse_rhs (fold_rhs_trees acc ts) \<sigma> = fold_rhs_values acc \<sigma> ts"
  by (induction ts arbitrary: acc) (simp_all add: traverse_seqcomp)

lemma traverse_side_rhs_fold_eff:
  "traverse_rhs (side_rhs_fold_eff etf acc es ens cs) \<sigma> =
   side_acc_eff etf acc \<sigma> es ens cs"
  unfolding side_rhs_fold_eff_def side_acc_eff_def
  by (rule traverse_fold_rhs_trees)

lemma eq_side_cfg_T_eff:
  "eq (side_cfg_T_eff g etf bot0 s0 gseed) v \<sigma> =
     side_acc_eff etf
       (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
       \<sigma> (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)"
  unfolding side_cfg_T_eff_def make_side_rhs_tree_eff_def
  by (simp add: traverse_side_rhs_fold_eff Let_def)


subsection \<open>Per-edge contributions and their folded join\<close>

text \<open>
  Each incoming CFG edge contributes the transfer of its source unknown to the
  target equation.  The transfer depends on the source point and edge action;
  the target point selects the equation that receives the contribution.
  \<open>edge_constraint_tree\<close> exposes this contribution as a strategy tree.
\<close>

definition edge_constraint_tree ::
  "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> pp \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow> (pp, 'g, 'a abs_state) strategy_tree"
where
  "edge_constraint_tree etf u a v = apply_etf etf a u"

lemma traverse_edge_constraint_tree:
  "traverse_rhs (edge_constraint_tree etf u a v) \<sigma>
   = traverse_rhs (apply_etf etf a u) \<sigma>"
  by (simp add: edge_constraint_tree_def)

text \<open>
  The folded accumulator is the least upper bound of the seed and every
  contribution tree.  The contribution lemmas expose each source family, while
  \<open>side_acc_eff_least\<close> proves that any common upper bound dominates the
  complete fold.
\<close>

lemma acc_le_fold_rhs_values:
  "acc \<le> fold_rhs_values acc \<sigma> ts"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have "acc \<le> acc \<squnion> traverse_rhs t \<sigma>" by (rule sup_ge1)
  also have "... \<le> fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>) \<sigma> ts"
    by (rule Cons.IH)
  finally show ?case by simp
qed

lemma fold_rhs_values_member:
  assumes "t \<in> set ts"
  shows "traverse_rhs t \<sigma> \<le> fold_rhs_values acc \<sigma> ts"
  using assms
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons u ts)
  show ?case
  proof (cases "t = u")
    case True
    have "traverse_rhs t \<sigma> \<le> acc \<squnion> traverse_rhs t \<sigma>" by (rule sup_ge2)
    also have "... \<le> fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>) \<sigma> ts"
      by (rule acc_le_fold_rhs_values)
    finally show ?thesis using True by simp
  next
    case False
    with Cons.prems have "t \<in> set ts" by simp
    then show ?thesis using Cons.IH by simp
  qed
qed

lemma fold_rhs_values_least:
  assumes "acc \<le> b"
    and "\<And>t. t \<in> set ts \<Longrightarrow> traverse_rhs t \<sigma> \<le> b"
  shows "fold_rhs_values acc \<sigma> ts \<le> b"
  using assms
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have step: "acc \<squnion> traverse_rhs t \<sigma> \<le> b"
    using Cons.prems by simp
  have rest: "\<And>u. u \<in> set ts \<Longrightarrow> traverse_rhs u \<sigma> \<le> b"
    using Cons.prems(2) by simp
  show ?case by (simp add: Cons.IH[OF step rest])
qed

lemma acc_le_side_acc_eff:
  "acc \<le> side_acc_eff etf acc \<sigma> es ens cs"
  unfolding side_acc_eff_def
  by (rule acc_le_fold_rhs_values)

lemma side_acc_eff_edge_contributes:
  assumes "(u, a) \<in> set es"
  shows "traverse_rhs (apply_etf etf a u) \<sigma> \<le> side_acc_eff etf acc \<sigma> es ens cs"
  unfolding side_acc_eff_def
  apply (rule fold_rhs_values_member)
  unfolding side_contribution_trees_def
  using assms by force

lemma side_acc_eff_enter_contributes:
  assumes "(cl, fs, as) \<in> set ens"
  shows "traverse_rhs (etf_enter etf fs as cl) \<sigma> \<le> side_acc_eff etf acc \<sigma> es ens cs"
  unfolding side_acc_eff_def
  apply (rule fold_rhs_values_member)
  unfolding side_contribution_trees_def
  using assms by force

lemma side_acc_eff_combine_contributes:
  assumes "(cc, dst, ex) \<in> set cs"
  shows "traverse_rhs (etf_combine etf dst cc ex) \<sigma> \<le> side_acc_eff etf acc \<sigma> es ens cs"
  unfolding side_acc_eff_def
  apply (rule fold_rhs_values_member)
  unfolding side_contribution_trees_def
  using assms by force

lemma side_acc_eff_nil_enter_contributes:
  assumes "(cl, fs, as) \<in> set ens"
  shows "traverse_rhs (etf_enter etf fs as cl) \<sigma> \<le> side_acc_eff etf acc \<sigma> [] ens cs"
  by (rule side_acc_eff_enter_contributes[OF assms])

lemma side_acc_eff_nil_nil_combine_contributes:
  assumes "(cc, dst, ex) \<in> set cs"
  shows "traverse_rhs (etf_combine etf dst cc ex) \<sigma> \<le> side_acc_eff etf acc \<sigma> [] [] cs"
  by (rule side_acc_eff_combine_contributes[OF assms])

lemma side_acc_eff_nil_combine_contributes:
  assumes "(cc, dst, ex) \<in> set cs"
  shows "traverse_rhs (etf_combine etf dst cc ex) \<sigma> \<le> side_acc_eff etf acc \<sigma> [] ens cs"
  by (rule side_acc_eff_combine_contributes[OF assms])

lemma side_acc_eff_least:
  assumes "acc \<le> b"
    and "\<And>u a. (u, a) \<in> set es \<Longrightarrow> traverse_rhs (apply_etf etf a u) \<sigma> \<le> b"
    and "\<And>c fs as. (c, fs, as) \<in> set ens \<Longrightarrow> traverse_rhs (etf_enter etf fs as c) \<sigma> \<le> b"
    and "\<And>cc ex dst. (cc, dst, ex) \<in> set cs \<Longrightarrow> traverse_rhs (etf_combine etf dst cc ex) \<sigma> \<le> b"
  shows "side_acc_eff etf acc \<sigma> es ens cs \<le> b"
  unfolding side_acc_eff_def
  apply (rule fold_rhs_values_least[OF assms(1)])
  unfolding side_contribution_trees_def
  using assms(2-4)
  by (auto split: prod.splits)

lemma side_acc_eff_nil_nil_least:
  assumes "acc \<le> b"
    and "\<And>cc dst ex. (cc, dst, ex) \<in> set cs \<Longrightarrow> traverse_rhs (etf_combine etf dst cc ex) \<sigma> \<le> b"
  shows "side_acc_eff etf acc \<sigma> [] [] cs \<le> b"
  by (rule side_acc_eff_least[OF assms(1)]) (auto intro: assms(2))

lemma side_acc_eff_nil_least:
  assumes "acc \<le> b"
    and "\<And>c fs as. (c, fs, as) \<in> set ens \<Longrightarrow> traverse_rhs (etf_enter etf fs as c) \<sigma> \<le> b"
    and "\<And>cc ex dst. (cc, dst, ex) \<in> set cs \<Longrightarrow> traverse_rhs (etf_combine etf dst cc ex) \<sigma> \<le> b"
  shows "side_acc_eff etf acc \<sigma> [] ens cs \<le> b"
  by (rule side_acc_eff_least[OF assms(1)]) (auto intro: assms(2-3))

subsection \<open>Contribution bounds at the interprocedural CFG\<close>

text \<open>
  Every incoming ordinary edge, procedure-entry transfer, and return/combine
  transfer contributes to its target equation.  The entry equation additionally
  covers the initial local state and publishes the initial global state through
  the distinguished global seed.
\<close>

lemma cfg_edge_contributes_to_eq:
  fixes g :: cfg
  assumes "finite (intra g)" and "(u, a, v) \<in> intra g"
  shows "traverse_rhs (edge_constraint_tree etf u a v) \<sigma>
         \<le> eq (side_cfg_T_eff g etf bot0 s0 gseed) v \<sigma>"
proof -
  have "(u, a) \<in> set (intra_predecessor_list g v)"
    using assms by (simp add: intra_predecessors_def)
  then show ?thesis
    unfolding traverse_edge_constraint_tree eq_side_cfg_T_eff
    by (rule side_acc_eff_edge_contributes)
qed

lemma cfg_enter_contributes_to_eq:
  fixes g :: cfg
  assumes "finite (calls g)" and "(cl, CallEdge dst fs as, v, k) \<in> calls g"
  shows "traverse_rhs (etf_enter etf fs as cl) \<sigma>
         \<le> eq (side_cfg_T_eff g etf bot0 s0 gseed) v \<sigma>"
proof -
  have "(cl, fs, as) \<in> set (entry_seed_list g v)"
    using assms
    by (force simp: entry_seed_list_def entry_calls_def image_iff)
  then show ?thesis
    unfolding eq_side_cfg_T_eff
    by (rule side_acc_eff_enter_contributes)
qed

lemma cfg_combine_contributes_to_eq:
  fixes g :: cfg
  assumes "finite (calls g)" and "(cc, CallEdge dst fs as, FunctionEntry p, v) \<in> calls g"
  shows "traverse_rhs (etf_combine etf dst cc (FunctionResult p)) \<sigma>
         \<le> eq (side_cfg_T_eff g etf bot0 s0 gseed) v \<sigma>"
proof -
  have "(cc, dst, FunctionResult p) \<in> set (return_call_list g v)"
    using assms(2) by (force simp: set_return_call_list[OF assms(1)] return_calls_def)
  then show ?thesis
    unfolding eq_side_cfg_T_eff
    by (rule side_acc_eff_combine_contributes)
qed

lemma entry_local_seed_le_eq:
  fixes g :: cfg
  shows "restrict_local s0 \<le> eq (side_cfg_T_eff g etf bot0 s0 gseed) (cfg_entry g) \<sigma>"
proof -
  have "restrict_local s0 \<le> bot0 \<squnion> restrict_local s0" by (rule sup_ge2)
  also have "\<dots> \<le> side_acc_eff etf (bot0 \<squnion> restrict_local s0) \<sigma>
                    (intra_predecessor_list g (cfg_entry g))
                    (entry_seed_list g (cfg_entry g))
                    (return_call_list g (cfg_entry g))"
    by (rule acc_le_side_acc_eff)
  finally show ?thesis unfolding eq_side_cfg_T_eff by simp
qed

lemma entry_global_seed_le_sides:
  "restrict_global s0
   \<le> sides_of_rhs (side_cfg_T_eff g etf bot0 s0 gseed (cfg_entry g)) \<sigma> (Inr gseed)"
  unfolding side_cfg_T_eff_def make_side_rhs_tree_eff_def
  by (simp add: Let_def)

subsection \<open>Relabelling local unknowns for context indexing\<close>

text \<open>
  Context-sensitivity reindexes the local unknown \<open>pp\<close> to \<open>pp \<times> 'c\<close>.  A
  per-edge tree \<open>apply_etf etf a u\<close> queries only the single predecessor \<open>u\<close>, and a
  combine tree \<open>etf_combine etf dst cc ex\<close> queries the caller \<open>cc\<close> and the callee exit
  \<open>ex\<close>; so the context routing of either is captured by a position-aware
  relabelling \<open>h :: pp \<Rightarrow> pp \<times> 'c\<close> of the \<open>QueryL\<close> targets (intra: \<open>u \<mapsto> (u, c)\<close>;
  combine: caller \<open>\<mapsto> (cc, c)\<close>, callee \<open>\<mapsto> (ex, c')\<close>).  \<open>map_ltree\<close> performs that
  relabelling; \<open>traverse_rhs_map_ltree\<close> shows it commutes with the denotation under
  the matching \<open>map_sum\<close>-pullback of the unknown environment, so a context-indexed
  equation system's denotation is the original one read against the relabelled
  environment.  Globals (\<open>QueryG\<close> / \<open>Side\<close>) are untouched.
\<close>

primrec map_ltree ::
  "('x \<Rightarrow> 'y) \<Rightarrow> ('x, 'g, 'd) strategy_tree \<Rightarrow> ('y, 'g, 'd) strategy_tree" where
  "map_ltree h (Answer d) = Answer d"
| "map_ltree h (QueryL y f) = QueryL (h y) (\<lambda>d. map_ltree h (f d))"
| "map_ltree h (QueryG y f) = QueryG y (\<lambda>d. map_ltree h (f d))"
| "map_ltree h (Side y d t) = Side y d (map_ltree h t)"

lemma traverse_rhs_map_ltree:
  "traverse_rhs (map_ltree h t) \<sigma> = traverse_rhs t (\<lambda>z. \<sigma> (map_sum h id z))"
  by (induction t) auto



subsection \<open>General context-indexed equation system\<close>

text \<open>
  The equation for \<open>(v, c)\<close> statically relabels ordinary-edge and entry trees to
  context \<open>c\<close>.  Return/combine trees come from the supplied builder \<open>cmb\<close>, which
  may route the callee-exit query through a context computed from the caller state.
  Keeping \<open>cmb\<close> explicit separates context routing from the domain transfer record.
\<close>


definition side_cfg_T_eff_ctx ::
  "('c \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
     \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree)
   \<Rightarrow> cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g
   \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) eqsT"
where
  "side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0);
            intra = map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, c)) (apply_etf etf a u))
                        (intra_predecessor_list g v);
            enter = map (\<lambda>(cl, fs, as). map_ltree (\<lambda>w. (w, c)) (etf_enter etf fs as cl))
                        (entry_seed_list g v);
            comb  = map (\<lambda>(cc, dst, ex). cmb c dst cc ex) (return_call_list g v);
            t = fold_rhs_trees acc0 (intra @ enter @ comb)
        in if v = cfg_entry g then Side gseed (restrict_global s0) t else t)"


text \<open>
  Denotation of the context-indexed equation system at \<open>(v, c)\<close>, mirroring
  \<open>eq_side_cfg_T_eff\<close>: the entry \<open>Side\<close> wrapper is denotation-transparent, so the
  value of the unknown is the \<open>fold_rhs_values\<close> fold over the intra (relabelled) and
  combine (instance \<open>cmb\<close>) trees.  This is the form the soundness chain reads.
\<close>

lemma eq_side_cfg_T_eff_ctx:
  "eq (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) (v, ctx) \<sigma> =
     fold_rhs_values
       (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0) \<sigma>
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
            (intra_predecessor_list g v)
        @ map (\<lambda>(cl, fs, as). map_ltree (\<lambda>w. (w, ctx)) (etf_enter etf fs as cl))
            (entry_seed_list g v)
        @ map (\<lambda>(cc, dst, ex). cmb ctx dst cc ex) (return_call_list g v))"
  unfolding side_cfg_T_eff_ctx_def
  by (simp add: traverse_fold_rhs_trees Let_def)


subsection \<open>Bounds on the context fold\<close>

text \<open>
  The seed and every contributing tree lie below the context fold.  Monotonicity
  follows separately in the seed and in the unknown environment.  The uniform
  tree list makes these properties independent of the contribution source.
\<close>

lemma fold_rhs_values_mono_seed:
  fixes acc1 acc2 :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "acc1 \<le> acc2 \<Longrightarrow> fold_rhs_values acc1 \<sigma> ts \<le> fold_rhs_values acc2 \<sigma> ts"
proof (induction ts arbitrary: acc1 acc2)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  show ?case
    using Cons.IH[OF sup_mono[OF Cons.prems order_refl]] by (simp add: sup_fun_def)
qed

lemma fold_rhs_values_ge_acc:
  fixes acc :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "acc \<le> fold_rhs_values acc \<sigma> ts"
proof (induction ts arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  have "acc \<le> acc \<squnion> traverse_rhs t \<sigma>" by simp
  also have "\<dots> \<le> fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>) \<sigma> ts" by (rule Cons.IH)
  finally show ?case by simp
qed

lemma traverse_le_fold_rhs_values:
  fixes acc :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "t \<in> set ts \<Longrightarrow> traverse_rhs t \<sigma> \<le> fold_rhs_values acc \<sigma> ts"
proof (induction ts arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons t' ts)
  show ?case
  proof (cases "t = t'")
    case True
    have "traverse_rhs t \<sigma> \<le> acc \<squnion> traverse_rhs t' \<sigma>" using True by simp
    also have "\<dots> \<le> fold_rhs_values (acc \<squnion> traverse_rhs t' \<sigma>) \<sigma> ts"
      by (rule fold_rhs_values_ge_acc)
    finally show ?thesis by simp
  next
    case False
    with Cons.prems have "t \<in> set ts" by simp
    then have "traverse_rhs t \<sigma> \<le> fold_rhs_values (acc \<squnion> traverse_rhs t' \<sigma>) \<sigma> ts"
      by (rule Cons.IH)
    then show ?thesis by simp
  qed
qed

lemma fold_rhs_values_mono_sigma:
  fixes acc :: "'a::bounded_semilattice_sup_bot abs_state"
  assumes tree_mono:
    "\<And>t s1 s2. t \<in> set ts \<Longrightarrow> s1 \<le> s2 \<Longrightarrow> traverse_rhs t s1 \<le> traverse_rhs t s2"
  assumes sig: "\<sigma>1 \<le> \<sigma>2"
  shows "fold_rhs_values acc \<sigma>1 ts \<le> fold_rhs_values acc \<sigma>2 ts"
  using tree_mono
proof (induction ts arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  have hd_le: "traverse_rhs t \<sigma>1 \<le> traverse_rhs t \<sigma>2"
    using Cons.prems[of t] sig by simp
  have step1:
    "fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>1) \<sigma>1 ts
       \<le> fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>1) \<sigma>2 ts"
    by (rule Cons.IH) (use Cons.prems in simp)
  have step2:
    "fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>1) \<sigma>2 ts
       \<le> fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>2) \<sigma>2 ts"
    by (rule fold_rhs_values_mono_seed[OF sup_mono[OF order_refl hd_le]])
  show ?case using order_trans[OF step1 step2] by simp
qed

text \<open>
  A post-solution bounds every contribution tree at \<open>(v, c)\<close> by that local
  unknown.  This extracts ordinary-edge, entry, and return/combine bounds from
  the single equation post-fixpoint.
\<close>

lemma post_sol_tree_le_ctx:
  fixes \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes post:
    "eq (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) (v, ctx) \<sigma> \<le> \<sigma> (Inl (v, ctx))"
  assumes mem:
    "t \<in> set (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
                  (intra_predecessor_list g v)
              @ map (\<lambda>(cl, fs, as). map_ltree (\<lambda>w. (w, ctx)) (etf_enter etf fs as cl))
                  (entry_seed_list g v)
              @ map (\<lambda>(cc, dst, ex). cmb ctx dst cc ex) (return_call_list g v))"
  shows "traverse_rhs t \<sigma> \<le> \<sigma> (Inl (v, ctx))"
proof -
  have "traverse_rhs t \<sigma>
          \<le> eq (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) (v, ctx) \<sigma>"
    unfolding eq_side_cfg_T_eff_ctx by (rule traverse_le_fold_rhs_values[OF mem])
  then show ?thesis using post by (rule order_trans)
qed


end
