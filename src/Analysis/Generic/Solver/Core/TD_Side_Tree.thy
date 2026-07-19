theory TD_Side_Tree
  imports TD_Side_CFG "Voblint_CFG.CFG_Transfer" Strategy_Tree_Monad
begin

section \<open>Side IP solver: constraint system construction and denotation\<close>

text \<open>
  Side-effecting constraint system over an interprocedural CFG, with a
  locals/globals split -- construction and denotation.

  side_acc_eff folds the incoming ordinary edges of a program point and then,
  at a return point, the incoming combine triples.  For a return point v,
  combines g contains triples (call, proc_exit, v).  The combined abstract
  state combine_abs sc se takes locals from the caller sc and globals from the
  callee exit se -- exactly restrict_local sc join restrict_global se.  The
  local part flows on to v's local unknown; the global part is contributed to
  named global slots by per-tree Side nodes.

  Monotonicity / solver preconditions: TD_Side_Eff_Bounds (generic _gen) and TD_Side_Eff_Soundness.
  Post-solution bounds for soundness: TD_Side_Eff_Bounds.
\<close>


subsection \<open>Effectful fold: per-edge trees composed with seqcomp_tree\<close>

text \<open>
  side_rhs_fold_eff builds the equation-system tree for one program point
  using per-edge effectful TF trees (from apply_etf) chained by seqcomp_tree.
  The accumulator acc collects local results; each per-edge tree may fire Side
  contributions to any named global.

  The combine case models IP call/return linkage and queries the named global
  slots referenced by the per-combine effectful tree.
\<close>

fun side_rhs_fold_eff ::
  "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> pp \<times> vname option) list
   \<Rightarrow> (pp, 'g, 'a abs_state) strategy_tree"
where
  "side_rhs_fold_eff etf acc [] [] = Answer acc"
| "side_rhs_fold_eff etf acc ((u, a) # ps) cs =
     seqcomp_tree (apply_etf etf a u)
       (\<lambda>res. side_rhs_fold_eff etf (acc \<squnion> res) ps cs)"
| "side_rhs_fold_eff etf acc [] ((cc, ex, dst) # cs) =
     seqcomp_tree (etf_combine etf dst cc ex)
       (\<lambda>res. side_rhs_fold_eff etf (acc \<squnion> res) [] cs)"

definition make_side_rhs_tree_eff ::
  "cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'a abs_state) strategy_tree"
where
  "make_side_rhs_tree_eff g etf bot0 s0 gseed v =
     (let acc0 = (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0);
          t    = side_rhs_fold_eff etf acc0
                   (predecessor_list g v) (combine_predecessor_list g v)
      in if v = cfg_entry g then Side gseed (restrict_global s0) t else t)"

definition side_cfg_T_eff ::
  "cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g
   \<Rightarrow> (pp, 'g, 'a abs_state) eqsT"
where
  "side_cfg_T_eff g etf bot0 s0 gseed = make_side_rhs_tree_eff g etf bot0 s0 gseed"

subsection \<open>Denotation of the effectful fold\<close>

fun side_acc_eff ::
  "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp + 'g \<Rightarrow> 'a abs_state)
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> pp \<times> vname option) list \<Rightarrow> 'a abs_state"
where
  "side_acc_eff etf acc \<sigma> [] [] = acc"
| "side_acc_eff etf acc \<sigma> ((u, a) # ps) cs =
     side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) \<sigma> ps cs"
| "side_acc_eff etf acc \<sigma> [] ((cc, ex, dst) # cs) =
     side_acc_eff etf
       (acc \<squnion> traverse_rhs (etf_combine etf dst cc ex) \<sigma>) \<sigma> [] cs"

lemma traverse_side_rhs_fold_eff:
  "traverse_rhs (side_rhs_fold_eff etf acc es cs) \<sigma> =
   side_acc_eff etf acc \<sigma> es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc)
    case Nil
    show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex dst where x: "x = (cc, ex, dst)" by (cases x)
    show ?case unfolding x
      unfolding side_rhs_fold_eff.simps side_acc_eff.simps
      by (simp only: traverse_seqcomp Cons.IH)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x
    unfolding side_rhs_fold_eff.simps side_acc_eff.simps
    by (simp only: traverse_seqcomp Cons.IH)
qed

lemma eq_side_cfg_T_eff:
  "eq (side_cfg_T_eff g etf bot0 s0 gseed) v \<sigma> =
     side_acc_eff etf
       (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
       \<sigma> (predecessor_list g v) (combine_predecessor_list g v)"
  unfolding side_cfg_T_eff_def make_side_rhs_tree_eff_def
  by (simp add: traverse_side_rhs_fold_eff Let_def)


subsection \<open>Paper equation (2): per-edge constraint and the folded join\<close>

text \<open>
  Seidl et al. (FM 2026) give every incoming CFG edge (u, act, v) the constraint
  (eta, eta[v]) >= [[(u,act,v)]] (eta[u]) eta.  The transfer [[(u,act,v)]] depends
  only on the source unknown and the action, so the paper edge tree is the
  existing apply_etf; edge_constraint_tree names that correspondence.  The target
  point v indexes the constraint, not the tree.
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
  The folded accumulator is the least upper bound of its per-edge and per-combine
  contributions above the seed acc: every incoming edge and combine contributes
  (side_acc_eff_edge_contributes / side_acc_eff_combine_contributes), and any
  common upper bound of them dominates the fold (side_acc_eff_least).  Together
  these characterise side_acc_eff -- hence the eq (2) fold -- as the finite join
  of the paper's per-edge constraints.
\<close>

lemma acc_le_side_acc_eff:
  "acc \<le> side_acc_eff etf acc \<sigma> es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc)
    case Nil show ?case by simp
  next
    case (Cons c cs)
    obtain cc ex dst where c: "c = (cc, ex, dst)" by (cases c)
    have "acc \<le> acc \<squnion> traverse_rhs (etf_combine etf dst cc ex) \<sigma>" by (rule sup_ge1)
    also have "\<dots> \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (etf_combine etf dst cc ex) \<sigma>)
                       \<sigma> [] cs"
      by (rule Cons.IH)
    finally show ?case unfolding c by simp
  qed
next
  case (Cons e es)
  obtain u a where e: "e = (u, a)" by (cases e)
  have "acc \<le> acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>" by (rule sup_ge1)
  also have "\<dots> \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) \<sigma> es cs"
    by (rule Cons.IH)
  finally show ?case unfolding e by simp
qed

lemma side_acc_eff_edge_contributes:
  assumes "(u, a) \<in> set es"
  shows "traverse_rhs (apply_etf etf a u) \<sigma> \<le> side_acc_eff etf acc \<sigma> es cs"
  using assms
proof (induction es arbitrary: acc)
  case (Cons e es)
  obtain u' a' where e: "e = (u', a')" by (cases e)
  show ?case
  proof (cases "(u, a) = e")
    case True
    have "traverse_rhs (apply_etf etf a u) \<sigma>
          \<le> acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>" by (rule sup_ge2)
    also have "\<dots> \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) \<sigma> es cs"
      by (rule acc_le_side_acc_eff)
    finally show ?thesis using True e by simp
  next
    case False
    with Cons.prems have "(u, a) \<in> set es" by simp
    then show ?thesis using Cons.IH e by simp
  qed
qed simp

lemma side_acc_eff_nil_combine_contributes:
  assumes "(cc, ex, dst) \<in> set cs"
  shows "traverse_rhs (etf_combine etf dst cc ex) \<sigma> \<le> side_acc_eff etf acc \<sigma> [] cs"
  using assms
proof (induction cs arbitrary: acc)
  case (Cons c cs)
  obtain cc' ex' dst' where c: "c = (cc', ex', dst')" by (cases c)
  show ?case
  proof (cases "(cc, ex, dst) = c")
    case True
    have "traverse_rhs (etf_combine etf dst cc ex) \<sigma>
          \<le> acc \<squnion> traverse_rhs (etf_combine etf dst cc ex) \<sigma>" by (rule sup_ge2)
    also have "\<dots> \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (etf_combine etf dst cc ex) \<sigma>)
                       \<sigma> [] cs"
      by (rule acc_le_side_acc_eff)
    finally show ?thesis using True c by simp
  next
    case False
    with Cons.prems have "(cc, ex, dst) \<in> set cs" by simp
    then show ?thesis using Cons.IH c by simp
  qed
qed simp

lemma side_acc_eff_combine_contributes:
  assumes "(cc, ex, dst) \<in> set cs"
  shows "traverse_rhs (etf_combine etf dst cc ex) \<sigma> \<le> side_acc_eff etf acc \<sigma> es cs"
  using assms
proof (induction es arbitrary: acc)
  case Nil
  then show ?case by (rule side_acc_eff_nil_combine_contributes)
next
  case (Cons e es)
  obtain u a where e: "e = (u, a)" by (cases e)
  show ?case using Cons.IH[OF Cons.prems] e by simp
qed

lemma side_acc_eff_nil_least:
  assumes "acc \<le> b"
    and "\<And>cc ex dst dst. (cc, ex, dst) \<in> set cs \<Longrightarrow> traverse_rhs (etf_combine etf dst cc ex) \<sigma> \<le> b"
  shows "side_acc_eff etf acc \<sigma> [] cs \<le> b"
  using assms
proof (induction cs arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons c cs)
  obtain cc ex dst where c: "c = (cc, ex, dst)" by (cases c)
  have le1: "acc \<squnion> traverse_rhs (etf_combine etf dst cc ex) \<sigma> \<le> b"
    using Cons.prems(1) Cons.prems(2)[of cc ex dst] c by simp
  have cb: "\<And>cc' ex' dst'. (cc', ex', dst') \<in> set cs
              \<Longrightarrow> traverse_rhs (etf_combine etf dst' cc' ex') \<sigma> \<le> b"
    using Cons.prems(2) by simp
  have "side_acc_eff etf (acc \<squnion> traverse_rhs (etf_combine etf dst cc ex) \<sigma>) \<sigma> [] cs \<le> b"
    by (rule Cons.IH[OF le1 cb])
  then show ?case unfolding c by simp
qed

lemma side_acc_eff_least:
  assumes "acc \<le> b"
    and "\<And>u a. (u, a) \<in> set es \<Longrightarrow> traverse_rhs (apply_etf etf a u) \<sigma> \<le> b"
    and "\<And>cc ex dst dst. (cc, ex, dst) \<in> set cs \<Longrightarrow> traverse_rhs (etf_combine etf dst cc ex) \<sigma> \<le> b"
  shows "side_acc_eff etf acc \<sigma> es cs \<le> b"
  using assms
proof (induction es arbitrary: acc)
  case Nil
  show ?case by (rule side_acc_eff_nil_least[OF Nil.prems(1) Nil.prems(3)])
next
  case (Cons e es)
  obtain u a where e: "e = (u, a)" by (cases e)
  have le1: "acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma> \<le> b"
    using Cons.prems(1) Cons.prems(2)[of u a] e by simp
  have eb: "\<And>u' a'. (u', a') \<in> set es
              \<Longrightarrow> traverse_rhs (apply_etf etf a' u') \<sigma> \<le> b"
    using Cons.prems(2) by simp
  have "side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) \<sigma> es cs \<le> b"
    by (rule Cons.IH[OF le1 eb Cons.prems(3)])
  then show ?case unfolding e by simp
qed

subsection \<open>Paper equation (2) at the interprocedural CFG\<close>

text \<open>
  Lifting the fold characterisation to the CFG: through eq_side_cfg_T_eff, every
  incoming ordinary edge and every incoming combine (call/return) triple of a
  program point contributes to that point's equation right-hand side, and the
  entry point's local seed restrict_local s0 and global seed restrict_global s0
  (into gseed) are covered -- the paper's initialization constraint.
\<close>

lemma cfg_edge_contributes_to_eq:
  assumes "finite (edges g)" and "(u, a, v) \<in> edges g"
  shows "traverse_rhs (edge_constraint_tree etf u a v) \<sigma>
         \<le> eq (side_cfg_T_eff g etf bot0 s0 gseed) v \<sigma>"
proof -
  have "(u, a) \<in> set (predecessor_list g v)"
    using assms by (simp add: predecessors_def)
  then show ?thesis
    unfolding traverse_edge_constraint_tree eq_side_cfg_T_eff
    by (rule side_acc_eff_edge_contributes)
qed

lemma cfg_combine_contributes_to_eq:
  assumes "finite (combines g)" and "(cc, ex, v, dst) \<in> combines g"
  shows "traverse_rhs (etf_combine etf dst cc ex) \<sigma>
         \<le> eq (side_cfg_T_eff g etf bot0 s0 gseed) v \<sigma>"
proof -
  have "(cc, ex, dst) \<in> set (combine_predecessor_list g v)"
    using assms by (simp add: combine_predecessors_eq)
  then show ?thesis
    unfolding eq_side_cfg_T_eff
    by (rule side_acc_eff_combine_contributes)
qed

lemma entry_local_seed_le_eq:
  "restrict_local s0 \<le> eq (side_cfg_T_eff g etf bot0 s0 gseed) (cfg_entry g) \<sigma>"
proof -
  have "restrict_local s0 \<le> bot0 \<squnion> restrict_local s0" by (rule sup_ge2)
  also have "\<dots> \<le> side_acc_eff etf (bot0 \<squnion> restrict_local s0) \<sigma>
                    (predecessor_list g (cfg_entry g))
                    (combine_predecessor_list g (cfg_entry g))"
    by (rule acc_le_side_acc_eff)
  finally show ?thesis unfolding eq_side_cfg_T_eff by simp
qed

lemma entry_global_seed_le_sides:
  "restrict_global s0
   \<le> sides_of_rhs (side_cfg_T_eff g etf bot0 s0 gseed (cfg_entry g)) \<sigma> (Inr gseed)"
  unfolding side_cfg_T_eff_def make_side_rhs_tree_eff_def
  by (simp add: Let_def)

subsection \<open>Relabelling local unknowns (context-indexing primitive, S1)\<close>

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


subsection \<open>Context-indexed fold over a list of per-point trees (S1)\<close>

text \<open>
  The context-level analogue of \<open>side_rhs_fold_eff\<close>: given the list of
  context-indexed trees contributing to a single unknown \<open>(v, c)\<close> -- the intra
  per-edge trees and the combine trees, each already routed to the right
  predecessor contexts -- fold them with \<open>seqcomp_tree\<close>, joining the local Answers.
  \<open>side_acc_ctx\<close> is the denotation; \<open>traverse_side_rhs_fold_ctx\<close> connects the two,
  exactly as \<open>traverse_side_rhs_fold_eff\<close> does for the monovariant fold.  Keeping
  the per-point tree list abstract leaves the context routing -- intra (static,
  via \<open>map_ltree\<close>) versus the value-dependent semantic combine (which breaks
  \<open>static_deps\<close>, hence warrowing-only) -- to the instance (Phase 3 / S2).
\<close>

fun side_rhs_fold_ctx ::
  "'d::bounded_semilattice_sup_bot
   \<Rightarrow> (pp \<times> 'c, 'g, 'd) strategy_tree list
   \<Rightarrow> (pp \<times> 'c, 'g, 'd) strategy_tree"
where
  "side_rhs_fold_ctx acc [] = Answer acc"
| "side_rhs_fold_ctx acc (t # ts) =
     seqcomp_tree t (\<lambda>res. side_rhs_fold_ctx (acc \<squnion> res) ts)"

fun side_acc_ctx ::
  "'d::bounded_semilattice_sup_bot \<Rightarrow> (pp \<times> 'c + 'g \<Rightarrow> 'd)
   \<Rightarrow> (pp \<times> 'c, 'g, 'd) strategy_tree list \<Rightarrow> 'd"
where
  "side_acc_ctx acc \<sigma> [] = acc"
| "side_acc_ctx acc \<sigma> (t # ts) = side_acc_ctx (acc \<squnion> traverse_rhs t \<sigma>) \<sigma> ts"

lemma traverse_side_rhs_fold_ctx:
  "traverse_rhs (side_rhs_fold_ctx acc ts) \<sigma> = side_acc_ctx acc \<sigma> ts"
  by (induction ts arbitrary: acc) (simp_all add: traverse_seqcomp)


subsection \<open>Conservativity at the trivial context (S1 acceptance #1)\<close>

text \<open>
  The context-indexed equation system reindexed to the single trivial context \<open>()\<close>:
  relabel every local query of the monovariant RHS to its \<open>()\<close>-context copy.  This
  is the \<open>'c = unit\<close> specialisation -- with one context the value-dependent combine
  routing collapses, so a uniform \<open>map_ltree\<close> relabel is exact.
  \<open>context_eqsystem_conservative\<close> then shows its denotation is the monovariant
  equation system read against the canonical \<open>pp \<cong> pp \<times> unit\<close> pullback of the
  unknown environment -- i.e. nothing changes but the reindexing.  This isolates
  "the equation system is preserved at the trivial context" from solver soundness;
  the general value-dependent \<open>side_cfg_T_eff_ctx\<close> (which routes the semantic
  combine through the strategy monad, breaking \<open>static_deps\<close>, hence warrowing-only)
  and acceptance #2 (context-parametric soundness) build on this.
\<close>

definition side_cfg_T_eff_ctx_unit ::
  "cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g
   \<Rightarrow> (pp \<times> unit, 'g, 'a abs_state) eqsT"
where
  "side_cfg_T_eff_ctx_unit g etf bot0 s0 gseed =
     (\<lambda>x. map_ltree (\<lambda>u. (u, ())) (side_cfg_T_eff g etf bot0 s0 gseed (fst x)))"

theorem context_eqsystem_conservative:
  "eq (side_cfg_T_eff_ctx_unit g etf bot0 s0 gseed) (v, ()) \<sigma>
   = eq (side_cfg_T_eff g etf bot0 s0 gseed) v
        (\<lambda>z. \<sigma> (map_sum (\<lambda>u. (u, ())) id z))"
  unfolding side_cfg_T_eff_ctx_unit_def
  by (simp add: traverse_rhs_map_ltree)


subsection \<open>Value-dependent semantic combine (S1, unit-global domain)\<close>

text \<open>
  The semantic combine routes the callee-exit query to a context computed from the
  queried CALLER state -- the value dependence that makes the context entry-state
  (Goblint-style) rather than syntactic.  \<open>unit_combine_tree_ctx\<close> is the
  context-indexed version of \<open>unit_combine_tree\<close> (TD_Side_CFG): it queries the
  caller \<open>(cc, c)\<close>, binds its local \<open>sc\<close>, computes the callee context \<open>ec c sc\<close>,
  then queries \<open>(ex, ec c sc)\<close>.  Because the queried unknown \<open>(ex, ec c sc)\<close>
  depends on the value \<open>sc\<close>, this tree does NOT have \<open>static_deps\<close> for a
  non-constant \<open>ec\<close> -- exactly why the context-indexed system is warrowing-only.
  \<open>traverse_unit_combine_tree_ctx\<close> gives its denotation; \<open>unit_combine_tree_ctx_unit\<close>
  shows that at the trivial context (\<open>ec = (\<lambda>_ _. ())\<close>) it collapses to the
  \<open>map_ltree\<close> relabel of the monovariant combine -- the combine-level instance of
  \<open>context_eqsystem_conservative\<close>.
\<close>

definition unit_combine_tree_ctx ::
  "('c \<Rightarrow> 'a abs_state \<Rightarrow> 'c) \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> 'c
   \<Rightarrow> (pp \<times> 'c, unit, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
where
  "unit_combine_tree_ctx ec cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG () (\<lambda>g. QueryL (ex, ec ctx (sc \<squnion> g)) (\<lambda>se.
       let res = restrict_local (sc \<squnion> g) \<squnion> restrict_global (se \<squnion> g) in
       Side () (restrict_global res)
         (Answer (restrict_local res)))))"

lemma traverse_unit_combine_tree_ctx:
  "traverse_rhs (unit_combine_tree_ctx ec cc ex ctx) \<sigma> =
     (let sc = \<sigma> (Inl (cc, ctx)); g = \<sigma> (Inr ()); se = \<sigma> (Inl (ex, ec ctx (sc \<squnion> g)))
      in restrict_local (restrict_local (sc \<squnion> g) \<squnion> restrict_global (se \<squnion> g)))"
  unfolding unit_combine_tree_ctx_def by (simp add: Let_def)

lemma unit_combine_tree_ctx_unit_traverse:
  "traverse_rhs (unit_combine_tree_ctx (\<lambda>_ _. ()) cc ex ()) \<sigma>
   = traverse_rhs (map_ltree (\<lambda>u. (u, ())) (unit_combine_tree None cc ex)) \<sigma>"
  unfolding unit_combine_tree_ctx_def unit_combine_tree_def
  by (simp add: Let_def combine_collect_abs_def combine_abs_def restrict_combine)


subsection \<open>General context-indexed equation system (S1 assembly)\<close>

text \<open>
  \<open>side_cfg_T_eff_ctx\<close> assembles the context-indexed RHS at every unknown
  \<open>(v, c)\<close>: the intra per-edge trees are relabelled \<open>u \<mapsto> (u, c)\<close> (the context is
  unchanged along an intra edge, so a static \<open>map_ltree\<close> relabel is exact), while
  the combine trees are produced by a context-combine builder \<open>cmb\<close> supplied by
  the instance -- for a semantic (entry-state) context \<open>cmb\<close> routes the callee-exit
  query value-dependently (cf. \<open>unit_combine_tree_ctx\<close>), which is why the system is
  warrowing-only.  Passing \<open>cmb\<close> as a parameter (rather than a field of the
  transfer record) keeps the definition local to the strategy-tree layer: it lands
  without disturbing the monovariant spine, and an instance later folds \<open>cmb\<close> into
  the transfer record once the record carries a context type.

  \<open>side_cfg_T_eff_ctx_collapses_unit\<close> is the assembly-level conservativity gate:
  with the trivial context and the conservative combine builder (the monovariant
  combine, statically relabelled), the assembled system is exactly the
  \<open>'c = unit\<close> reindexing \<open>side_cfg_T_eff_ctx_unit\<close> -- so by
  \<open>context_eqsystem_conservative\<close> its denotation is the monovariant equation
  system.  This isolates the assembly from solver soundness (acceptance #2).
\<close>

lemma map_ltree_seqcomp:
  "map_ltree h (seqcomp_tree t k)
   = seqcomp_tree (map_ltree h t) (\<lambda>d. map_ltree h (k d))"
  by (induction t) auto

lemma map_ltree_side_rhs_fold_eff:
  "map_ltree h (side_rhs_fold_eff etf acc preds combs)
   = side_rhs_fold_ctx acc
       (map (\<lambda>(u, a). map_ltree h (apply_etf etf a u)) preds
        @ map (\<lambda>(cc, ex, dst). map_ltree h (etf_combine etf dst cc ex)) combs)"
proof (induction preds arbitrary: acc)
  case Nil
  show ?case
  proof (induction combs arbitrary: acc)
    case Nil show ?case by simp
  next
    case (Cons cx cs)
    obtain cc ex dst where "cx = (cc, ex, dst)" by (cases cx)
    with Cons show ?case by (simp add: map_ltree_seqcomp sup_fun_def)
  qed
next
  case (Cons p ps)
  obtain u a where "p = (u, a)" by (cases p)
  with Cons show ?case by (simp add: map_ltree_seqcomp sup_fun_def)
qed

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
                        (predecessor_list g v);
            comb  = map (\<lambda>(cc, ex, dst). cmb c dst cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx acc0 (intra @ comb)
        in if v = cfg_entry g then Side gseed (restrict_global s0) t else t)"

theorem side_cfg_T_eff_ctx_collapses_unit:
  "side_cfg_T_eff_ctx
      (\<lambda>_ dst cc ex. map_ltree (\<lambda>u. (u, ())) (etf_combine etf dst cc ex))
      g etf bot0 s0 gseed (v, ())
   = side_cfg_T_eff_ctx_unit g etf bot0 s0 gseed (v, ())"
proof -
  let ?h = "\<lambda>u::pp. (u, ())"
  have fold:
    "side_rhs_fold_ctx acc0
        (map (\<lambda>(u, a). map_ltree ?h (apply_etf etf a u)) (predecessor_list g v)
         @ map (\<lambda>(cc, ex, dst). map_ltree ?h (etf_combine etf dst cc ex))
               (combine_predecessor_list g v))
     = map_ltree ?h
         (side_rhs_fold_eff etf acc0 (predecessor_list g v)
            (combine_predecessor_list g v))" for acc0 v
    by (simp add: map_ltree_side_rhs_fold_eff)
  show ?thesis
  proof (cases "v = cfg_entry g")
    case True
    thus ?thesis
      unfolding side_cfg_T_eff_ctx_def side_cfg_T_eff_ctx_unit_def
                side_cfg_T_eff_def make_side_rhs_tree_eff_def
      by (simp add: fold Let_def)
  next
    case False
    thus ?thesis
      unfolding side_cfg_T_eff_ctx_def side_cfg_T_eff_ctx_unit_def
                side_cfg_T_eff_def make_side_rhs_tree_eff_def
      by (simp add: fold Let_def)
  qed
qed

text \<open>
  Denotation of the context-indexed equation system at \<open>(v, c)\<close>, mirroring
  \<open>eq_side_cfg_T_eff\<close>: the entry \<open>Side\<close> wrapper is denotation-transparent, so the
  value of the unknown is the \<open>side_acc_ctx\<close> fold over the intra (relabelled) and
  combine (instance \<open>cmb\<close>) trees.  This is the form the soundness chain reads.
\<close>

lemma eq_side_cfg_T_eff_ctx:
  "eq (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) (v, ctx) \<sigma> =
     side_acc_ctx
       (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0) \<sigma>
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
            (predecessor_list g v)
        @ map (\<lambda>(cc, ex, dst). cmb ctx dst cc ex) (combine_predecessor_list g v))"
  unfolding side_cfg_T_eff_ctx_def
  by (simp add: traverse_side_rhs_fold_ctx Let_def)


subsection \<open>Bounds on the context fold (S1, for acceptance #2)\<close>

text \<open>
  Structural bounds on \<open>side_acc_ctx\<close>, the context analogues of the
  \<open>side_acc_eff\<close> bounds in \<open>TD_Side_Eff_Bounds\<close>.  Because the context fold runs a
  single uniform tree list (intra and combine trees already assembled), these are
  simpler than the edge/combine-split monovariant versions.  \<open>side_acc_ctx_ge_acc\<close>
  and \<open>traverse_le_side_acc_ctx\<close> give the post-fixpoint lower bounds (the seed and
  every contributing tree sit below the fold); \<open>side_acc_ctx_mono_acc\<close> /
  \<open>side_acc_ctx_mono\<close> give monotonicity in the seed and the environment.
\<close>

lemma side_acc_ctx_mono_acc:
  fixes acc1 acc2 :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "acc1 \<le> acc2 \<Longrightarrow> side_acc_ctx acc1 \<sigma> ts \<le> side_acc_ctx acc2 \<sigma> ts"
proof (induction ts arbitrary: acc1 acc2)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  show ?case
    using Cons.IH[OF sup_mono[OF Cons.prems order_refl]] by (simp add: sup_fun_def)
qed

lemma side_acc_ctx_ge_acc:
  fixes acc :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "acc \<le> side_acc_ctx acc \<sigma> ts"
proof (induction ts arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  have "acc \<le> acc \<squnion> traverse_rhs t \<sigma>" by simp
  also have "\<dots> \<le> side_acc_ctx (acc \<squnion> traverse_rhs t \<sigma>) \<sigma> ts" by (rule Cons.IH)
  finally show ?case by simp
qed

lemma traverse_le_side_acc_ctx:
  fixes acc :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "t \<in> set ts \<Longrightarrow> traverse_rhs t \<sigma> \<le> side_acc_ctx acc \<sigma> ts"
proof (induction ts arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons t' ts)
  show ?case
  proof (cases "t = t'")
    case True
    have "traverse_rhs t \<sigma> \<le> acc \<squnion> traverse_rhs t' \<sigma>" using True by simp
    also have "\<dots> \<le> side_acc_ctx (acc \<squnion> traverse_rhs t' \<sigma>) \<sigma> ts"
      by (rule side_acc_ctx_ge_acc)
    finally show ?thesis by simp
  next
    case False
    with Cons.prems have "t \<in> set ts" by simp
    then have "traverse_rhs t \<sigma> \<le> side_acc_ctx (acc \<squnion> traverse_rhs t' \<sigma>) \<sigma> ts"
      by (rule Cons.IH)
    then show ?thesis by simp
  qed
qed

lemma side_acc_ctx_mono:
  fixes acc :: "'a::bounded_semilattice_sup_bot abs_state"
  assumes tree_mono:
    "\<And>t s1 s2. t \<in> set ts \<Longrightarrow> s1 \<le> s2 \<Longrightarrow> traverse_rhs t s1 \<le> traverse_rhs t s2"
  assumes sig: "\<sigma>1 \<le> \<sigma>2"
  shows "side_acc_ctx acc \<sigma>1 ts \<le> side_acc_ctx acc \<sigma>2 ts"
  using tree_mono
proof (induction ts arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  have hd_le: "traverse_rhs t \<sigma>1 \<le> traverse_rhs t \<sigma>2"
    using Cons.prems[of t] sig by simp
  have step1:
    "side_acc_ctx (acc \<squnion> traverse_rhs t \<sigma>1) \<sigma>1 ts
       \<le> side_acc_ctx (acc \<squnion> traverse_rhs t \<sigma>1) \<sigma>2 ts"
    by (rule Cons.IH) (use Cons.prems in simp)
  have step2:
    "side_acc_ctx (acc \<squnion> traverse_rhs t \<sigma>1) \<sigma>2 ts
       \<le> side_acc_ctx (acc \<squnion> traverse_rhs t \<sigma>2) \<sigma>2 ts"
    by (rule side_acc_ctx_mono_acc[OF sup_mono[OF order_refl hd_le]])
  show ?case using order_trans[OF step1 step2] by simp
qed

text \<open>
  Per-predecessor post-fixpoint extraction: at a post-solution \<open>\<sigma>\<close> of the
  context-indexed system (\<open>eq \<dots> (v,c) \<sigma> \<le> \<sigma> (Inl (v,c))\<close>), every contributing
  tree at \<open>(v,c)\<close> -- intra or combine -- denotes below the unknown \<open>(v,c)\<close>.  This
  is the \<open>step_le\<close>/\<open>combine_le\<close>-shaped fact the context witness-soundness induction
  consumes (the context analogue of reading off the per-edge bounds from a
  post-fixpoint), built from \<open>eq_side_cfg_T_eff_ctx\<close> and \<open>traverse_le_side_acc_ctx\<close>.
\<close>

lemma post_sol_tree_le_ctx:
  fixes \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes post:
    "eq (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) (v, ctx) \<sigma> \<le> \<sigma> (Inl (v, ctx))"
  assumes mem:
    "t \<in> set (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
                  (predecessor_list g v)
              @ map (\<lambda>(cc, ex, dst). cmb ctx dst cc ex) (combine_predecessor_list g v))"
  shows "traverse_rhs t \<sigma> \<le> \<sigma> (Inl (v, ctx))"
proof -
  have "traverse_rhs t \<sigma>
          \<le> eq (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) (v, ctx) \<sigma>"
    unfolding eq_side_cfg_T_eff_ctx by (rule traverse_le_side_acc_ctx[OF mem])
  then show ?thesis using post by (rule order_trans)
qed


subsection \<open>Frame-entry context seeding (S1, new generator)\<close>

text \<open>
  \<^const>\<open>side_cfg_T_eff_ctx\<close> routes every predecessor of a node -- including
  \<^const>\<open>EA_Enter\<close> edges -- through the uniform intra fold, so a frame-entry
  node's locals come from \<^const>\<open>apply_etf\<close>'s enter transfer applied to the
  caller's state, never from the context index itself.  \<open>side_cfg_T_eff_ctx_seeded\<close>
  is a separate generator (not a modification of \<^const>\<open>side_cfg_T_eff_ctx\<close>, to
  keep the existing entry-store soundness chain in the dedicated entry-store witness
  untouched): at a frame-entry node \<^term>\<open>v\<close> (\<^term>\<open>is_frame_entry g v\<close>), every
  \<^const>\<open>EA_Enter\<close> predecessor is dropped from the ordinary intra fold and
  replaced by a single context-derived seed \<^term>\<open>combine_abs (ent c) s\<close> --
  locals from the context, globals from the predecessor's queried state, exactly
  the locals/globals split \<^const>\<open>unit_combine_tree_ctx\<close> already uses for
  call returns.  Every non-\<^const>\<open>EA_Enter\<close> predecessor (e.g. a loop backedge
  into the same node) still flows through \<^const>\<open>apply_etf\<close> unchanged.
\<close>

definition side_cfg_T_eff_ctx_seeded ::
  "('c \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
     \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree)
   \<Rightarrow> ('c \<Rightarrow> 'a abs_state)
   \<Rightarrow> cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g
   \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) eqsT"
where
  "side_cfg_T_eff_ctx_seeded cmb ent g etf bot0 s0 gseed =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0);
            intra = map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, c)) (apply_etf etf a u))
                        (non_enter_predecessor_list g v);
            enter = map (\<lambda>(u, a). QueryL (u, c) (\<lambda>s. Answer (combine_abs (ent c) s)))
                        (enter_predecessor_list g v);
            comb  = map (\<lambda>(cc, ex, dst). cmb c dst cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx acc0 (intra @ enter @ comb)
        in if v = cfg_entry g then Side gseed (restrict_global s0) t else t)"

lemma eq_side_cfg_T_eff_ctx_seeded:
  "eq (side_cfg_T_eff_ctx_seeded cmb ent g etf bot0 s0 gseed) (v, ctx) \<sigma> =
     side_acc_ctx
       (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0) \<sigma>
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
            (non_enter_predecessor_list g v)
        @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent ctx) s)))
              (enter_predecessor_list g v)
        @ map (\<lambda>(cc, ex, dst). cmb ctx dst cc ex) (combine_predecessor_list g v))"
  unfolding side_cfg_T_eff_ctx_seeded_def
  by (simp add: traverse_side_rhs_fold_ctx Let_def)

end
