theory TD_Side_Tree
  imports TD_Side_CFG "Voblint_CFG.CFG_Collect" Strategy_Tree_Monad
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
   \<Rightarrow> (pp \<times> edge_action) list \<Rightarrow> (pp \<times> pp) list
   \<Rightarrow> (pp, 'g, 'a abs_state) strategy_tree"
where
  "side_rhs_fold_eff etf acc [] [] = Answer acc"
| "side_rhs_fold_eff etf acc ((u, a) # ps) cs =
     seqcomp_tree (apply_etf etf a u)
       (\<lambda>res. side_rhs_fold_eff etf (acc \<squnion> res) ps cs)"
| "side_rhs_fold_eff etf acc [] ((cc, ex) # cs) =
     seqcomp_tree (etf_combine etf cc ex)
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
   \<Rightarrow> (pp \<times> edge_action) list \<Rightarrow> (pp \<times> pp) list \<Rightarrow> 'a abs_state"
where
  "side_acc_eff etf acc \<sigma> [] [] = acc"
| "side_acc_eff etf acc \<sigma> ((u, a) # ps) cs =
     side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) \<sigma> ps cs"
| "side_acc_eff etf acc \<sigma> [] ((cc, ex) # cs) =
     side_acc_eff etf
       (acc \<squnion> traverse_rhs (etf_combine etf cc ex) \<sigma>) \<sigma> [] cs"

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
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
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



end
