theory TD_Side_IP_Tree
  imports TD_Side_CFG "Voblint_CFG.CFG_Collect_IP" Strategy_Tree_Monad
begin

section \<open>Side IP solver: constraint system construction and denotation\<close>

text \<open>
  Side-effecting constraint system over an interprocedural CFG, with a
  locals/globals split -- construction and denotation.

  side_acc_ip folds the incoming ordinary edges of a program point and then,
  at a return point, the incoming combine triples.  For a return point v,
  combines g contains triples (call, proc_exit, v).  The combined abstract
  state combine_abs sc se takes locals from the caller sc and globals from the
  callee exit se -- exactly restrict_local sc join restrict_global se.  The
  local part flows on to v's local unknown; the global part is contributed to
  the single global unknown by a side effect.

  Monotonicity / solver preconditions: TD_Side_IP_Mono.
  Post-solution bounds for soundness: TD_Side_IP_Bounds.
\<close>

subsection \<open>Strategy tree\<close>

(* One program point: fold the incoming edges (QueryL/QueryG/Side) then the
   incoming combine triples (QueryL call / QueryL exit / QueryG / Side). *)
fun side_rhs_fold_ip ::
  "'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => 'a abs_state => (pp * edge_action) list => (pp * pp) list
   => (pp, unit, 'a abs_state) strategy_tree"
where
  "side_rhs_fold_ip tf join acc [] [] = Answer acc"
| "side_rhs_fold_ip tf join acc ((u, a) # ps) cs =
     QueryL u (\<lambda>su. QueryG () (\<lambda>glob.
       let res = apply_tf tf a (join su glob)
       in Side () (restrict_global res)
            (side_rhs_fold_ip tf join (join acc (restrict_local res)) ps cs)))"
| "side_rhs_fold_ip tf join acc [] ((cc, ex) # cs) =
     QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG () (\<lambda>glob.
       let res = restrict_local (join sc glob) \<squnion> restrict_global (join se glob)
       in Side () (restrict_global res)
            (side_rhs_fold_ip tf join (join acc (restrict_local res)) [] cs))))"

definition make_side_rhs_tree_ip ::
  "cfg => 'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => 'a abs_state => 'a abs_state => pp
   => (pp, unit, 'a abs_state) strategy_tree"
where
  "make_side_rhs_tree_ip g tf join bot0 s0 v =
     (let acc0 = (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0);
          t    = side_rhs_fold_ip tf join acc0
                   (predecessor_list g v) (combine_predecessor_list g v)
      in if v = cfg_entry g then Side () (restrict_global s0) t else t)"

definition side_cfg_T_ip ::
  "cfg => 'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => 'a abs_state => 'a abs_state
   => (pp, unit, 'a abs_state) eqsT"
where
  "side_cfg_T_ip g tf join bot0 s0 = make_side_rhs_tree_ip g tf join bot0 s0"

subsection \<open>Denotation: local fold\<close>

fun side_acc_ip ::
  "'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => 'a abs_state => (pp + unit => 'a abs_state)
   => (pp * edge_action) list => (pp * pp) list => 'a abs_state"
where
  "side_acc_ip tf join acc \<sigma> [] [] = acc"
| "side_acc_ip tf join acc \<sigma> ((u, a) # ps) cs =
     side_acc_ip tf join
       (join acc (restrict_local (apply_tf tf a (join (\<sigma> (Inl u)) (\<sigma> (Inr ()))))))
       \<sigma> ps cs"
| "side_acc_ip tf join acc \<sigma> [] ((cc, ex) # cs) =
     side_acc_ip tf join
       (join acc (restrict_local (join (\<sigma> (Inl cc)) (\<sigma> (Inr ())))))
       \<sigma> [] cs"

subsection \<open>Denotation: global contribution\<close>

fun side_glob_ip ::
  "'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => (pp + unit => 'a abs_state)
   => (pp * edge_action) list => (pp * pp) list => 'a abs_state"
where
  "side_glob_ip tf join \<sigma> [] [] = bot"
| "side_glob_ip tf join \<sigma> ((u, a) # ps) cs =
     side_glob_ip tf join \<sigma> ps cs
       \<squnion> restrict_global (apply_tf tf a (join (\<sigma> (Inl u)) (\<sigma> (Inr ()))))"
| "side_glob_ip tf join \<sigma> [] ((cc, ex) # cs) =
     side_glob_ip tf join \<sigma> [] cs
       \<squnion> restrict_global (join (\<sigma> (Inl ex)) (\<sigma> (Inr ())))"

(* traverse_rhs (= eq) of the fold is exactly side_acc_ip. *)
lemma traverse_side_rhs_fold_ip:
  "traverse_rhs (side_rhs_fold_ip tf join acc es cs) \<sigma> = side_acc_ip tf join acc \<sigma> es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc)
    case Nil
    show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    show ?case unfolding x using Cons.IH
      by (simp add: Let_def restrict_local_combine_eq)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH by (simp add: Let_def)
qed

lemma eq_side_cfg_T_ip:
  "eq (side_cfg_T_ip g tf join bot0 s0) v \<sigma> =
     side_acc_ip tf join
       (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0)
       \<sigma> (predecessor_list g v) (combine_predecessor_list g v)"
  unfolding side_cfg_T_ip_def make_side_rhs_tree_ip_def
  by (simp add: traverse_side_rhs_fold_ip Let_def)

subsection \<open>Effectful fold: per-edge trees composed with seqcomp_tree\<close>

text \<open>
  side_rhs_fold_ip_eff builds the equation-system tree for one program point
  using per-edge effectful TF trees (from apply_etf) chained by seqcomp_tree.
  The accumulator acc collects local results; each per-edge tree may fire Side
  contributions to any named global.

  The combine case retains the unit-global structure of side_rhs_fold_ip:
  combine triples model IP call/return linkage and always reference the single
  global unknown.

  For etf = etf_from_tf tf, edge cases produce the same tree as side_rhs_fold_ip
  tf (\<squnion>), proved below via traverse_seqcomp and traverse_pure_edge_tree.
\<close>

fun side_rhs_fold_ip_eff ::
  "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp \<times> edge_action) list \<Rightarrow> (pp \<times> pp) list
   \<Rightarrow> (pp, unit, 'a abs_state) strategy_tree"
where
  "side_rhs_fold_ip_eff etf acc [] [] = Answer acc"
| "side_rhs_fold_ip_eff etf acc ((u, a) # ps) cs =
     seqcomp_tree (apply_etf etf a u)
       (\<lambda>res. side_rhs_fold_ip_eff etf (acc \<squnion> res) ps cs)"
| "side_rhs_fold_ip_eff etf acc [] ((cc, ex) # cs) =
     seqcomp_tree (etf_combine etf cc ex)
       (\<lambda>res. side_rhs_fold_ip_eff etf (acc \<squnion> res) [] cs)"

definition make_side_rhs_tree_ip_eff ::
  "cfg \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> pp
   \<Rightarrow> (pp, unit, 'a abs_state) strategy_tree"
where
  "make_side_rhs_tree_ip_eff g etf bot0 s0 v =
     (let acc0 = (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0);
          t    = side_rhs_fold_ip_eff etf acc0
                   (predecessor_list g v) (combine_predecessor_list g v)
      in if v = cfg_entry g then Side () (restrict_global s0) t else t)"

definition side_cfg_T_ip_eff ::
  "cfg \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp, unit, 'a abs_state) eqsT"
where
  "side_cfg_T_ip_eff g etf bot0 s0 = make_side_rhs_tree_ip_eff g etf bot0 s0"

subsection \<open>Denotation of the effectful fold\<close>

fun side_acc_ip_eff ::
  "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp + unit \<Rightarrow> 'a abs_state)
   \<Rightarrow> (pp \<times> edge_action) list \<Rightarrow> (pp \<times> pp) list \<Rightarrow> 'a abs_state"
where
  "side_acc_ip_eff etf acc \<sigma> [] [] = acc"
| "side_acc_ip_eff etf acc \<sigma> ((u, a) # ps) cs =
     side_acc_ip_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) \<sigma> ps cs"
| "side_acc_ip_eff etf acc \<sigma> [] ((cc, ex) # cs) =
     side_acc_ip_eff etf
       (acc \<squnion> traverse_rhs (etf_combine etf cc ex) \<sigma>) \<sigma> [] cs"

lemma traverse_side_rhs_fold_ip_eff:
  "traverse_rhs (side_rhs_fold_ip_eff etf acc es cs) \<sigma> =
   side_acc_ip_eff etf acc \<sigma> es cs"
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
      unfolding side_rhs_fold_ip_eff.simps side_acc_ip_eff.simps
      by (simp only: traverse_seqcomp Cons.IH)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x
    unfolding side_rhs_fold_ip_eff.simps side_acc_ip_eff.simps
    by (simp only: traverse_seqcomp Cons.IH)
qed

lemma eq_side_cfg_T_ip_eff:
  "eq (side_cfg_T_ip_eff g etf bot0 s0) v \<sigma> =
     side_acc_ip_eff etf
       (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
       \<sigma> (predecessor_list g v) (combine_predecessor_list g v)"
  unfolding side_cfg_T_ip_eff_def make_side_rhs_tree_ip_eff_def
  by (simp add: traverse_side_rhs_fold_ip_eff Let_def)

lemma side_acc_ip_eff_eq_side_acc_ip:
  "side_acc_ip_eff (etf_from_tf tf) acc \<sigma> es cs =
   side_acc_ip tf (\<squnion>) acc \<sigma> es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc)
    case Nil show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    show ?case unfolding x using Cons.IH
      by (simp add: traverse_pure_combine_tree sup_fun_def)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH
    by (simp add: traverse_pure_edge_tree sup_fun_def)
qed

subsection \<open>Pure shim: effectful and pure folds build the same tree\<close>

text \<open>
  For etf = etf_from_tf tf the effectful fold builds exactly the tree the pure
  fold builds (with join = \<squnion>).  This is the backward-compatibility bridge: every
  result proven about side_cfg_T_ip tf (\<squnion>) -- monotonicity, side contributions,
  dependencies, soundness -- transfers verbatim to side_cfg_T_ip_eff (etf_from_tf tf).
\<close>

lemma side_rhs_fold_ip_eff_etf_from_tf:
  "side_rhs_fold_ip_eff (etf_from_tf tf) acc es cs
   = side_rhs_fold_ip tf (\<squnion>) acc es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc)
    case Nil show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    show ?case unfolding x
      by (simp add: Cons.IH pure_combine_tree_def Let_def sup_fun_def)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x
    by (simp add: Cons.IH pure_edge_tree_def Let_def sup_fun_def)
qed

lemma make_side_rhs_tree_ip_eff_etf_from_tf:
  "make_side_rhs_tree_ip_eff g (etf_from_tf tf) bot0 s0
   = make_side_rhs_tree_ip g tf (\<squnion>) bot0 s0"
  by (rule ext)
     (simp add: make_side_rhs_tree_ip_eff_def make_side_rhs_tree_ip_def
                side_rhs_fold_ip_eff_etf_from_tf Let_def)

lemma side_cfg_T_ip_eff_etf_from_tf:
  "side_cfg_T_ip_eff g (etf_from_tf tf) bot0 s0 = side_cfg_T_ip g tf (\<squnion>) bot0 s0"
  unfolding side_cfg_T_ip_eff_def side_cfg_T_ip_def
  by (rule make_side_rhs_tree_ip_eff_etf_from_tf)

end
