theory TD_Side_IP_Tree
  imports TD_Side_CFG "Voblint_CFG.CFG_Collect_IP"
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

(* The combine result keeps locals from A (caller) and globals from B (callee
   exit); its local restriction is restrict_local A, its global restriction is
   restrict_global B.  (Compare combine_abs / restrict_combine.) *)
lemma restrict_local_combine_eq:
  "restrict_local (restrict_local A \<squnion> restrict_global B) = restrict_local A"
  unfolding restrict_local_def restrict_global_def sup_fun_def by (rule ext) simp

lemma restrict_global_combine_eq:
  "restrict_global (restrict_local A \<squnion> restrict_global B) = restrict_global B"
  unfolding restrict_local_def restrict_global_def sup_fun_def by (rule ext) simp

subsection \<open>Denotation: local fold\<close>

fun side_acc_ip ::
  "'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => 'a abs_state => (pp + unit => 'a abs_state)
   => (pp * edge_action) list => (pp * pp) list => 'a abs_state"
where
  "side_acc_ip tf join acc sigma [] [] = acc"
| "side_acc_ip tf join acc sigma ((u, a) # ps) cs =
     side_acc_ip tf join
       (join acc (restrict_local (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ()))))))
       sigma ps cs"
| "side_acc_ip tf join acc sigma [] ((cc, ex) # cs) =
     side_acc_ip tf join
       (join acc (restrict_local (join (sigma (Inl cc)) (sigma (Inr ())))))
       sigma [] cs"

subsection \<open>Denotation: global contribution\<close>

fun side_glob_ip ::
  "'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => (pp + unit => 'a abs_state)
   => (pp * edge_action) list => (pp * pp) list => 'a abs_state"
where
  "side_glob_ip tf join sigma [] [] = bot"
| "side_glob_ip tf join sigma ((u, a) # ps) cs =
     side_glob_ip tf join sigma ps cs
       \<squnion> restrict_global (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ()))))"
| "side_glob_ip tf join sigma [] ((cc, ex) # cs) =
     side_glob_ip tf join sigma [] cs
       \<squnion> restrict_global (join (sigma (Inl ex)) (sigma (Inr ())))"

(* traverse_rhs (= eq) of the fold is exactly side_acc_ip. *)
lemma traverse_side_rhs_fold_ip:
  "traverse_rhs (side_rhs_fold_ip tf join acc es cs) sigma = side_acc_ip tf join acc sigma es cs"
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
  "eq (side_cfg_T_ip g tf join bot0 s0) v sigma =
     side_acc_ip tf join
       (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0)
       sigma (predecessor_list g v) (combine_predecessor_list g v)"
  unfolding side_cfg_T_ip_def make_side_rhs_tree_ip_def
  by (simp add: traverse_side_rhs_fold_ip Let_def)

end
