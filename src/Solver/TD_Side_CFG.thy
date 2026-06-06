theory TD_Side_CFG
  imports Constraint_System IMP2_Globals "TD.TD_side"
begin

(*
  Side-effecting constraint system over a CFG, with a locals/globals split.

  Local unknowns are program points (flow-sensitive); a single global unknown
  (unit) holds the flow-insensitive abstract state of the global variables.

  For a program point v, the strategy tree folds over the incoming edges: for
  each predecessor (u, a) it queries u's local state (QueryL), reads the global
  state (QueryG), applies the edge transfer to the combined state, then splits
  the result -- the local component flows on to v, the global component is
  contributed to the global unknown by a side effect (Side).
*)

(* Keep only the local (resp. global) component of an abstract state; the other
   component is set to bot, so the join of the two recovers the original. *)
definition restrict_local ::
  "'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_local sigma = (\<lambda>x. if is_global x then bot else sigma x)"

definition restrict_global ::
  "'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_global sigma = (\<lambda>x. if is_global x then sigma x else bot)"

lemma restrict_local_global_join:
  "restrict_local sigma \<squnion> restrict_global sigma = sigma"
  unfolding restrict_local_def restrict_global_def sup_fun_def by (rule ext) simp

(* Strategy tree for one program point: fold the incoming edges into a
   QueryL / QueryG / Side chain. *)
fun side_rhs_fold ::
  "'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => 'a abs_state => (pp * edge_action) list
   => (pp, unit, 'a abs_state) strategy_tree"
where
  "side_rhs_fold tf join acc [] = Answer acc"
| "side_rhs_fold tf join acc ((u, a) # ps) =
     QueryL u (\<lambda>su. QueryG () (\<lambda>glob.
       let res = apply_tf tf a (join su glob)
       in Side () (restrict_global res)
            (side_rhs_fold tf join (join acc (restrict_local res)) ps)))"

definition make_side_rhs_tree ::
  "cfg => 'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => 'a abs_state => 'a abs_state => pp
   => (pp, unit, 'a abs_state) strategy_tree"
where
  "make_side_rhs_tree g tf join bot0 s0 v =
     (let acc0 = (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0)
      in side_rhs_fold tf join acc0 (predecessor_list g v))"

(* The side-effecting equation system: one strategy tree per program point. *)
definition side_cfg_T ::
  "cfg => 'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => 'a abs_state => 'a abs_state
   => (pp, unit, 'a abs_state) eqsT"
where
  "side_cfg_T g tf join bot0 s0 = make_side_rhs_tree g tf join bot0 s0"

(* -- Denotation of the strategy tree --------------------------------- *)

(* The local value computed by traversing the tree: a left fold over the
   incoming edges, each contributing the local part of its transferred state
   (the predecessor's local value joined with the global value). *)
fun side_acc ::
  "'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => 'a abs_state => (pp + unit => 'a abs_state)
   => (pp * edge_action) list => 'a abs_state"
where
  "side_acc tf join acc sigma [] = acc"
| "side_acc tf join acc sigma ((u, a) # ps) =
     side_acc tf join
       (join acc (restrict_local (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ()))))))
       sigma ps"

(* traverse_rhs (= eq) of the fold is exactly side_acc: QueryL/QueryG resolve
   through sigma, Side is ignored by the answer traversal. *)
lemma traverse_side_rhs_fold:
  "traverse_rhs (side_rhs_fold tf join acc ps) sigma = side_acc tf join acc sigma ps"
proof (induction ps arbitrary: acc)
  case Nil
  show ?case by simp
next
  case (Cons x ps)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH by (simp add: Let_def)
qed

lemma eq_side_cfg_T:
  "eq (side_cfg_T g tf join bot0 s0) v sigma =
     side_acc tf join
       (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0)
       sigma (predecessor_list g v)"
  unfolding side_cfg_T_def make_side_rhs_tree_def
  by (simp add: traverse_side_rhs_fold Let_def)

(* The global contribution: the join over incoming edges of the global part of
   each transferred state.  (Independent of the local accumulator.) *)
fun side_glob ::
  "'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => (pp + unit => 'a abs_state) => (pp * edge_action) list => 'a abs_state"
where
  "side_glob tf join sigma [] = bot"
| "side_glob tf join sigma ((u, a) # ps) =
     side_glob tf join sigma ps
       \<squnion> restrict_global (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ()))))"

(* sides_of_rhs of the fold: all contributions land in the single global slot
   Inr (); the local slots receive nothing. *)
lemma sides_side_rhs_fold_Inr:
  "sides_of_rhs (side_rhs_fold tf join acc ps) sigma (Inr ()) = side_glob tf join sigma ps"
proof (induction ps arbitrary: acc)
  case Nil
  show ?case by simp
next
  case (Cons x ps)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH by (simp add: Let_def)
qed

lemma sides_side_rhs_fold_Inl:
  "sides_of_rhs (side_rhs_fold tf join acc ps) sigma (Inl u) = bot"
proof (induction ps arbitrary: acc)
  case Nil
  show ?case by simp
next
  case (Cons x ps)
  obtain w a where x: "x = (w, a)" by (cases x)
  show ?case unfolding x using Cons.IH by (simp add: Let_def)
qed

end
