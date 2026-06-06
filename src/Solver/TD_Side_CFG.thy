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

end
