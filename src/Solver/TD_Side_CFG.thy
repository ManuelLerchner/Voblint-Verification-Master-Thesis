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

(* -- Post-solution in usable form ------------------------------------ *)

(* Joining the local restriction of A with the global restriction of B is the
   abstract combine: locals from A, globals from B. *)
lemma restrict_combine:
  "restrict_local A \<squnion> restrict_global B = (\<lambda>x. if is_global x then B x else A x)"
  unfolding restrict_local_def restrict_global_def sup_fun_def by (rule ext) simp

(* A post-solution of side_cfg_T bounds, at every program point in scope, the
   local fold by the local unknown and the global contribution by the single
   global unknown. *)
lemma side_post_solution_le_local:
  assumes "part_post_solution (side_cfg_T g tf join bot0 s0) x sigma vars"
      and "v \<in> vars"
  shows "side_acc tf join
           (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0)
           sigma (predecessor_list g v) \<le> sigma (Inl v)"
proof -
  from assms have "eq (side_cfg_T g tf join bot0 s0) v sigma \<le> sigma (Inl v)" by auto
  thus ?thesis by (simp add: eq_side_cfg_T)
qed

lemma side_post_solution_le_global:
  assumes "part_post_solution (side_cfg_T g tf join bot0 s0) x sigma vars"
      and "v \<in> vars"
  shows "side_glob tf join sigma (predecessor_list g v) \<le> sigma (Inr ())"
proof -
  from assms have "sides_of_rhs (side_cfg_T g tf join bot0 s0 v) sigma \<le> sigma" by auto
  hence "sides_of_rhs (side_cfg_T g tf join bot0 s0 v) sigma (Inr ()) \<le> sigma (Inr ())"
    by (simp add: le_fun_def)
  thus ?thesis
    unfolding side_cfg_T_def make_side_rhs_tree_def
    by (simp add: sides_side_rhs_fold_Inr)
qed

(* -- Fold upper bounds (join = sup) ---------------------------------- *)

lemma side_acc_ge_acc:
  "acc \<le> side_acc tf (\<squnion>) acc sigma ps"
proof (induction ps arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x ps)
  obtain u a where x: "x = (u, a)" by (cases x)
  have "acc \<le> side_acc tf (\<squnion>)
          (acc \<squnion> restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))) sigma ps"
    by (meson Cons.IH sup_ge1 order_trans)
  then show ?case unfolding x by (simp only: side_acc.simps)
qed

(* Each incoming edge's local contribution is below the local fold. *)
lemma restrict_local_le_side_acc:
  "(u, a) \<in> set ps \<Longrightarrow>
   restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
     \<le> side_acc tf (\<squnion>) acc sigma ps"
proof (induction ps arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x ps)
  obtain w b where x: "x = (w, b)" by (cases x)
  from Cons.prems x consider (hd) "(u, a) = (w, b)" | (tl) "(u, a) \<in> set ps" by auto
  then show ?case
  proof cases
    case hd
    then have uw: "u = w" and ab: "a = b" by auto
    have "restrict_local (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))
          \<le> side_acc tf (\<squnion>)
               (acc \<squnion> restrict_local (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ()))))
               sigma ps"
      using side_acc_ge_acc sup_ge2 order_trans by blast
    thus ?thesis unfolding x uw ab by (simp only: side_acc.simps)
  next
    case tl
    have "restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
          \<le> side_acc tf (\<squnion>)
               (acc \<squnion> restrict_local (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ()))))
               sigma ps"
      by (rule Cons.IH[OF tl])
    thus ?thesis unfolding x by (simp only: side_acc.simps)
  qed
qed

(* Each incoming edge's global contribution is below the global join. *)
lemma restrict_global_le_side_glob:
  "(u, a) \<in> set ps \<Longrightarrow>
   restrict_global (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
     \<le> side_glob tf (\<squnion>) sigma ps"
proof (induction ps)
  case Nil thus ?case by simp
next
  case (Cons x ps)
  obtain w b where x: "x = (w, b)" by (cases x)
  from Cons.prems x consider (hd) "(u, a) = (w, b)" | (tl) "(u, a) \<in> set ps" by auto
  then show ?case
  proof cases
    case hd
    then have uw: "u = w" and ab: "a = b" by auto
    have "restrict_global (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))
          \<le> side_glob tf (\<squnion>) sigma ps
               \<squnion> restrict_global (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))"
      by (rule sup_ge2)
    thus ?thesis unfolding x uw ab by (simp only: side_glob.simps)
  next
    case tl
    have "restrict_global (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
          \<le> side_glob tf (\<squnion>) sigma ps
               \<squnion> restrict_global (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))"
      using Cons.IH[OF tl] by (rule le_supI1)
    thus ?thesis unfolding x by (simp only: side_glob.simps)
  qed
qed

(* -- Edge step: the combined env is closed under each edge transfer -- *)

(* The abstract state combined from the local unknown at v and the single
   global unknown. *)
definition side_env ::
  "(pp + unit => 'a::bounded_semilattice_sup_bot abs_state) => pp => 'a abs_state" where
  "side_env sigma v = sigma (Inl v) \<squnion> sigma (Inr ())"

(* For any CFG edge (u, a, v), a post-solution's combined env at u, transferred
   along a, is below the combined env at v.  This is the per-edge inductive step
   of the collecting-soundness bridge. *)
lemma apply_tf_combined_le:
  assumes pp:  "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) x sigma vars"
      and v:   "v \<in> vars"
      and e:   "(u, a, v) \<in> edges g"
      and fin: "finite (edges g)"
  shows "apply_tf tf a (side_env sigma u) \<le> side_env sigma v"
proof -
  have mem: "(u, a) \<in> set (predecessor_list g v)"
    using e by (simp add: set_predecessor_list[OF fin] predecessors_def)
  have loc: "restrict_local (apply_tf tf a (side_env sigma u)) \<le> sigma (Inl v)"
    using restrict_local_le_side_acc[OF mem] side_post_solution_le_local[OF pp v]
    unfolding side_env_def by (rule order_trans)
  have glob: "restrict_global (apply_tf tf a (side_env sigma u)) \<le> sigma (Inr ())"
    using restrict_global_le_side_glob[OF mem] side_post_solution_le_global[OF pp v]
    unfolding side_env_def by (rule order_trans)
  have "apply_tf tf a (side_env sigma u)
        = restrict_local (apply_tf tf a (side_env sigma u))
          \<squnion> restrict_global (apply_tf tf a (side_env sigma u))"
    by (rule restrict_local_global_join[symmetric])
  also have "\<dots> \<le> sigma (Inl v) \<squnion> sigma (Inr ())"
    using loc glob by (rule sup_mono)
  finally show ?thesis unfolding side_env_def .
qed

end
