theory TD_Side_CFG
  imports Constraint_System_Sound IMP2_Globals "TD.TD_side"
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

lemma restrict_local_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> restrict_local (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
     \<le> restrict_local sigma2"
  unfolding restrict_local_def le_fun_def
  by (auto dest: le_funD simp: bot_least)

lemma restrict_global_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> restrict_global (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
     \<le> restrict_global sigma2"
  unfolding restrict_global_def le_fun_def
  by (auto dest: le_funD simp: bot_least)

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
     (let acc0 = (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0);
          t    = side_rhs_fold tf join acc0 (predecessor_list g v)
      in if v = cfg_entry g then Side () (restrict_global s0) t else t)"

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
(* Monotonicity in the queried assignment (join = \<squnion>). *)

lemma join_abs_state_left_mono:
  fixes join :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and acc1 acc2 s :: "'a abs_state"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes acc_le: "acc1 \<le> acc2"
  shows "join acc1 s \<le> join acc2 s"
  by (rule join_mono[OF acc_le order_refl])

lemma join_abs_state_right_mono:
  fixes join :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and s acc1 acc2 :: "'a abs_state"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes acc_le: "acc1 \<le> acc2"
  shows "join s acc1 \<le> join s acc2"
  by (rule join_mono[OF order_refl acc_le])

lemma side_acc_mono_acc:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sigma :: "pp + unit \<Rightarrow> 'a abs_state"
    and acc1 acc2 :: "'a abs_state"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  shows "acc1 \<le> acc2 \<Longrightarrow> side_acc tf join acc1 sigma ps \<le> side_acc tf join acc2 sigma ps"
proof (induction ps arbitrary: acc1 acc2)
  case Nil
  then show ?case by simp
next
  case (Cons ua ps)
  obtain u a where ua: "ua = (u, a)" by (cases ua)
  define acc1' acc2' where
    "acc1' = join acc1 (restrict_local (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ())))))" and
    "acc2' = join acc2 (restrict_local (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ())))))"
  have acc1'_le_acc2': "acc1' \<le> acc2'"
    unfolding acc1'_def acc2'_def
    by (rule join_abs_state_left_mono[OF join_mono Cons.prems])
  have inner: "side_acc tf join acc1' sigma ps \<le> side_acc tf join acc2' sigma ps"
    by (rule Cons.IH[OF acc1'_le_acc2'])
  then show ?case
    using inner unfolding ua acc1'_def acc2'_def side_acc.simps by simp
qed

lemma side_acc_mono:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_acc tf join acc sigma1 ps \<le> side_acc tf join acc sigma2 ps"
proof (induction ps arbitrary: acc)
  case Nil
  show ?case by simp
next
  case (Cons ua ps)
  obtain u a where ua: "ua = (u, a)" by (cases ua)
  define su1 su2 where
    "su1 = join (sigma1 (Inl u)) (sigma1 (Inr ()))" and
    "su2 = join (sigma2 (Inl u)) (sigma2 (Inr ()))"
  define acc1 acc2 where
    "acc1 = join acc (restrict_local (apply_tf tf a su1))" and
    "acc2 = join acc (restrict_local (apply_tf tf a su2))"
  have su_le: "su1 \<le> su2"
    using join_mono sigma_le unfolding su1_def su2_def le_fun_def by auto
  have tf_le: "apply_tf tf a su1 \<le> apply_tf tf a su2"
    by (rule tf_mono[OF su_le])
  have loc_le: "restrict_local (apply_tf tf a su1)
                 \<le> restrict_local (apply_tf tf a su2)"
    by (rule restrict_local_mono[OF tf_le])
  have acc1_le_acc2: "acc1 \<le> acc2"
    unfolding acc1_def acc2_def
    by (rule join_abs_state_right_mono[OF join_mono loc_le])
  have step1: "side_acc tf join acc1 sigma1 ps \<le> side_acc tf join acc1 sigma2 ps"
    by (rule Cons.IH)
  have step2: "side_acc tf join acc1 sigma2 ps \<le> side_acc tf join acc2 sigma2 ps"
    by (rule side_acc_mono_acc[OF join_mono acc1_le_acc2])
  have step1': "side_acc tf join (join acc (restrict_local (apply_tf tf a (join (sigma1 (Inl u)) (sigma1 (Inr ())))))) sigma1 ps
              \<le> side_acc tf join (join acc (restrict_local (apply_tf tf a (join (sigma1 (Inl u)) (sigma1 (Inr ())))))) sigma2 ps"
    using step1 unfolding acc1_def su1_def by simp
  have step2': "side_acc tf join (join acc (restrict_local (apply_tf tf a (join (sigma1 (Inl u)) (sigma1 (Inr ())))))) sigma2 ps
              \<le> side_acc tf join (join acc (restrict_local (apply_tf tf a (join (sigma2 (Inl u)) (sigma2 (Inr ())))))) sigma2 ps"
    using step2 unfolding acc1_def acc2_def su1_def su2_def by simp
  show ?case unfolding ua side_acc.simps
    by (rule order_trans[OF step1' step2'])
qed

lemma side_acc_mono_sup:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_acc tf (\<squnion>) acc sigma1 ps \<le> side_acc tf (\<squnion>) acc sigma2 ps"
  by (rule side_acc_mono[OF tf_mono sup_mono sigma_le])

lemma side_glob_mono:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_glob tf join sigma1 ps \<le> side_glob tf join sigma2 ps"
proof (induction ps)
  case Nil
  show ?case by simp
next
  case (Cons ua ps)
  obtain u a where ua: "ua = (u, a)" by (cases ua)
  define su1 su2 where
    "su1 = join (sigma1 (Inl u)) (sigma1 (Inr ()))" and
    "su2 = join (sigma2 (Inl u)) (sigma2 (Inr ()))"
  have su_le: "su1 \<le> su2"
    using join_mono sigma_le unfolding su1_def su2_def le_fun_def by auto
  have glob_le: "restrict_global (apply_tf tf a su1)
                  \<le> restrict_global (apply_tf tf a su2)"
    by (rule restrict_global_mono[OF tf_mono[OF su_le]])
  show ?case unfolding ua su1_def su2_def
    using sup_mono[OF Cons.IH glob_le]
    by (metis side_glob.simps(2) su1_def su2_def)
qed

lemma side_glob_mono_sup:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_glob tf (\<squnion>) sigma1 ps \<le> side_glob tf (\<squnion>) sigma2 ps"
  by (rule side_glob_mono[OF tf_mono sup_mono sigma_le])

(* acc in side_rhs_fold does not affect dep_aux. *)
lemma dep_aux_side_rhs_fold_acc_indep:
  "dep_aux sigma (side_rhs_fold tf join acc1 ps)
   = dep_aux sigma (side_rhs_fold tf join acc2 ps)"
proof (induction ps arbitrary: acc1 acc2)
  case Nil
  show ?case by simp
next
  case (Cons ua ps)
  obtain u a where ua: "ua = (u, a)" by (cases ua)
  show ?case unfolding ua side_rhs_fold.simps dep_aux.simps Let_def
    using Cons.IH[of "join acc1 (restrict_local (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ())))))"
                  "join acc2 (restrict_local (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ())))))"]
    by simp
qed

(* Dependencies of side_rhs_fold trees depend only on the edge list, not sigma. *)
lemma dep_aux_side_rhs_fold_indep:
  "dep_aux sigma1 (side_rhs_fold tf join acc ps)
   = dep_aux sigma2 (side_rhs_fold tf join acc ps)"
proof (induction ps arbitrary: acc sigma1 sigma2)
  case Nil
  show ?case by simp
next
  case (Cons ua ps)
  obtain u a where ua: "ua = (u, a)" by (cases ua)
  define acc1 acc2 where
    "acc1 = join acc (restrict_local (apply_tf tf a (join (sigma1 (Inl u)) (sigma1 (Inr ())))))" and
    "acc2 = join acc (restrict_local (apply_tf tf a (join (sigma2 (Inl u)) (sigma2 (Inr ())))))"
  have inner: "dep_aux sigma1 (side_rhs_fold tf join acc1 ps)
              = dep_aux sigma2 (side_rhs_fold tf join acc2 ps)"
  proof -
    have "dep_aux sigma1 (side_rhs_fold tf join acc1 ps)
          = dep_aux sigma1 (side_rhs_fold tf join acc ps)"
      by (rule dep_aux_side_rhs_fold_acc_indep[symmetric])
    also have "... = dep_aux sigma2 (side_rhs_fold tf join acc ps)"
      by (rule Cons.IH)
    also have "... = dep_aux sigma2 (side_rhs_fold tf join acc2 ps)"
      by (rule dep_aux_side_rhs_fold_acc_indep)
    finally show ?thesis .
  qed
  show ?case unfolding ua side_rhs_fold.simps dep_aux.simps Let_def
    using inner unfolding acc1_def acc2_def by simp
qed


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

(* The entry node additionally seeds the initial globals into the single global
   unknown via its wrapping Side (); every other node is the bare fold. *)
lemma sides_make_side_rhs_tree_Inr:
  "sides_of_rhs (make_side_rhs_tree g tf join bot0 s0 v) sigma (Inr ())
   = side_glob tf join sigma (predecessor_list g v)
      \<squnion> (if v = cfg_entry g then restrict_global s0 else bot)"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_def Let_def
    using True by (simp add: sides_side_rhs_fold_Inr Let_def)
next
  case False
  show ?thesis unfolding make_side_rhs_tree_def Let_def
    using False by (simp add: sides_side_rhs_fold_Inr Let_def)
qed

lemma sides_make_side_rhs_tree_Inl:
  "sides_of_rhs (make_side_rhs_tree g tf join bot0 s0 v) sigma (Inl u) = bot"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_def Let_def
    using True by (simp add: sides_side_rhs_fold_Inl Let_def)
next
  case False
  show ?thesis unfolding make_side_rhs_tree_def Let_def
    using False by (simp add: sides_side_rhs_fold_Inl Let_def)
qed

(* The wrapping Side () is invisible to dep_aux, so dependencies are still the
   fold's -- in particular independent of sigma. *)
lemma dep_aux_make_side_rhs_tree:
  "dep_aux sigma (make_side_rhs_tree g tf join bot0 s0 v)
   = dep_aux sigma (side_rhs_fold tf join
        (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0)
        (predecessor_list g v))"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_def Let_def using True by simp
next
  case False
  show ?thesis unfolding make_side_rhs_tree_def Let_def using False by simp
qed

(* -- Monotonicity of side_cfg_T (TD_side solver precondition) ---------- *)

lemma side_cfg_T_is_mono_eq:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  shows "is_mono_eq (side_cfg_T g tf (\<squnion>) bot0 s0)"
  unfolding is_mono_eq_def side_cfg_T_def
  by (simp add: make_side_rhs_tree_def side_acc_mono_sup tf_mono traverse_side_rhs_fold)
 

lemma side_cfg_T_mono_sides:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  shows "mono_sides (side_cfg_T g tf (\<squnion>) bot0 s0)"
proof (unfold mono_sides_def, intro allI impI)
  fix w :: pp and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assume le: "sigma1 \<le> sigma2"
  show "sides_of_rhs (side_cfg_T g tf (\<squnion>) bot0 s0 w) sigma1
        \<le> sides_of_rhs (side_cfg_T g tf (\<squnion>) bot0 s0 w) sigma2"
  proof (rule le_funI)
    fix x :: "pp + unit"
    show "sides_of_rhs (side_cfg_T g tf (\<squnion>) bot0 s0 w) sigma1 x
          \<le> sides_of_rhs (side_cfg_T g tf (\<squnion>) bot0 s0 w) sigma2 x"
    proof (cases x)
      case (Inl b)
      thus ?thesis
        unfolding side_cfg_T_def by (simp add: sides_make_side_rhs_tree_Inl)
    next
      case (Inr b)
      have e1: "sides_of_rhs (side_cfg_T g tf (\<squnion>) bot0 s0 w) sigma1 x
                = side_glob tf (\<squnion>) sigma1 (predecessor_list g w)
                  \<squnion> (if w = cfg_entry g then restrict_global s0 else bot)"
        unfolding side_cfg_T_def Inr by (simp add: sides_make_side_rhs_tree_Inr)
      have e2: "sides_of_rhs (side_cfg_T g tf (\<squnion>) bot0 s0 w) sigma2 x
                = side_glob tf (\<squnion>) sigma2 (predecessor_list g w)
                  \<squnion> (if w = cfg_entry g then restrict_global s0 else bot)"
        unfolding side_cfg_T_def Inr by (simp add: sides_make_side_rhs_tree_Inr)
      show ?thesis unfolding e1 e2
        by (rule sup_mono[OF side_glob_mono_sup[OF tf_mono le] order_refl])
    qed
  qed
qed

lemma side_cfg_T_mono_deps:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state"
  shows "mono_deps (side_cfg_T g tf (\<squnion>) bot0 s0)"
  unfolding mono_deps_def side_cfg_T_def dep_def
  apply clarify
  apply (simp only: dep_aux_make_side_rhs_tree)
  apply (subst (asm) dep_aux_side_rhs_fold_indep)
  by simp

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
  hence le: "sides_of_rhs (side_cfg_T g tf join bot0 s0 v) sigma (Inr ()) \<le> sigma (Inr ())"
    by (simp add: le_fun_def)
  have "side_glob tf join sigma (predecessor_list g v)
        \<le> sides_of_rhs (side_cfg_T g tf join bot0 s0 v) sigma (Inr ())"
    unfolding side_cfg_T_def
    by (simp add: sides_make_side_rhs_tree_Inr)
  thus ?thesis using le by (rule order_trans)
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

(* -- Entry coverage from an arbitrary initial state ------------------ *)

(* The entry node's wrapping Side () contributes restrict_global s0 to the
   single global unknown, so the initial globals are below it in any
   post-solution. *)
lemma restrict_global_s0_le_global:
  assumes pp: "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) x sigma vars"
      and entry_in: "cfg_entry g \<in> vars"
  shows "restrict_global s0 \<le> sigma (Inr ())"
proof -
  from pp entry_in have "sides_of_rhs (side_cfg_T g tf (\<squnion>) bot0 s0 (cfg_entry g)) sigma \<le> sigma"
    by auto
  hence le: "sides_of_rhs (side_cfg_T g tf (\<squnion>) bot0 s0 (cfg_entry g)) sigma (Inr ())
             \<le> sigma (Inr ())"
    by (simp add: le_fun_def)
  have "restrict_global s0
        \<le> side_glob tf (\<squnion>) sigma (predecessor_list g (cfg_entry g)) \<squnion> restrict_global s0"
    by (rule sup_ge2)
  also have "... = sides_of_rhs (side_cfg_T g tf (\<squnion>) bot0 s0 (cfg_entry g)) sigma (Inr ())"
    unfolding side_cfg_T_def by (simp add: sides_make_side_rhs_tree_Inr)
  also have "... \<le> sigma (Inr ())" by (rule le)
  finally show ?thesis .
qed

(* At the entry point the local fold seeds restrict_local s0 and the wrapping
   Side () seeds restrict_global s0, so s0 itself is below the combined env at
   the entry -- for an arbitrary initial state, no globals-free hypothesis. *)
lemma s0_le_side_env_entry:
  assumes pp: "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) v0 sigma vars"
      and entry_in: "cfg_entry g \<in> vars"
  shows "s0 \<le> side_env sigma (cfg_entry g)"
proof -
  have acc_le: "side_acc tf (\<squnion>) (bot0 \<squnion> restrict_local s0) sigma
                  (predecessor_list g (cfg_entry g)) \<le> sigma (Inl (cfg_entry g))"
    using side_post_solution_le_local[OF pp entry_in] by simp
  have "restrict_local s0 \<le> bot0 \<squnion> restrict_local s0" by simp
  also have "... \<le> side_acc tf (\<squnion>) (bot0 \<squnion> restrict_local s0) sigma
                     (predecessor_list g (cfg_entry g))"
    by (rule side_acc_ge_acc)
  also have "... \<le> sigma (Inl (cfg_entry g))" by (rule acc_le)
  finally have rl: "restrict_local s0 \<le> sigma (Inl (cfg_entry g))" .
  have rg: "restrict_global s0 \<le> sigma (Inr ())"
    by (rule restrict_global_s0_le_global[OF pp entry_in])
  have "s0 = restrict_local s0 \<squnion> restrict_global s0"
    by (rule restrict_local_global_join[symmetric])
  also have "... \<le> sigma (Inl (cfg_entry g)) \<squnion> sigma (Inr ())"
    using rl rg by (rule sup_mono)
  finally show ?thesis unfolding side_env_def .
qed

(* -- Dependency / reachability (solver stable set) ------------------- *)

lemma dep_side_rhs_fold:
  assumes mem: "(u, a) \<in> set ps"
  shows "Inl u \<in> dep_aux sigma (side_rhs_fold tf join acc ps)"
  using assms
proof (induction ps arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons ua ps)
  obtain u0 a0 where ua: "ua = (u0, a0)" by (cases ua)
  show ?case
  proof (cases "ua = (u, a)")
    case True
    then show ?thesis unfolding ua by auto
  next
    case False
    have mem_ps: "(u, a) \<in> set ps" using Cons.prems ua False by auto
    then show ?thesis unfolding ua side_rhs_fold.simps dep_aux.simps Let_def
      using Cons.IH by auto
  qed
qed

lemma dep_side_rhs_tree_pred:
  assumes fin: "finite (edges g)"
  assumes pred: "(u, a) \<in> predecessors g w"
  shows "u \<in> dep\<^sub>L (side_cfg_T g tf join bot0 s0) sigma w"
proof -
  have mem: "(u, a) \<in> set (predecessor_list g w)"
    using pred fin by (auto simp: predecessors_def set_predecessor_list)
  have "Inl u \<in> dep_aux sigma (make_side_rhs_tree g tf join bot0 s0 w)"
    unfolding dep_aux_make_side_rhs_tree
    by (rule dep_side_rhs_fold[OF mem])
  thus ?thesis unfolding side_cfg_T_def dep\<^sub>L_def dep_def by simp
qed

lemma dep_side_rhs_tree_edge:
  assumes fin: "finite (edges g)"
  assumes ed: "(u, a, w) \<in> edges g"
  shows "u \<in> dep\<^sub>L (side_cfg_T g tf join bot0 s0) sigma w"
  using dep_side_rhs_tree_pred[OF fin, unfolded predecessors_def] ed by auto

lemma trans_dep\<^sub>L_step_in:
  fixes T :: "(pp, unit, 'd::order_bot) eqsT"
  assumes "y \<in> dep\<^sub>L T sigma x"
  shows "y \<in> trans_dep\<^sub>L T sigma x"
  using assms by blast

lemma trans_dep\<^sub>L_trans:
  fixes T :: "(pp, unit, 'd::order_bot) eqsT"
  assumes "y \<in> trans_dep\<^sub>L T sigma x"
    and "z \<in> dep\<^sub>L T sigma y"
  shows "z \<in> trans_dep\<^sub>L T sigma x"
  by (metis Nitpick.tranclp_unfold assms(1,2) mem_Collect_eq tranclp.trancl_into_trancl)
 

lemma cfg_path_node_in_trans_dep_side:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state" and sigma :: "pp + unit \<Rightarrow> 'a abs_state"
    and w v0 :: pp and es :: "(edge_action * pp) list"
  assumes fin: "finite (edges g)"
  assumes path: "g \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> v0"
  assumes w_ne: "w \<noteq> v0"
  shows "w \<in> trans_dep\<^sub>L (side_cfg_T g tf (\<squnion>) bot0 s0) sigma v0"
proof (cases "w = v0")
  case True
  with w_ne show ?thesis by simp
next
  case False
  show ?thesis using path False
  proof (induction es arbitrary: w)
    case Nil
    then show ?case using cfg_path_ne_nil by auto
  next
    case (Cons e es')
    obtain a w' where ew: "e = (a, w')" by (cases e) auto
    have path': "g \<turnstile> w \<longrightarrow>\<^bsub>(a, w') # es'\<^esub> v0"
      using path Cons ew by simp
    have ed: "(w, a, w') \<in> edges g"
      by (rule cfg_path_ConsD_edge[OF path'])
    have p2: "g \<turnstile> w' \<longrightarrow>\<^bsub>es'\<^esub> v0"
      by (rule cfg_path_ConsD_rest[OF path'])
    have w_dep: "w \<in> dep\<^sub>L (side_cfg_T g tf (\<lambda>a b c. a c \<squnion> b c) bot0 s0) sigma w'"
      using dep_side_rhs_tree_edge[OF fin ed] by blast
    show ?case
    proof (cases "w' = v0")
      case True
      show ?thesis
        using w_dep trans_dep\<^sub>L_step_in True
        by (auto simp: side_cfg_T_def fun_eq_iff)
    next
      case False
      have w'_in: "w' \<in> trans_dep\<^sub>L (side_cfg_T g tf (\<lambda>a b c. a c \<squnion> b c) bot0 s0) sigma v0"
        using Cons.IH[OF p2 False] by (simp add: side_cfg_T_def fun_eq_iff)
      show ?thesis
        using w_dep w'_in trans_dep\<^sub>L_trans
        by (auto simp: side_cfg_T_def fun_eq_iff)
    qed
  qed
qed



lemma side_vars_on_query_path:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state" and sigma :: "pp + unit \<Rightarrow> 'a abs_state"
    and v0 w :: pp and vars :: "pp set"
  assumes pp: "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) v0 sigma vars"
  assumes fin: "finite (edges g)"
  assumes suffix: "g \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> v0"
  shows "w \<in> vars"
proof (cases "w = v0")
  case True
  then show ?thesis using pp by auto
next
  case False
  have "w \<in> trans_dep\<^sub>L (side_cfg_T g tf (\<squnion>) bot0 s0) sigma v0"
    using cfg_path_node_in_trans_dep_side[OF fin suffix False] by simp
  moreover have "trans_dep\<^sub>L (side_cfg_T g tf (\<squnion>) bot0 s0) sigma v0 \<subseteq> vars"
    using part_post_solution_implies_trans_dep_subsumed[OF pp] by simp
  ultimately show ?thesis by blast
qed

lemma cfg_path_entry_step_target:
  assumes step: "g \<turnstile> x \<longrightarrow>\<^bsub>(a, w) # es'\<^esub> v"
  assumes prefix: "g \<turnstile> cfg_entry g \<longrightarrow>\<^bsub>es1\<^esub> x"
  shows "g \<turnstile> cfg_entry g \<longrightarrow>\<^bsub>es1 @ [(a, w)]\<^esub> w"
  using cfg_path_on_path_step[OF prefix step] .

(* -- Collecting soundness of a side-effecting post-solution (M3) ------ *)

context sound_transfer
begin

(*
  The combined env of a side_cfg_T post-solution soundly over-approximates the
  CFG collecting semantics at every program point reachable from the entry:
  along any path, the stores collected from S stay within the concretisation of
  the combined env.  Globals are tracked flow-insensitively (one global unknown,
  joined across all points), locals flow-sensitively.

  Assumptions: sigma is a partial post-solution over vars covering all program
  points; the initial set S is covered by the combined env at the entry.
*)
theorem side_collect_sound_path:
  fixes sigma :: "pp + unit => 'a abs_state"
    and bot0 s0 :: "'a abs_state"
  assumes pp: "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) v sigma vars"
  assumes fin: "finite (edges g)"
  assumes entry: "S \<subseteq> gamma_state (side_env sigma (cfg_entry g))"
  assumes path: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v"
  assumes t_in: "t \<in> edges_collect es S"
  shows "t \<in> gamma_state (side_env sigma v)"
proof -
  have step_le: "\<And>x b y es'. g \<turnstile> x \<longrightarrow>\<^bsub>(b, y) # es'\<^esub> v
     \<Longrightarrow> apply_tf tf b (side_env sigma x) \<le> side_env sigma y"
  proof -
    fix x b y es'
    assume p: "g \<turnstile> x \<longrightarrow>\<^bsub>(b, y) # es'\<^esub> v"
    obtain edge where edge: "(x, b, y) \<in> edges g"
      using p by (cases rule: cfg_stepE) auto
    have y_suf: "g \<turnstile> y \<longrightarrow>\<^bsub>es'\<^esub> v"
      using p by (cases rule: cfg_stepE) auto
    have y_in: "y \<in> vars"
      using side_vars_on_query_path[OF pp fin y_suf] by simp
    show "apply_tf tf b (side_env sigma x) \<le> side_env sigma y"
      by (rule apply_tf_combined_le[OF pp y_in edge fin])
  qed
  have collect: "edges_collect es (gamma_state (side_env sigma (cfg_entry g)))
                 \<subseteq> gamma_state (side_env sigma v)"
    by (rule edges_collect_gamma_path_aux[OF fin path step_le])
  have "edges_collect es S
        \<subseteq> edges_collect es (gamma_state (side_env sigma (cfg_entry g)))"
    by (rule edges_collect_mono_strong[OF entry])
  thus ?thesis using collect t_in by blast
qed

(* Subset form: any store collected at v lies in the side env at v. *)
corollary side_collect_sound_at:
  fixes sigma :: "pp + unit => 'a abs_state"
    and bot0 s0 :: "'a abs_state"
  assumes pp: "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) v sigma vars"
  assumes fin: "finite (edges g)"
  assumes entry: "S \<subseteq> gamma_state (side_env sigma (cfg_entry g))"
  assumes path: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v"
  shows "cfg_collect g S v \<le> gamma_state (side_env sigma v)"
proof -
  have paths: "cfg_collect g S v \<subseteq> cfg_collect_paths g S v"
    by (rule cfg_collect_le_paths)
  show ?thesis
  proof
    fix t
    assume "t \<in> cfg_collect g S v"
    with paths have "t \<in> cfg_collect_paths g S v" by blast
    then obtain path_es where path_es: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>path_es\<^esub> v"
      and t_in: "t \<in> edges_collect path_es S"
      unfolding cfg_collect_paths_def by blast
    show "t \<in> gamma_state (side_env sigma v)"
      by (rule side_collect_sound_path[OF pp fin entry path_es t_in])
  qed
qed

end

end
