theory TD_Side_IP_CFG
  imports TD_Side_CFG CFG_Collect_IP
begin

(*
  Side-effecting constraint system over an INTERPROCEDURAL CFG, with a
  locals/globals split.  This is the IP analogue of TD_Side_CFG: the intra
  encoding handles ordinary edges; here we additionally fold the incoming
  combine triples of each return point.

  For a return point v, combines g contains triples (call, proc_exit, v).
  The combined abstract state combine_abs sc se takes locals from the caller
  sc and globals from the callee exit se -- exactly restrict_local sc join
  restrict_global se.  As with edges, the local part flows on to v's local
  unknown and the global part is contributed to the single global unknown by a
  side effect.
*)

(* -- Strategy tree ---------------------------------------------------- *)

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
     (let acc0 = (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0)
      in side_rhs_fold_ip tf join acc0
           (predecessor_list g v) (combine_predecessor_list g v))"

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

(* -- Denotation: local fold ------------------------------------------- *)

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

(* -- Denotation: global contribution ---------------------------------- *)

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

(* -- Monotonicity of the local fold ----------------------------------- *)

lemma side_acc_ip_mono_acc:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sigma :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  shows "acc1 \<le> acc2 \<Longrightarrow>
         side_acc_ip tf join acc1 sigma es cs \<le> side_acc_ip tf join acc2 sigma es cs"
proof (induction es arbitrary: acc1 acc2 cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc1 acc2)
    case Nil
    then show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have jle: "join acc1 (restrict_local (join (sigma (Inl cc)) (sigma (Inr ()))))
             \<le> join acc2 (restrict_local (join (sigma (Inl cc)) (sigma (Inr ()))))"
      by (rule join_abs_state_left_mono[OF join_mono Cons.prems])
    show ?case unfolding x
      using Cons.IH[OF jle] by simp
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have jle: "join acc1 (restrict_local (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ())))))
           \<le> join acc2 (restrict_local (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ())))))"
    by (rule join_abs_state_left_mono[OF join_mono Cons.prems])
  show ?case unfolding x
    using Cons.IH[OF jle] by simp
qed

lemma side_acc_ip_mono:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_acc_ip tf join acc sigma1 es cs \<le> side_acc_ip tf join acc sigma2 es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc)
    case Nil
    show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have su_le: "join (sigma1 (Inl cc)) (sigma1 (Inr ())) \<le> join (sigma2 (Inl cc)) (sigma2 (Inr ()))"
      using join_mono sigma_le unfolding le_fun_def by auto
    have loc_le: "restrict_local (join (sigma1 (Inl cc)) (sigma1 (Inr ())))
                 \<le> restrict_local (join (sigma2 (Inl cc)) (sigma2 (Inr ())))"
      by (rule restrict_local_mono[OF su_le])
    have acc_le: "join acc (restrict_local (join (sigma1 (Inl cc)) (sigma1 (Inr ()))))
                \<le> join acc (restrict_local (join (sigma2 (Inl cc)) (sigma2 (Inr ()))))"
      by (rule join_abs_state_right_mono[OF join_mono loc_le])
    have step1: "side_acc_ip tf join (join acc (restrict_local (join (sigma1 (Inl cc)) (sigma1 (Inr ()))))) sigma1 [] cs
               \<le> side_acc_ip tf join (join acc (restrict_local (join (sigma1 (Inl cc)) (sigma1 (Inr ()))))) sigma2 [] cs"
      by (rule Cons.IH)
    have step2: "side_acc_ip tf join (join acc (restrict_local (join (sigma1 (Inl cc)) (sigma1 (Inr ()))))) sigma2 [] cs
               \<le> side_acc_ip tf join (join acc (restrict_local (join (sigma2 (Inl cc)) (sigma2 (Inr ()))))) sigma2 [] cs"
      by (rule side_acc_ip_mono_acc[OF join_mono acc_le])
    show ?case unfolding x
      using order_trans[OF step1 step2] by simp
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have su_le: "join (sigma1 (Inl u)) (sigma1 (Inr ())) \<le> join (sigma2 (Inl u)) (sigma2 (Inr ()))"
    using join_mono sigma_le unfolding le_fun_def by auto
  have loc_le: "restrict_local (apply_tf tf a (join (sigma1 (Inl u)) (sigma1 (Inr ()))))
               \<le> restrict_local (apply_tf tf a (join (sigma2 (Inl u)) (sigma2 (Inr ()))))"
    by (rule restrict_local_mono[OF tf_mono[OF su_le]])
  have acc_le: "join acc (restrict_local (apply_tf tf a (join (sigma1 (Inl u)) (sigma1 (Inr ())))))
              \<le> join acc (restrict_local (apply_tf tf a (join (sigma2 (Inl u)) (sigma2 (Inr ())))))"
    by (rule join_abs_state_right_mono[OF join_mono loc_le])
  have step1: "side_acc_ip tf join (join acc (restrict_local (apply_tf tf a (join (sigma1 (Inl u)) (sigma1 (Inr ())))))) sigma1 es cs
             \<le> side_acc_ip tf join (join acc (restrict_local (apply_tf tf a (join (sigma1 (Inl u)) (sigma1 (Inr ())))))) sigma2 es cs"
    by (rule Cons.IH)
  have step2: "side_acc_ip tf join (join acc (restrict_local (apply_tf tf a (join (sigma1 (Inl u)) (sigma1 (Inr ())))))) sigma2 es cs
             \<le> side_acc_ip tf join (join acc (restrict_local (apply_tf tf a (join (sigma2 (Inl u)) (sigma2 (Inr ())))))) sigma2 es cs"
    by (rule side_acc_ip_mono_acc[OF join_mono acc_le])
  show ?case unfolding x
    using order_trans[OF step1 step2] by simp
qed

lemma side_acc_ip_mono_sup:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_acc_ip tf (\<squnion>) acc sigma1 es cs \<le> side_acc_ip tf (\<squnion>) acc sigma2 es cs"
  by (rule side_acc_ip_mono[OF tf_mono sup_mono sigma_le])

(* -- Monotonicity of the global contribution -------------------------- *)

lemma side_glob_ip_mono:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_glob_ip tf join sigma1 es cs \<le> side_glob_ip tf join sigma2 es cs"
proof (induction es arbitrary: cs)
  case Nil
  show ?case
  proof (induction cs)
    case Nil
    show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have su_le: "join (sigma1 (Inl ex)) (sigma1 (Inr ())) \<le> join (sigma2 (Inl ex)) (sigma2 (Inr ()))"
      using join_mono sigma_le unfolding le_fun_def by auto
    have glob_le: "restrict_global (join (sigma1 (Inl ex)) (sigma1 (Inr ())))
                  \<le> restrict_global (join (sigma2 (Inl ex)) (sigma2 (Inr ())))"
      by (rule restrict_global_mono[OF su_le])
    show ?case unfolding x side_glob_ip.simps(3)
      by (rule sup_mono[OF Cons.IH glob_le])
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have ih: "side_glob_ip tf join sigma1 es cs \<le> side_glob_ip tf join sigma2 es cs"
    by (rule Cons.IH)
  have su_le: "join (sigma1 (Inl u)) (sigma1 (Inr ())) \<le> join (sigma2 (Inl u)) (sigma2 (Inr ()))"
    using join_mono sigma_le unfolding le_fun_def by auto
  have glob_le: "restrict_global (apply_tf tf a (join (sigma1 (Inl u)) (sigma1 (Inr ()))))
                \<le> restrict_global (apply_tf tf a (join (sigma2 (Inl u)) (sigma2 (Inr ()))))"
    by (rule restrict_global_mono[OF tf_mono[OF su_le]])
  show ?case unfolding x side_glob_ip.simps(2)
    by (rule sup_mono[OF ih glob_le])
qed

lemma side_glob_ip_mono_sup:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_glob_ip tf (\<squnion>) sigma1 es cs \<le> side_glob_ip tf (\<squnion>) sigma2 es cs"
  by (rule side_glob_ip_mono[OF tf_mono sup_mono sigma_le])

(* -- Dependencies are independent of acc and of sigma ----------------- *)

lemma dep_aux_side_rhs_fold_ip_acc_indep:
  "dep_aux sigma (side_rhs_fold_ip tf join acc1 es cs)
   = dep_aux sigma (side_rhs_fold_ip tf join acc2 es cs)"
proof (induction es arbitrary: acc1 acc2 cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc1 acc2)
    case Nil
    show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    show ?case unfolding x side_rhs_fold_ip.simps dep_aux.simps Let_def
      using Cons.IH[of "join acc1 (restrict_local (restrict_local (join (sigma (Inl cc)) (sigma (Inr ()))) \<squnion> restrict_global (join (sigma (Inl ex)) (sigma (Inr ())))))"
                       "join acc2 (restrict_local (restrict_local (join (sigma (Inl cc)) (sigma (Inr ()))) \<squnion> restrict_global (join (sigma (Inl ex)) (sigma (Inr ()))))) "]
      by simp
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have step: "dep_aux sigma (side_rhs_fold_ip tf join (join acc1 (restrict_local (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ())))))) es cs)
            = dep_aux sigma (side_rhs_fold_ip tf join (join acc2 (restrict_local (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ())))))) es cs)"
    by (rule Cons.IH)
  show ?case unfolding x side_rhs_fold_ip.simps dep_aux.simps Let_def
    using step by simp
qed

lemma dep_aux_side_rhs_fold_ip_indep:
  "dep_aux sigma1 (side_rhs_fold_ip tf join acc es cs)
   = dep_aux sigma2 (side_rhs_fold_ip tf join acc es cs)"
proof (induction es arbitrary: acc cs sigma1 sigma2)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc sigma1 sigma2)
    case Nil
    show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    define acc1 acc2 where
      "acc1 = join acc (restrict_local (restrict_local (join (sigma1 (Inl cc)) (sigma1 (Inr ()))) \<squnion> restrict_global (join (sigma1 (Inl ex)) (sigma1 (Inr ())))))" and
      "acc2 = join acc (restrict_local (restrict_local (join (sigma2 (Inl cc)) (sigma2 (Inr ()))) \<squnion> restrict_global (join (sigma2 (Inl ex)) (sigma2 (Inr ())))))"
    have inner: "dep_aux sigma1 (side_rhs_fold_ip tf join acc1 [] cs)
                = dep_aux sigma2 (side_rhs_fold_ip tf join acc2 [] cs)"
    proof -
      have "dep_aux sigma1 (side_rhs_fold_ip tf join acc1 [] cs)
            = dep_aux sigma1 (side_rhs_fold_ip tf join acc [] cs)"
        by (rule dep_aux_side_rhs_fold_ip_acc_indep)
      also have "... = dep_aux sigma2 (side_rhs_fold_ip tf join acc [] cs)"
        by (rule Cons.IH)
      also have "... = dep_aux sigma2 (side_rhs_fold_ip tf join acc2 [] cs)"
        by (rule dep_aux_side_rhs_fold_ip_acc_indep)
      finally show ?thesis .
    qed
    show ?case unfolding x side_rhs_fold_ip.simps dep_aux.simps Let_def
      using inner unfolding acc1_def acc2_def by simp
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  define acc1 acc2 where
    "acc1 = join acc (restrict_local (apply_tf tf a (join (sigma1 (Inl u)) (sigma1 (Inr ())))))" and
    "acc2 = join acc (restrict_local (apply_tf tf a (join (sigma2 (Inl u)) (sigma2 (Inr ())))))"
  have inner: "dep_aux sigma1 (side_rhs_fold_ip tf join acc1 es cs)
              = dep_aux sigma2 (side_rhs_fold_ip tf join acc2 es cs)"
  proof -
    have "dep_aux sigma1 (side_rhs_fold_ip tf join acc1 es cs)
          = dep_aux sigma1 (side_rhs_fold_ip tf join acc es cs)"
      by (rule dep_aux_side_rhs_fold_ip_acc_indep)
    also have "... = dep_aux sigma2 (side_rhs_fold_ip tf join acc es cs)"
      by (rule Cons.IH)
    also have "... = dep_aux sigma2 (side_rhs_fold_ip tf join acc2 es cs)"
      by (rule dep_aux_side_rhs_fold_ip_acc_indep)
    finally show ?thesis .
  qed
  show ?case unfolding x side_rhs_fold_ip.simps dep_aux.simps Let_def
    using inner unfolding acc1_def acc2_def by simp
qed

(* -- Side contributions: all land in the global slot Inr () ----------- *)

lemma sides_side_rhs_fold_ip_Inr:
  "sides_of_rhs (side_rhs_fold_ip tf join acc es cs) sigma (Inr ())
   = side_glob_ip tf join sigma es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc)
    case Nil
    show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    show ?case unfolding x
      using Cons.IH by (simp add: Let_def restrict_global_combine_eq)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH by (simp add: Let_def)
qed

lemma sides_side_rhs_fold_ip_Inl:
  "sides_of_rhs (side_rhs_fold_ip tf join acc es cs) sigma (Inl u) = bot"
proof (induction es arbitrary: acc cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc)
    case Nil
    show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    show ?case unfolding x using Cons.IH by (simp add: Let_def)
  qed
next
  case (Cons x es)
  obtain w a where x: "x = (w, a)" by (cases x)
  show ?case unfolding x using Cons.IH by (simp add: Let_def)
qed

(* -- Solver preconditions for TD_side --------------------------------- *)

lemma side_cfg_T_ip_is_mono_eq:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  shows "is_mono_eq (side_cfg_T_ip g tf (\<squnion>) bot0 s0)"
  unfolding is_mono_eq_def side_cfg_T_ip_def
  by (simp add: make_side_rhs_tree_ip_def side_acc_ip_mono_sup tf_mono traverse_side_rhs_fold_ip)

lemma side_cfg_T_ip_mono_sides:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  shows "mono_sides (side_cfg_T_ip g tf (\<squnion>) bot0 s0)"
  unfolding mono_sides_def side_cfg_T_ip_def make_side_rhs_tree_ip_def Let_def
  apply clarify
  apply (rename_tac w sigma1 sigma2)
  apply (rule le_funI)
  apply (case_tac x rule: sum.exhaust)
   apply (simp add: sides_side_rhs_fold_ip_Inl)
  apply (simp add: sides_side_rhs_fold_ip_Inr side_glob_ip_mono_sup[OF tf_mono])
  done

lemma side_cfg_T_ip_mono_deps:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state"
  shows "mono_deps (side_cfg_T_ip g tf (\<squnion>) bot0 s0)"
  unfolding mono_deps_def side_cfg_T_ip_def make_side_rhs_tree_ip_def Let_def dep_def
  apply clarify
  apply (subst (asm) dep_aux_side_rhs_fold_ip_indep)
  by simp

end
