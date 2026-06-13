theory TD_Side_IP_CFG
  imports TD_Side_CFG "Voblint_CFG.CFG_Collect_IP"
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

(* The entry node additionally seeds the initial globals into the single global
   unknown via its wrapping Side ();  every other node is the bare fold. *)
lemma sides_make_side_rhs_tree_ip_Inr:
  "sides_of_rhs (make_side_rhs_tree_ip g tf join bot0 s0 v) sigma (Inr ())
   = side_glob_ip tf join sigma (predecessor_list g v) (combine_predecessor_list g v)
      \<squnion> (if v = cfg_entry g then restrict_global s0 else bot)"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_ip_def Let_def
    using True by (simp add: sides_side_rhs_fold_ip_Inr Let_def)
next
  case False
  show ?thesis unfolding make_side_rhs_tree_ip_def Let_def
    using False by (simp add: sides_side_rhs_fold_ip_Inr Let_def)
qed

lemma sides_make_side_rhs_tree_ip_Inl:
  "sides_of_rhs (make_side_rhs_tree_ip g tf join bot0 s0 v) sigma (Inl u) = bot"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_ip_def Let_def
    using True by (simp add: sides_side_rhs_fold_ip_Inl Let_def)
next
  case False
  show ?thesis unfolding make_side_rhs_tree_ip_def Let_def
    using False by (simp add: sides_side_rhs_fold_ip_Inl Let_def)
qed

(* The wrapping Side () is invisible to dep_aux, so dependencies are still the
   fold's -- in particular independent of sigma. *)
lemma dep_aux_make_side_rhs_tree_ip:
  "dep_aux sigma (make_side_rhs_tree_ip g tf join bot0 s0 v)
   = dep_aux sigma (side_rhs_fold_ip tf join
        (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0)
        (predecessor_list g v) (combine_predecessor_list g v))"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_ip_def Let_def using True by simp
next
  case False
  show ?thesis unfolding make_side_rhs_tree_ip_def Let_def using False by simp
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
proof (unfold mono_sides_def, intro allI impI)
  fix w :: pp and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assume le: "sigma1 \<le> sigma2"
  show "sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 w) sigma1
        \<le> sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 w) sigma2"
  proof (rule le_funI)
    fix x :: "pp + unit"
    show "sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 w) sigma1 x
          \<le> sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 w) sigma2 x"
    proof (cases x)
      case (Inl b)
      thus ?thesis
        unfolding side_cfg_T_ip_def by (simp add: sides_make_side_rhs_tree_ip_Inl)
    next
      case (Inr b)
      have e1: "sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 w) sigma1 x
                = side_glob_ip tf (\<squnion>) sigma1
                    (predecessor_list g w) (combine_predecessor_list g w)
                  \<squnion> (if w = cfg_entry g then restrict_global s0 else bot)"
        unfolding side_cfg_T_ip_def Inr by (simp add: sides_make_side_rhs_tree_ip_Inr)
      have e2: "sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 w) sigma2 x
                = side_glob_ip tf (\<squnion>) sigma2
                    (predecessor_list g w) (combine_predecessor_list g w)
                  \<squnion> (if w = cfg_entry g then restrict_global s0 else bot)"
        unfolding side_cfg_T_ip_def Inr by (simp add: sides_make_side_rhs_tree_ip_Inr)
      show ?thesis unfolding e1 e2
        by (rule sup_mono[OF side_glob_ip_mono_sup[OF tf_mono le] order_refl])
    qed
  qed
qed

lemma side_cfg_T_ip_mono_deps:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state"
  shows "mono_deps (side_cfg_T_ip g tf (\<squnion>) bot0 s0)"
  unfolding mono_deps_def side_cfg_T_ip_def dep_def
  apply clarify
  apply (simp only: dep_aux_make_side_rhs_tree_ip)
  apply (subst (asm) dep_aux_side_rhs_fold_ip_indep)
  by simp

(* -- Post-solution in usable form ------------------------------------- *)

(* A post-solution of side_cfg_T_ip bounds, at every program point in scope,
   the local fold by the local unknown and the global contribution by the
   single global unknown. *)
lemma side_post_solution_le_local_ip:
  assumes "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0) x sigma vars"
      and "v \<in> vars"
  shows "side_acc_ip tf (\<squnion>)
           (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
           sigma (predecessor_list g v) (combine_predecessor_list g v) \<le> sigma (Inl v)"
proof -
  from assms have "eq (side_cfg_T_ip g tf (\<squnion>) bot0 s0) v sigma \<le> sigma (Inl v)" by auto
  thus ?thesis by (simp add: eq_side_cfg_T_ip)
qed

lemma side_post_solution_le_global_ip:
  assumes "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0) x sigma vars"
      and "v \<in> vars"
  shows "side_glob_ip tf (\<squnion>) sigma (predecessor_list g v) (combine_predecessor_list g v)
         \<le> sigma (Inr ())"
proof -
  from assms have "sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 v) sigma \<le> sigma" by auto
  hence le: "sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 v) sigma (Inr ()) \<le> sigma (Inr ())"
    by (simp add: le_fun_def)
  have "side_glob_ip tf (\<squnion>) sigma (predecessor_list g v) (combine_predecessor_list g v)
        \<le> sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 v) sigma (Inr ())"
    unfolding side_cfg_T_ip_def
    by (simp add: sides_make_side_rhs_tree_ip_Inr)
  thus ?thesis using le by (rule order_trans)
qed

(* -- Fold upper bounds (join = sup) ----------------------------------- *)

lemma side_acc_ip_ge_acc:
  "acc \<le> side_acc_ip tf (\<squnion>) acc sigma es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc)
    case Nil show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have "acc \<le> side_acc_ip tf (\<squnion>)
            (acc \<squnion> restrict_local (sigma (Inl cc) \<squnion> sigma (Inr ()))) sigma [] cs"
      by (meson Cons.IH sup_ge1 order_trans)
    then show ?case unfolding x by (simp only: side_acc_ip.simps)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have "acc \<le> side_acc_ip tf (\<squnion>)
          (acc \<squnion> restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))) sigma es cs"
    by (meson Cons.IH sup_ge1 order_trans)
  then show ?case unfolding x by (simp only: side_acc_ip.simps)
qed

(* The local fold grows monotonically as more incoming edges are processed. *)
lemma side_acc_ip_es_mono:
  "side_acc_ip tf (\<squnion>) acc sigma [] cs \<le> side_acc_ip tf (\<squnion>) acc sigma es cs"
proof (induction es arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have "side_acc_ip tf (\<squnion>) acc sigma [] cs
        \<le> side_acc_ip tf (\<squnion>)
            (acc \<squnion> restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))) sigma [] cs"
    by (rule side_acc_ip_mono_acc[OF sup_mono sup_ge1])
  also have "... \<le> side_acc_ip tf (\<squnion>)
            (acc \<squnion> restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))) sigma es cs"
    by (rule Cons.IH)
  finally show ?case unfolding x by (simp only: side_acc_ip.simps)
qed

(* Each incoming edge's local contribution is below the local fold. *)
lemma restrict_local_le_side_acc_ip_edge:
  "(u, a) \<in> set es \<Longrightarrow>
   restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
     \<le> side_acc_ip tf (\<squnion>) acc sigma es cs"
proof (induction es arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x es)
  obtain w b where x: "x = (w, b)" by (cases x)
  from Cons.prems x consider (hd) "(u, a) = (w, b)" | (tl) "(u, a) \<in> set es" by auto
  then show ?case
  proof cases
    case hd
    then have uw: "u = w" and ab: "a = b" by auto
    have "restrict_local (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))
          \<le> side_acc_ip tf (\<squnion>)
               (acc \<squnion> restrict_local (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ()))))
               sigma es cs"
      using side_acc_ip_ge_acc sup_ge2 order_trans by blast
    thus ?thesis unfolding x uw ab by (simp only: side_acc_ip.simps)
  next
    case tl
    have "restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
          \<le> side_acc_ip tf (\<squnion>)
               (acc \<squnion> restrict_local (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ()))))
               sigma es cs"
      by (rule Cons.IH[OF tl])
    thus ?thesis unfolding x by (simp only: side_acc_ip.simps)
  qed
qed

(* Each incoming combine's local contribution (caller locals) is below the
   local fold (edge list exhausted). *)
lemma restrict_local_le_side_acc_ip_combine_nil:
  "(cc, ex) \<in> set cs \<Longrightarrow>
   restrict_local (sigma (Inl cc) \<squnion> sigma (Inr ()))
     \<le> side_acc_ip tf (\<squnion>) acc sigma [] cs"
proof (induction cs arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x cs)
  obtain c2 e2 where x: "x = (c2, e2)" by (cases x)
  from Cons.prems x consider (hd) "(cc, ex) = (c2, e2)" | (tl) "(cc, ex) \<in> set cs" by auto
  then show ?case
  proof cases
    case hd
    then have cc2: "cc = c2" and exe2: "ex = e2" by auto
    have "restrict_local (sigma (Inl c2) \<squnion> sigma (Inr ()))
          \<le> side_acc_ip tf (\<squnion>)
               (acc \<squnion> restrict_local (sigma (Inl c2) \<squnion> sigma (Inr ()))) sigma [] cs"
      using side_acc_ip_ge_acc sup_ge2 order_trans by blast
    thus ?thesis unfolding x cc2 exe2 by (simp only: side_acc_ip.simps)
  next
    case tl
    have "restrict_local (sigma (Inl cc) \<squnion> sigma (Inr ()))
          \<le> side_acc_ip tf (\<squnion>)
               (acc \<squnion> restrict_local (sigma (Inl c2) \<squnion> sigma (Inr ()))) sigma [] cs"
      by (rule Cons.IH[OF tl])
    thus ?thesis unfolding x by (simp only: side_acc_ip.simps)
  qed
qed

lemma restrict_local_le_side_acc_ip_combine:
  assumes "(cc, ex) \<in> set cs"
  shows "restrict_local (sigma (Inl cc) \<squnion> sigma (Inr ()))
         \<le> side_acc_ip tf (\<squnion>) acc sigma es cs"
  using restrict_local_le_side_acc_ip_combine_nil[OF assms] side_acc_ip_es_mono
  by (rule order_trans)

(* Global fold analogues. *)
lemma side_glob_ip_es_mono:
  "side_glob_ip tf (\<squnion>) sigma [] cs \<le> side_glob_ip tf (\<squnion>) sigma es cs"
proof (induction es)
  case Nil show ?case by simp
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have "side_glob_ip tf (\<squnion>) sigma [] cs \<le> side_glob_ip tf (\<squnion>) sigma es cs"
    by (rule Cons.IH)
  also have "... \<le> side_glob_ip tf (\<squnion>) sigma es cs
                     \<squnion> restrict_global (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))"
    by (rule sup_ge1)
  finally show ?case unfolding x by (simp only: side_glob_ip.simps)
qed

lemma restrict_global_le_side_glob_ip_edge:
  "(u, a) \<in> set es \<Longrightarrow>
   restrict_global (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
     \<le> side_glob_ip tf (\<squnion>) sigma es cs"
proof (induction es)
  case Nil thus ?case by simp
next
  case (Cons x es)
  obtain w b where x: "x = (w, b)" by (cases x)
  from Cons.prems x consider (hd) "(u, a) = (w, b)" | (tl) "(u, a) \<in> set es" by auto
  then show ?case
  proof cases
    case hd
    then have uw: "u = w" and ab: "a = b" by auto
    have "restrict_global (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))
          \<le> side_glob_ip tf (\<squnion>) sigma es cs
               \<squnion> restrict_global (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))"
      by (rule sup_ge2)
    thus ?thesis unfolding x uw ab by (simp only: side_glob_ip.simps)
  next
    case tl
    have "restrict_global (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
          \<le> side_glob_ip tf (\<squnion>) sigma es cs
               \<squnion> restrict_global (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))"
      using Cons.IH[OF tl] by (rule le_supI1)
    thus ?thesis unfolding x by (simp only: side_glob_ip.simps)
  qed
qed

lemma restrict_global_le_side_glob_ip_combine_nil:
  "(cc, ex) \<in> set cs \<Longrightarrow>
   restrict_global (sigma (Inl ex) \<squnion> sigma (Inr ()))
     \<le> side_glob_ip tf (\<squnion>) sigma [] cs"
proof (induction cs)
  case Nil thus ?case by simp
next
  case (Cons x cs)
  obtain c2 e2 where x: "x = (c2, e2)" by (cases x)
  from Cons.prems x consider (hd) "(cc, ex) = (c2, e2)" | (tl) "(cc, ex) \<in> set cs" by auto
  then show ?case
  proof cases
    case hd
    then have exe2: "ex = e2" by auto
    have "restrict_global (sigma (Inl e2) \<squnion> sigma (Inr ()))
          \<le> side_glob_ip tf (\<squnion>) sigma [] cs
               \<squnion> restrict_global (sigma (Inl e2) \<squnion> sigma (Inr ()))"
      by (rule sup_ge2)
    thus ?thesis unfolding x exe2 by (simp only: side_glob_ip.simps)
  next
    case tl
    have "restrict_global (sigma (Inl ex) \<squnion> sigma (Inr ()))
          \<le> side_glob_ip tf (\<squnion>) sigma [] cs
               \<squnion> restrict_global (sigma (Inl e2) \<squnion> sigma (Inr ()))"
      using Cons.IH[OF tl] by (rule le_supI1)
    thus ?thesis unfolding x by (simp only: side_glob_ip.simps)
  qed
qed

lemma restrict_global_le_side_glob_ip_combine:
  assumes "(cc, ex) \<in> set cs"
  shows "restrict_global (sigma (Inl ex) \<squnion> sigma (Inr ()))
         \<le> side_glob_ip tf (\<squnion>) sigma es cs"
  using restrict_global_le_side_glob_ip_combine_nil[OF assms] side_glob_ip_es_mono
  by (rule order_trans)

(* -- Edge / combine closure of a side post-solution ------------------- *)

(* For any CFG edge (u, a, v), a post-solution's combined env at u, transferred
   along a, is below the combined env at v. *)
lemma apply_tf_combined_le_ip:
  assumes pp:  "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0) x sigma vars"
      and v:   "v \<in> vars"
      and e:   "(u, a, v) \<in> edges g"
      and fin: "finite (edges g)"
  shows "apply_tf tf a (side_env sigma u) \<le> side_env sigma v"
proof -
  have mem: "(u, a) \<in> set (predecessor_list g v)"
    using e by (simp add: set_predecessor_list[OF fin] predecessors_def)
  have loc: "restrict_local (apply_tf tf a (side_env sigma u)) \<le> sigma (Inl v)"
    using restrict_local_le_side_acc_ip_edge[OF mem] side_post_solution_le_local_ip[OF pp v]
    unfolding side_env_def by (rule order_trans)
  have glob: "restrict_global (apply_tf tf a (side_env sigma u)) \<le> sigma (Inr ())"
    using restrict_global_le_side_glob_ip_edge[OF mem] side_post_solution_le_global_ip[OF pp v]
    unfolding side_env_def by (rule order_trans)
  have "apply_tf tf a (side_env sigma u)
        = restrict_local (apply_tf tf a (side_env sigma u))
          \<squnion> restrict_global (apply_tf tf a (side_env sigma u))"
    by (rule restrict_local_global_join[symmetric])
  also have "... \<le> sigma (Inl v) \<squnion> sigma (Inr ())"
    using loc glob by (rule sup_mono)
  finally show ?thesis unfolding side_env_def .
qed

(* For any combine triple (c, ex, v), the abstract combine of the post-solution's
   combined envs at the caller c and the callee exit ex is below the combined env
   at the return point v. *)
lemma combine_combined_le_ip:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state" and sigma :: "pp + unit \<Rightarrow> 'a abs_state"
    and c ex v :: pp
  assumes pp:   "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0) x sigma vars"
      and v:    "v \<in> vars"
      and e:    "(c, ex, v) \<in> combines g"
      and finC: "finite (combines g)"
  shows "combine_abs (side_env sigma c) (side_env sigma ex) \<le> side_env sigma v"
proof -
  have mem: "(c, ex) \<in> set (combine_predecessor_list g v)"
    using e by (simp add: set_combine_predecessor_list[OF finC] combine_predecessors_def)
  have loc: "restrict_local (side_env sigma c) \<le> sigma (Inl v)"
    using restrict_local_le_side_acc_ip_combine[OF mem] side_post_solution_le_local_ip[OF pp v]
    unfolding side_env_def by (rule order_trans)
  have glob: "restrict_global (side_env sigma ex) \<le> sigma (Inr ())"
    using restrict_global_le_side_glob_ip_combine[OF mem] side_post_solution_le_global_ip[OF pp v]
    unfolding side_env_def by (rule order_trans)
  have "combine_abs (side_env sigma c) (side_env sigma ex)
        = restrict_local (side_env sigma c) \<squnion> restrict_global (side_env sigma ex)"
    by (simp add: combine_abs_def restrict_combine)
  also have "... \<le> sigma (Inl v) \<squnion> sigma (Inr ())"
    using loc glob by (rule sup_mono)
  finally show ?thesis unfolding side_env_def .
qed

(* -- Dependency membership (edges and combine endpoints) -------------- *)

lemma Inl_dep_aux_side_rhs_fold_ip_edge:
  assumes "(u, a) \<in> set es"
  shows "Inl u \<in> dep_aux sigma (side_rhs_fold_ip tf join acc es cs)"
  using assms
proof (induction es arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x es)
  obtain w b where x: "x = (w, b)" by (cases x)
  show ?case
  proof (cases "x = (u, a)")
    case True
    thus ?thesis unfolding True side_rhs_fold_ip.simps dep_aux.simps Let_def by simp
  next
    case False
    have mem: "(u, a) \<in> set es" using Cons.prems x False by auto
    show ?thesis unfolding x side_rhs_fold_ip.simps dep_aux.simps Let_def
      using Cons.IH[OF mem] by simp
  qed
qed

(* The dependencies reachable after the edge list is exhausted (the combine
   queries) survive the edge prefix. *)
lemma dep_aux_side_rhs_fold_ip_nil_sub_es:
  "dep_aux sigma (side_rhs_fold_ip tf join acc [] cs)
   \<subseteq> dep_aux sigma (side_rhs_fold_ip tf join acc es cs)"
proof (induction es arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x es)
  obtain w b where x: "x = (w, b)" by (cases x)
  let ?acc' = "join acc (restrict_local (apply_tf tf b (join (sigma (Inl w)) (sigma (Inr ())))))"
  have "dep_aux sigma (side_rhs_fold_ip tf join acc [] cs)
        = dep_aux sigma (side_rhs_fold_ip tf join ?acc' [] cs)"
    by (rule dep_aux_side_rhs_fold_ip_acc_indep)
  also have "... \<subseteq> dep_aux sigma (side_rhs_fold_ip tf join ?acc' es cs)"
    by (rule Cons.IH)
  also have "... \<subseteq> dep_aux sigma (side_rhs_fold_ip tf join acc (x # es) cs)"
    unfolding x side_rhs_fold_ip.simps dep_aux.simps Let_def by auto
  finally show ?case .
qed

lemma Inl_dep_aux_side_rhs_fold_ip_call:
  fixes c ex :: pp
  assumes "(c, ex) \<in> set cs"
  shows "Inl c \<in> dep_aux sigma (side_rhs_fold_ip tf join acc es cs)"
proof -
  have "Inl c \<in> dep_aux sigma (side_rhs_fold_ip tf join acc [] cs)"
    using assms
  proof (induction cs arbitrary: acc)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain c2 e2 where x: "x = (c2, e2)" by (cases x)
    show ?case
    proof (cases "x = (c, ex)")
      case True
      thus ?thesis unfolding True side_rhs_fold_ip.simps dep_aux.simps Let_def by simp
    next
      case False
      have mem: "(c, ex) \<in> set cs" using Cons.prems x False by auto
      show ?thesis unfolding x side_rhs_fold_ip.simps dep_aux.simps Let_def
        using Cons.IH[OF mem] by simp
    qed
  qed
  thus ?thesis using dep_aux_side_rhs_fold_ip_nil_sub_es by blast
qed

lemma Inl_dep_aux_side_rhs_fold_ip_exit:
  fixes c ex :: pp
  assumes "(c, ex) \<in> set cs"
  shows "Inl ex \<in> dep_aux sigma (side_rhs_fold_ip tf join acc es cs)"
proof -
  have "Inl ex \<in> dep_aux sigma (side_rhs_fold_ip tf join acc [] cs)"
    using assms
  proof (induction cs arbitrary: acc)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain c2 e2 where x: "x = (c2, e2)" by (cases x)
    show ?case
    proof (cases "x = (c, ex)")
      case True
      thus ?thesis unfolding True side_rhs_fold_ip.simps dep_aux.simps Let_def by simp
    next
      case False
      have mem: "(c, ex) \<in> set cs" using Cons.prems x False by auto
      show ?thesis unfolding x side_rhs_fold_ip.simps dep_aux.simps Let_def
        using Cons.IH[OF mem] by simp
    qed
  qed
  thus ?thesis using dep_aux_side_rhs_fold_ip_nil_sub_es by blast
qed

(* -- Dependency at the eqsT level (edges and combine endpoints) ------- *)

lemma dep_side_rhs_tree_ip_edge:
  assumes fin: "finite (edges g)"
  assumes ed: "(u, a, w) \<in> edges g"
  shows "u \<in> dep\<^sub>L (side_cfg_T_ip g tf join bot0 s0) sigma w"
proof -
  have mem: "(u, a) \<in> set (predecessor_list g w)"
    using ed fin by (auto simp: predecessors_def set_predecessor_list)
  have "Inl u \<in> dep_aux sigma (make_side_rhs_tree_ip g tf join bot0 s0 w)"
    unfolding dep_aux_make_side_rhs_tree_ip
    by (rule Inl_dep_aux_side_rhs_fold_ip_edge[OF mem])
  thus ?thesis unfolding side_cfg_T_ip_def dep\<^sub>L_def dep_def by simp
qed

lemma dep_side_rhs_tree_ip_combine:
  fixes g :: cfg and c ex w :: pp
  assumes finC: "finite (combines g)"
  assumes ce: "(c, ex, w) \<in> combines g"
  shows "c \<in> dep\<^sub>L (side_cfg_T_ip g tf join bot0 s0) sigma w
       \<and> ex \<in> dep\<^sub>L (side_cfg_T_ip g tf join bot0 s0) sigma w"
proof -
  have mem: "(c, ex) \<in> set (combine_predecessor_list g w)"
    using ce finC by (simp add: combine_predecessors_def)
  have dc: "Inl c \<in> dep_aux sigma (make_side_rhs_tree_ip g tf join bot0 s0 w)"
    unfolding dep_aux_make_side_rhs_tree_ip
    by (rule Inl_dep_aux_side_rhs_fold_ip_call[OF mem])
  have de: "Inl ex \<in> dep_aux sigma (make_side_rhs_tree_ip g tf join bot0 s0 w)"
    unfolding dep_aux_make_side_rhs_tree_ip
    by (rule Inl_dep_aux_side_rhs_fold_ip_exit[OF mem])
  show ?thesis using dc de unfolding side_cfg_T_ip_def dep\<^sub>L_def dep_def by simp
qed

(* -- Entry coverage from an arbitrary initial state ------------------- *)

(* The entry node's wrapping Side () contributes restrict_global s0 to the
   single global unknown, so the initial globals are below it in any
   post-solution. *)
lemma restrict_global_s0_le_global_ip:
  assumes pp: "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0) x sigma vars"
      and entry_in: "cfg_entry g \<in> vars"
  shows "restrict_global s0 \<le> sigma (Inr ())"
proof -
  from pp entry_in have "sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 (cfg_entry g)) sigma \<le> sigma"
    by auto
  hence le: "sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 (cfg_entry g)) sigma (Inr ())
             \<le> sigma (Inr ())"
    by (simp add: le_fun_def)
  have "restrict_global s0
        \<le> side_glob_ip tf (\<squnion>) sigma
             (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))
           \<squnion> restrict_global s0"
    by (rule sup_ge2)
  also have "... = sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 (cfg_entry g)) sigma (Inr ())"
    unfolding side_cfg_T_ip_def by (simp add: sides_make_side_rhs_tree_ip_Inr)
  also have "... \<le> sigma (Inr ())" by (rule le)
  finally show ?thesis .
qed

(* At the entry point the local fold seeds restrict_local s0 and the wrapping
   Side () seeds restrict_global s0, so s0 itself is below the combined env at
   the entry -- for an arbitrary initial state, no globals-free hypothesis. *)
lemma s0_le_side_env_entry_ip:
  assumes pp: "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot s0) v0 sigma vars"
  assumes entry_in: "cfg_entry g \<in> vars"
  shows "s0 \<le> side_env sigma (cfg_entry g)"
proof -
  have acc_le: "side_acc_ip tf (\<squnion>) (bot \<squnion> restrict_local s0) sigma
                  (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))
                \<le> sigma (Inl (cfg_entry g))"
    using side_post_solution_le_local_ip[OF pp entry_in] by simp
  have "restrict_local s0 \<le> bot \<squnion> restrict_local s0" by simp
  also have "... \<le> side_acc_ip tf (\<squnion>) (bot \<squnion> restrict_local s0) sigma
                     (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))"
    by (rule side_acc_ip_ge_acc)
  also have "... \<le> sigma (Inl (cfg_entry g))" by (rule acc_le)
  finally have rl: "restrict_local s0 \<le> sigma (Inl (cfg_entry g))" .
  have rg: "restrict_global s0 \<le> sigma (Inr ())"
    by (rule restrict_global_s0_le_global_ip[OF pp entry_in])
  have "s0 = restrict_local s0 \<squnion> restrict_global s0"
    by (rule restrict_local_global_join[symmetric])
  also have "... \<le> sigma (Inl (cfg_entry g)) \<squnion> sigma (Inr ())"
    using rl rg by (rule sup_mono)
  finally show ?thesis unfolding side_env_def .
qed

end
