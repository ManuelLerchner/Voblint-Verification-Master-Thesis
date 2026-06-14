theory TD_Side_IP_Mono
  imports TD_Side_IP_Tree
begin

section \<open>Side IP solver: monotonicity and solver preconditions\<close>

text \<open>
  Monotonicity of the side IP strategy and the TD_side solver preconditions.

  Proves the local/global folds are monotone, that dependencies are stable
  (independent of acc and sigma), and packages these as the three TD_side
  hypotheses on side_cfg_T_ip: side_cfg_T_ip_is_mono_eq, _mono_sides,
  _mono_deps.  Construction: TD_Side_IP_Tree.  Bounds: TD_Side_IP_Bounds.
\<close>

subsection \<open>Monotonicity of the local fold\<close>

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

subsection \<open>Monotonicity of the global contribution\<close>

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

subsection \<open>Dependencies are independent of acc and of sigma\<close>

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

subsection \<open>Side contributions: all land in the global slot Inr ()\<close>

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

subsection \<open>Solver preconditions for TD_side\<close>

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

end
