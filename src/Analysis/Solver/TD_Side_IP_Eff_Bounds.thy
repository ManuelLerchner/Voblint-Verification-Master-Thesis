theory TD_Side_IP_Eff_Bounds
  imports TD_Side_IP_Mono
begin

section \<open>Effectful side IP solver: general monotonicity (no shim)\<close>

text \<open>
  Monotonicity of the effectful equation system for an *arbitrary* etf, from a
  per-tree contract (each edge / combine tree is monotone in the environment).
  This replaces the pure-shim discharge (td_cfg_side_ip_solver_eff_from_tf, which
  routes through the bridge to the pure mono lemmas): a genuinely effectful etf
  supplies the per-tree monotonicity directly -- e.g. via seqcomp_mono on its
  QueryL/QueryG/Side construction.

  The per-tree contract is stated on traverse_rhs of the trees the fold composes
  (apply_etf etf a u for edges, etf_combine etf c ex for combine endpoints).
\<close>

subsection \<open>Monotonicity of the effectful local fold\<close>

lemma side_acc_ip_eff_mono_acc:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  shows "acc1 \<le> acc2 \<Longrightarrow>
         side_acc_ip_eff etf acc1 \<sigma> es cs \<le> side_acc_ip_eff etf acc2 \<sigma> es cs"
proof (induction es arbitrary: acc1 acc2 cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc1 acc2)
    case Nil then show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    show ?case unfolding x
      using Cons.IH[OF sup_mono[OF Cons.prems order_refl]] by (simp add: sup_fun_def)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x
    using Cons.IH[OF sup_mono[OF Cons.prems order_refl]] by (simp add: sup_fun_def)
qed

lemma side_acc_ip_eff_mono:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes edge_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (apply_etf etf a u) s1 \<le> traverse_rhs (apply_etf etf a u) s2"
  assumes comb_mono:
    "\<And>cc ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (etf_combine etf cc ex) s1 \<le> traverse_rhs (etf_combine etf cc ex) s2"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_acc_ip_eff etf acc sigma1 es cs \<le> side_acc_ip_eff etf acc sigma2 es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc)
    case Nil show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have c_le: "traverse_rhs (etf_combine etf cc ex) sigma1
                  \<le> traverse_rhs (etf_combine etf cc ex) sigma2"
      by (rule comb_mono[OF sigma_le])
    have step1:
      "side_acc_ip_eff etf (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma1) sigma1 [] cs
       \<le> side_acc_ip_eff etf (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma1) sigma2 [] cs"
      by (rule Cons.IH)
    have step2:
      "side_acc_ip_eff etf (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma1) sigma2 [] cs
       \<le> side_acc_ip_eff etf (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma2) sigma2 [] cs"
      by (rule side_acc_ip_eff_mono_acc[OF sup_mono[OF order_refl c_le]])
    show ?case unfolding x using order_trans[OF step1 step2] by simp
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have c_le: "traverse_rhs (apply_etf etf a u) sigma1
                \<le> traverse_rhs (apply_etf etf a u) sigma2"
    by (rule edge_mono[OF sigma_le])
  have step1:
    "side_acc_ip_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) sigma1 es cs
     \<le> side_acc_ip_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) sigma2 es cs"
    by (rule Cons.IH)
  have step2:
    "side_acc_ip_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) sigma2 es cs
     \<le> side_acc_ip_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma2) sigma2 es cs"
    by (rule side_acc_ip_eff_mono_acc[OF sup_mono[OF order_refl c_le]])
  show ?case unfolding x using order_trans[OF step1 step2] by simp
qed

subsection \<open>is_mono_eq for an arbitrary etf\<close>

lemma side_cfg_T_ip_eff_is_mono_eq_gen:
  fixes g :: cfg
    and etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state"
  assumes edge_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (apply_etf etf a u) s1 \<le> traverse_rhs (apply_etf etf a u) s2"
  assumes comb_mono:
    "\<And>cc ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (etf_combine etf cc ex) s1 \<le> traverse_rhs (etf_combine etf cc ex) s2"
  shows "is_mono_eq (side_cfg_T_ip_eff g etf bot0 s0)"
  unfolding is_mono_eq_def
proof (intro allI impI)
  fix x :: pp and \<sigma>1 \<sigma>2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assume le: "\<sigma>1 \<le> \<sigma>2"
  show "eq (side_cfg_T_ip_eff g etf bot0 s0) x \<sigma>1
        \<le> eq (side_cfg_T_ip_eff g etf bot0 s0) x \<sigma>2"
    unfolding eq_side_cfg_T_ip_eff
    by (rule side_acc_ip_eff_mono[OF edge_mono comb_mono le])
qed

subsection \<open>Side contributions: independent of acc, monotone in the environment\<close>

text \<open>
  The fold's Side contributions are carried only by the per-tree Side nodes; the
  accumulator flows into the final Answer (sides = bot), so the side map is
  independent of acc.
\<close>
lemma sides_side_rhs_fold_ip_eff_acc_indep:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  shows "sides_of_rhs (side_rhs_fold_ip_eff etf acc1 es cs) \<sigma>
         = sides_of_rhs (side_rhs_fold_ip_eff etf acc2 es cs) \<sigma>"
proof (induction es arbitrary: acc1 acc2 cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc1 acc2)
    case Nil show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have step: "sides_of_rhs (side_rhs_fold_ip_eff etf
                  (acc1 \<squnion> traverse_rhs (etf_combine etf cc ex) \<sigma>) [] cs) \<sigma>
              = sides_of_rhs (side_rhs_fold_ip_eff etf
                  (acc2 \<squnion> traverse_rhs (etf_combine etf cc ex) \<sigma>) [] cs) \<sigma>"
      by (rule Cons.IH)
    show ?case unfolding x side_rhs_fold_ip_eff.simps
      using step by (simp add: sides_of_rhs_seqcomp)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have step: "sides_of_rhs (side_rhs_fold_ip_eff etf
                (acc1 \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) es cs) \<sigma>
            = sides_of_rhs (side_rhs_fold_ip_eff etf
                (acc2 \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) es cs) \<sigma>"
    by (rule Cons.IH)
  show ?case unfolding x side_rhs_fold_ip_eff.simps
    using step by (simp add: sides_of_rhs_seqcomp)
qed

lemma sides_side_rhs_fold_ip_eff_mono:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes edge_sides_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (apply_etf etf a u) s1 \<le> sides_of_rhs (apply_etf etf a u) s2"
  assumes comb_sides_mono:
    "\<And>cc ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (etf_combine etf cc ex) s1 \<le> sides_of_rhs (etf_combine etf cc ex) s2"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "sides_of_rhs (side_rhs_fold_ip_eff etf acc es cs) sigma1
         \<le> sides_of_rhs (side_rhs_fold_ip_eff etf acc es cs) sigma2"
proof (induction es arbitrary: acc cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc)
    case Nil show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have g_le: "sides_of_rhs (etf_combine etf cc ex) sigma1
                  \<le> sides_of_rhs (etf_combine etf cc ex) sigma2"
      by (rule comb_sides_mono[OF sigma_le])
    have ih: "sides_of_rhs (side_rhs_fold_ip_eff etf
                (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma1) [] cs) sigma1
            \<le> sides_of_rhs (side_rhs_fold_ip_eff etf
                (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma1) [] cs) sigma2"
      by (rule Cons.IH)
    have rest_le: "sides_of_rhs (side_rhs_fold_ip_eff etf
                     (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma1) [] cs) sigma1
                 \<le> sides_of_rhs (side_rhs_fold_ip_eff etf
                     (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma2) [] cs) sigma2"
      using ih sides_side_rhs_fold_ip_eff_acc_indep by metis
    show ?case unfolding x side_rhs_fold_ip_eff.simps
      by (simp only: sides_of_rhs_seqcomp) (rule sup_mono[OF g_le rest_le])
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have g_le: "sides_of_rhs (apply_etf etf a u) sigma1
                \<le> sides_of_rhs (apply_etf etf a u) sigma2"
    by (rule edge_sides_mono[OF sigma_le])
  have ih: "sides_of_rhs (side_rhs_fold_ip_eff etf
              (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) es cs) sigma1
          \<le> sides_of_rhs (side_rhs_fold_ip_eff etf
              (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) es cs) sigma2"
    by (rule Cons.IH)
  have rest_le: "sides_of_rhs (side_rhs_fold_ip_eff etf
                   (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) es cs) sigma1
               \<le> sides_of_rhs (side_rhs_fold_ip_eff etf
                   (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma2) es cs) sigma2"
    using ih sides_side_rhs_fold_ip_eff_acc_indep by metis
  show ?case unfolding x side_rhs_fold_ip_eff.simps
    by (simp only: sides_of_rhs_seqcomp) (rule sup_mono[OF g_le rest_le])
qed

subsection \<open>mono_sides for an arbitrary etf\<close>

lemma fun_upd_sup_mono:
  fixes m1 m2 :: "'b \<Rightarrow> 'a::bounded_semilattice_sup_bot"
  assumes "m1 \<le> m2"
  shows "m1(y := m1 y \<squnion> cd) \<le> m2(y := m2 y \<squnion> cd)"
proof -
  have eq: "\<And>m::'b \<Rightarrow> 'a. m(y := m y \<squnion> cd) = m \<squnion> ((\<lambda>_. bot)(y := cd))"
    by (rule ext) (simp add: fun_upd_def sup_fun_def)
  show ?thesis unfolding eq by (rule sup_mono[OF assms order_refl])
qed

lemma side_cfg_T_ip_eff_mono_sides_gen:
  fixes g :: cfg
    and etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state"
  assumes edge_sides_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (apply_etf etf a u) s1 \<le> sides_of_rhs (apply_etf etf a u) s2"
  assumes comb_sides_mono:
    "\<And>cc ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (etf_combine etf cc ex) s1 \<le> sides_of_rhs (etf_combine etf cc ex) s2"
  shows "mono_sides (side_cfg_T_ip_eff g etf bot0 s0)"
proof (unfold mono_sides_def, intro allI impI)
  fix w :: pp and \<sigma>1 \<sigma>2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assume le: "\<sigma>1 \<le> \<sigma>2"
  have fold_le: "\<And>acc. sides_of_rhs (side_rhs_fold_ip_eff etf acc
                   (predecessor_list g w) (combine_predecessor_list g w)) \<sigma>1
                 \<le> sides_of_rhs (side_rhs_fold_ip_eff etf acc
                   (predecessor_list g w) (combine_predecessor_list g w)) \<sigma>2"
    by (rule sides_side_rhs_fold_ip_eff_mono[OF edge_sides_mono comb_sides_mono le])
  show "sides_of_rhs (side_cfg_T_ip_eff g etf bot0 s0 w) \<sigma>1
        \<le> sides_of_rhs (side_cfg_T_ip_eff g etf bot0 s0 w) \<sigma>2"
  proof (cases "w = cfg_entry g")
    case False
    show ?thesis
      unfolding side_cfg_T_ip_eff_def make_side_rhs_tree_ip_eff_def Let_def
      using False fold_le[of bot0] by simp
  next
    case True
    have m_le: "sides_of_rhs (side_rhs_fold_ip_eff etf (bot0 \<squnion> restrict_local s0)
                  (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))) \<sigma>1
              \<le> sides_of_rhs (side_rhs_fold_ip_eff etf (bot0 \<squnion> restrict_local s0)
                  (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))) \<sigma>2"
      using fold_le[of "bot0 \<squnion> restrict_local s0"] True by simp
    show ?thesis
      unfolding side_cfg_T_ip_eff_def make_side_rhs_tree_ip_eff_def
      using True by (simp add: Let_def fun_upd_sup_mono[OF m_le])
  qed
qed

subsection \<open>mono_deps for an arbitrary etf (static per-tree dependencies)\<close>

text \<open>
  The fold's queried-unknown set is independent of the environment when each
  per-tree query skeleton is static (static_deps).  Via dep_aux_seqcomp the fold's
  deps are the union of the per-tree deps and the continuation's deps; the
  accumulator only affects the final Answer, so deps are also acc-independent.
\<close>
lemma dep_aux_side_rhs_fold_ip_eff_indep:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  shows "dep_aux \<sigma>1 (side_rhs_fold_ip_eff etf acc1 es cs)
       = dep_aux \<sigma>2 (side_rhs_fold_ip_eff etf acc2 es cs)"
proof (induction es arbitrary: acc1 acc2 cs \<sigma>1 \<sigma>2)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc1 acc2 \<sigma>1 \<sigma>2)
    case Nil show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have e: "dep_aux \<sigma>1 (etf_combine etf cc ex) = dep_aux \<sigma>2 (etf_combine etf cc ex)"
      using comb_static unfolding static_deps_def by blast
    have ih: "dep_aux \<sigma>1 (side_rhs_fold_ip_eff etf
                (acc1 \<squnion> traverse_rhs (etf_combine etf cc ex) \<sigma>1) [] cs)
            = dep_aux \<sigma>2 (side_rhs_fold_ip_eff etf
                (acc2 \<squnion> traverse_rhs (etf_combine etf cc ex) \<sigma>2) [] cs)"
      by (rule Cons.IH)
    show ?case unfolding x side_rhs_fold_ip_eff.simps
      by (simp add: dep_aux_seqcomp e ih)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have e: "dep_aux \<sigma>1 (apply_etf etf a u) = dep_aux \<sigma>2 (apply_etf etf a u)"
    using edge_static unfolding static_deps_def by blast
  have ih: "dep_aux \<sigma>1 (side_rhs_fold_ip_eff etf
              (acc1 \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>1) es cs)
          = dep_aux \<sigma>2 (side_rhs_fold_ip_eff etf
              (acc2 \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>2) es cs)"
    by (rule Cons.IH)
  show ?case unfolding x side_rhs_fold_ip_eff.simps
    by (simp add: dep_aux_seqcomp e ih)
qed

lemma dep_aux_make_side_rhs_tree_ip_eff:
  "dep_aux \<sigma> (make_side_rhs_tree_ip_eff g etf bot0 s0 v)
   = dep_aux \<sigma> (side_rhs_fold_ip_eff etf
        (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
        (predecessor_list g v) (combine_predecessor_list g v))"
  by (cases "v = cfg_entry g")
     (simp_all add: make_side_rhs_tree_ip_eff_def Let_def)

lemma side_cfg_T_ip_eff_mono_deps_gen:
  fixes g :: cfg
    and etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  shows "mono_deps (side_cfg_T_ip_eff g etf bot0 s0)"
  unfolding mono_deps_def side_cfg_T_ip_eff_def dep_def
  apply clarify
  apply (simp only: dep_aux_make_side_rhs_tree_ip_eff)
  apply (subst (asm) dep_aux_side_rhs_fold_ip_eff_indep[OF edge_static comb_static])
  apply assumption
  done

end
