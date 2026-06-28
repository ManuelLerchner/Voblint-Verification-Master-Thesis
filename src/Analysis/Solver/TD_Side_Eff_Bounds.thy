theory TD_Side_Eff_Bounds
  imports TD_Side_Tree
begin

section \<open>Effectful side IP solver: general monotonicity\<close>

text \<open>
  Monotonicity of the effectful equation system for an arbitrary etf follows
  from a per-tree contract: each edge and combine tree is monotone in the
  environment. A genuinely effectful etf supplies this contract directly, e.g.
  via seqcomp_mono on its QueryL/QueryG/Side construction.

  The per-tree contract is stated on traverse_rhs of the trees the fold composes
  (apply_etf etf a u for edges, etf_combine etf c ex for combine endpoints).
  Everything here is generic in the named-global type 'g; the global-side closure
  bounds (etf_combined_le_eff / etf_combine_combined_le_eff) route the per-name
  side bound through glob_env, so they require 'g::finite.
\<close>

subsection \<open>Monotonicity of the effectful local fold\<close>

lemma side_acc_eff_mono_acc:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  shows "acc1 \<le> acc2 \<Longrightarrow>
         side_acc_eff etf acc1 \<sigma> es cs \<le> side_acc_eff etf acc2 \<sigma> es cs"
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

lemma side_acc_eff_mono:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and sigma1 sigma2 :: "pp + 'g \<Rightarrow> 'a abs_state"
  assumes edge_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (apply_etf etf a u) s1 \<le> traverse_rhs (apply_etf etf a u) s2"
  assumes comb_mono:
    "\<And>cc ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (etf_combine etf cc ex) s1 \<le> traverse_rhs (etf_combine etf cc ex) s2"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_acc_eff etf acc sigma1 es cs \<le> side_acc_eff etf acc sigma2 es cs"
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
      "side_acc_eff etf (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma1) sigma1 [] cs
       \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma1) sigma2 [] cs"
      by (rule Cons.IH)
    have step2:
      "side_acc_eff etf (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma1) sigma2 [] cs
       \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma2) sigma2 [] cs"
      by (rule side_acc_eff_mono_acc[OF sup_mono[OF order_refl c_le]])
    show ?case unfolding x using order_trans[OF step1 step2] by simp
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have c_le: "traverse_rhs (apply_etf etf a u) sigma1
                \<le> traverse_rhs (apply_etf etf a u) sigma2"
    by (rule edge_mono[OF sigma_le])
  have step1:
    "side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) sigma1 es cs
     \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) sigma2 es cs"
    by (rule Cons.IH)
  have step2:
    "side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) sigma2 es cs
     \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma2) sigma2 es cs"
    by (rule side_acc_eff_mono_acc[OF sup_mono[OF order_refl c_le]])
  show ?case unfolding x using order_trans[OF step1 step2] by simp
qed

subsection \<open>is_mono_eq for an arbitrary etf\<close>

lemma side_cfg_T_eff_is_mono_eq_gen:
  fixes g :: cfg
    and etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state" and gseed :: 'g
  assumes edge_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (apply_etf etf a u) s1 \<le> traverse_rhs (apply_etf etf a u) s2"
  assumes comb_mono:
    "\<And>cc ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (etf_combine etf cc ex) s1 \<le> traverse_rhs (etf_combine etf cc ex) s2"
  shows "is_mono_eq (side_cfg_T_eff g etf bot0 s0 gseed)"
  unfolding is_mono_eq_def
proof (intro allI impI)
  fix x :: pp and \<sigma>1 \<sigma>2 :: "pp + 'g \<Rightarrow> 'a abs_state"
  assume le: "\<sigma>1 \<le> \<sigma>2"
  show "eq (side_cfg_T_eff g etf bot0 s0 gseed) x \<sigma>1
        \<le> eq (side_cfg_T_eff g etf bot0 s0 gseed) x \<sigma>2"
    unfolding eq_side_cfg_T_eff
    by (rule side_acc_eff_mono[OF edge_mono comb_mono le])
qed

subsection \<open>Side contributions: independent of acc, monotone in the environment\<close>

text \<open>
  The fold's Side contributions are carried only by the per-tree Side nodes; the
  accumulator flows into the final Answer (sides = bot), so the side map is
  independent of acc.
\<close>
lemma sides_side_rhs_fold_eff_acc_indep:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  shows "sides_of_rhs (side_rhs_fold_eff etf acc1 es cs) \<sigma>
         = sides_of_rhs (side_rhs_fold_eff etf acc2 es cs) \<sigma>"
proof (induction es arbitrary: acc1 acc2 cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc1 acc2)
    case Nil show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have step: "sides_of_rhs (side_rhs_fold_eff etf
                  (acc1 \<squnion> traverse_rhs (etf_combine etf cc ex) \<sigma>) [] cs) \<sigma>
              = sides_of_rhs (side_rhs_fold_eff etf
                  (acc2 \<squnion> traverse_rhs (etf_combine etf cc ex) \<sigma>) [] cs) \<sigma>"
      by (rule Cons.IH)
    show ?case unfolding x side_rhs_fold_eff.simps
      using step by (simp add: sides_of_rhs_seqcomp)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have step: "sides_of_rhs (side_rhs_fold_eff etf
                (acc1 \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) es cs) \<sigma>
            = sides_of_rhs (side_rhs_fold_eff etf
                (acc2 \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) es cs) \<sigma>"
    by (rule Cons.IH)
  show ?case unfolding x side_rhs_fold_eff.simps
    using step by (simp add: sides_of_rhs_seqcomp)
qed

lemma sides_side_rhs_fold_eff_mono:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and sigma1 sigma2 :: "pp + 'g \<Rightarrow> 'a abs_state"
  assumes edge_sides_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (apply_etf etf a u) s1 \<le> sides_of_rhs (apply_etf etf a u) s2"
  assumes comb_sides_mono:
    "\<And>cc ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (etf_combine etf cc ex) s1 \<le> sides_of_rhs (etf_combine etf cc ex) s2"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "sides_of_rhs (side_rhs_fold_eff etf acc es cs) sigma1
         \<le> sides_of_rhs (side_rhs_fold_eff etf acc es cs) sigma2"
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
    have ih: "sides_of_rhs (side_rhs_fold_eff etf
                (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma1) [] cs) sigma1
            \<le> sides_of_rhs (side_rhs_fold_eff etf
                (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma1) [] cs) sigma2"
      by (rule Cons.IH)
    have rest_le: "sides_of_rhs (side_rhs_fold_eff etf
                     (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma1) [] cs) sigma1
                 \<le> sides_of_rhs (side_rhs_fold_eff etf
                     (acc \<squnion> traverse_rhs (etf_combine etf cc ex) sigma2) [] cs) sigma2"
      using ih sides_side_rhs_fold_eff_acc_indep by metis
    show ?case unfolding x side_rhs_fold_eff.simps
      by (simp only: sides_of_rhs_seqcomp) (rule sup_mono[OF g_le rest_le])
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have g_le: "sides_of_rhs (apply_etf etf a u) sigma1
                \<le> sides_of_rhs (apply_etf etf a u) sigma2"
    by (rule edge_sides_mono[OF sigma_le])
  have ih: "sides_of_rhs (side_rhs_fold_eff etf
              (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) es cs) sigma1
          \<le> sides_of_rhs (side_rhs_fold_eff etf
              (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) es cs) sigma2"
    by (rule Cons.IH)
  have rest_le: "sides_of_rhs (side_rhs_fold_eff etf
                   (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) es cs) sigma1
               \<le> sides_of_rhs (side_rhs_fold_eff etf
                   (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma2) es cs) sigma2"
    using ih sides_side_rhs_fold_eff_acc_indep by metis
  show ?case unfolding x side_rhs_fold_eff.simps
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

lemma side_cfg_T_eff_mono_sides_gen:
  fixes g :: cfg
    and etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state" and gseed :: 'g
  assumes edge_sides_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (apply_etf etf a u) s1 \<le> sides_of_rhs (apply_etf etf a u) s2"
  assumes comb_sides_mono:
    "\<And>cc ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (etf_combine etf cc ex) s1 \<le> sides_of_rhs (etf_combine etf cc ex) s2"
  shows "mono_sides (side_cfg_T_eff g etf bot0 s0 gseed)"
proof (unfold mono_sides_def, intro allI impI)
  fix w :: pp and \<sigma>1 \<sigma>2 :: "pp + 'g \<Rightarrow> 'a abs_state"
  assume le: "\<sigma>1 \<le> \<sigma>2"
  have fold_le: "\<And>acc. sides_of_rhs (side_rhs_fold_eff etf acc
                   (predecessor_list g w) (combine_predecessor_list g w)) \<sigma>1
                 \<le> sides_of_rhs (side_rhs_fold_eff etf acc
                   (predecessor_list g w) (combine_predecessor_list g w)) \<sigma>2"
    by (rule sides_side_rhs_fold_eff_mono[OF edge_sides_mono comb_sides_mono le])
  show "sides_of_rhs (side_cfg_T_eff g etf bot0 s0 gseed w) \<sigma>1
        \<le> sides_of_rhs (side_cfg_T_eff g etf bot0 s0 gseed w) \<sigma>2"
  proof (cases "w = cfg_entry g")
    case False
    show ?thesis
      unfolding side_cfg_T_eff_def make_side_rhs_tree_eff_def Let_def
      using False fold_le[of bot0] by simp
  next
    case True
    have m_le: "sides_of_rhs (side_rhs_fold_eff etf (bot0 \<squnion> restrict_local s0)
                  (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))) \<sigma>1
              \<le> sides_of_rhs (side_rhs_fold_eff etf (bot0 \<squnion> restrict_local s0)
                  (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))) \<sigma>2"
      using fold_le[of "bot0 \<squnion> restrict_local s0"] True by simp
    show ?thesis
      unfolding side_cfg_T_eff_def make_side_rhs_tree_eff_def
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
lemma dep_aux_side_rhs_fold_eff_indep:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  shows "dep_aux \<sigma>1 (side_rhs_fold_eff etf acc1 es cs)
       = dep_aux \<sigma>2 (side_rhs_fold_eff etf acc2 es cs)"
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
    have ih: "dep_aux \<sigma>1 (side_rhs_fold_eff etf
                (acc1 \<squnion> traverse_rhs (etf_combine etf cc ex) \<sigma>1) [] cs)
            = dep_aux \<sigma>2 (side_rhs_fold_eff etf
                (acc2 \<squnion> traverse_rhs (etf_combine etf cc ex) \<sigma>2) [] cs)"
      by (rule Cons.IH)
    show ?case unfolding x side_rhs_fold_eff.simps
      by (simp add: dep_aux_seqcomp e ih)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have e: "dep_aux \<sigma>1 (apply_etf etf a u) = dep_aux \<sigma>2 (apply_etf etf a u)"
    using edge_static unfolding static_deps_def by blast
  have ih: "dep_aux \<sigma>1 (side_rhs_fold_eff etf
              (acc1 \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>1) es cs)
          = dep_aux \<sigma>2 (side_rhs_fold_eff etf
              (acc2 \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>2) es cs)"
    by (rule Cons.IH)
  show ?case unfolding x side_rhs_fold_eff.simps
    by (simp add: dep_aux_seqcomp e ih)
qed

lemma dep_aux_make_side_rhs_tree_eff:
  "dep_aux \<sigma> (make_side_rhs_tree_eff g etf bot0 s0 gseed v)
   = dep_aux \<sigma> (side_rhs_fold_eff etf
        (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
        (predecessor_list g v) (combine_predecessor_list g v))"
  by (cases "v = cfg_entry g")
     (simp_all add: make_side_rhs_tree_eff_def Let_def)

lemma side_cfg_T_eff_mono_deps_gen:
  fixes g :: cfg
    and etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state" and gseed :: 'g
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  shows "mono_deps (side_cfg_T_eff g etf bot0 s0 gseed)"
  unfolding mono_deps_def side_cfg_T_eff_def dep_def
  apply clarify
  apply (simp only: dep_aux_make_side_rhs_tree_eff)
  apply (subst (asm) dep_aux_side_rhs_fold_eff_indep[OF edge_static comb_static])
  apply assumption
  done

subsection \<open>Fold upper bounds: each contribution is below the fold\<close>

lemma side_acc_eff_ge_acc:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  shows "acc \<le> side_acc_eff etf acc \<sigma> es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc)
    case Nil show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have "acc \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (etf_combine etf cc ex) \<sigma>) \<sigma> [] cs"
      by (meson Cons.IH sup_ge1 order_trans)
    then show ?case unfolding x by (simp only: side_acc_eff.simps)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have "acc \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) \<sigma> es cs"
    by (meson Cons.IH sup_ge1 order_trans)
  then show ?case unfolding x by (simp only: side_acc_eff.simps)
qed

lemma side_acc_eff_es_mono:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  shows "side_acc_eff etf acc \<sigma> [] cs \<le> side_acc_eff etf acc \<sigma> es cs"
proof (induction es arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have "side_acc_eff etf acc \<sigma> [] cs
        \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) \<sigma> [] cs"
    by (rule side_acc_eff_mono_acc[OF sup_ge1])
  also have "\<dots> \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) \<sigma> es cs"
    by (rule Cons.IH)
  finally show ?case unfolding x by (simp only: side_acc_eff.simps)
qed

lemma traverse_le_side_acc_eff_edge:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  shows "(u, a) \<in> set es \<Longrightarrow>
         traverse_rhs (apply_etf etf a u) \<sigma> \<le> side_acc_eff etf acc \<sigma> es cs"
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
    have "traverse_rhs (apply_etf etf b w) \<sigma>
          \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf b w) \<sigma>) \<sigma> es cs"
      using side_acc_eff_ge_acc sup_ge2 order_trans by blast
    thus ?thesis unfolding x uw ab by (simp only: side_acc_eff.simps)
  next
    case tl
    have "traverse_rhs (apply_etf etf a u) \<sigma>
          \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf b w) \<sigma>) \<sigma> es cs"
      by (rule Cons.IH[OF tl])
    thus ?thesis unfolding x by (simp only: side_acc_eff.simps)
  qed
qed

lemma traverse_le_side_acc_eff_combine_nil:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  shows "(cc, ex) \<in> set cs \<Longrightarrow>
         traverse_rhs (etf_combine etf cc ex) \<sigma> \<le> side_acc_eff etf acc \<sigma> [] cs"
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
    have "traverse_rhs (etf_combine etf c2 e2) \<sigma>
          \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (etf_combine etf c2 e2) \<sigma>) \<sigma> [] cs"
      using side_acc_eff_ge_acc sup_ge2 order_trans by blast
    thus ?thesis unfolding x cc2 exe2 by (simp only: side_acc_eff.simps)
  next
    case tl
    have "traverse_rhs (etf_combine etf cc ex) \<sigma>
          \<le> side_acc_eff etf (acc \<squnion> traverse_rhs (etf_combine etf c2 e2) \<sigma>) \<sigma> [] cs"
      by (rule Cons.IH[OF tl])
    thus ?thesis unfolding x by (simp only: side_acc_eff.simps)
  qed
qed

lemma traverse_le_side_acc_eff_combine:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes "(cc, ex) \<in> set cs"
  shows "traverse_rhs (etf_combine etf cc ex) \<sigma> \<le> side_acc_eff etf acc \<sigma> es cs"
  using traverse_le_side_acc_eff_combine_nil[OF assms] side_acc_eff_es_mono
  by (rule order_trans)

lemma sides_le_side_rhs_fold_eff_edge:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  shows "(u, a) \<in> set es \<Longrightarrow>
         sides_of_rhs (apply_etf etf a u) \<sigma> (Inr gg)
           \<le> sides_of_rhs (side_rhs_fold_eff etf acc es cs) \<sigma> (Inr gg)"
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
    show ?thesis unfolding x uw ab side_rhs_fold_eff.simps
      by (simp only: sides_of_rhs_seqcomp_at) (rule sup_ge1)
  next
    case tl
    have ih: "sides_of_rhs (apply_etf etf a u) \<sigma> (Inr gg)
          \<le> sides_of_rhs (side_rhs_fold_eff etf
               (acc \<squnion> traverse_rhs (apply_etf etf b w) \<sigma>) es cs) \<sigma> (Inr gg)"
      by (rule Cons.IH[OF tl])
    show ?thesis unfolding x side_rhs_fold_eff.simps
      by (simp only: sides_of_rhs_seqcomp_at) (rule le_supI2[OF ih])
  qed
qed

lemma sides_le_side_rhs_fold_eff_combine_nil:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  shows "(cc, ex) \<in> set cs \<Longrightarrow>
         sides_of_rhs (etf_combine etf cc ex) \<sigma> (Inr gg)
           \<le> sides_of_rhs (side_rhs_fold_eff etf acc [] cs) \<sigma> (Inr gg)"
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
    show ?thesis unfolding x cc2 exe2 side_rhs_fold_eff.simps
      by (simp only: sides_of_rhs_seqcomp_at) (rule sup_ge1)
  next
    case tl
    have ih: "sides_of_rhs (etf_combine etf cc ex) \<sigma> (Inr gg)
          \<le> sides_of_rhs (side_rhs_fold_eff etf
               (acc \<squnion> traverse_rhs (etf_combine etf c2 e2) \<sigma>) [] cs) \<sigma> (Inr gg)"
      by (rule Cons.IH[OF tl])
    show ?thesis unfolding x side_rhs_fold_eff.simps
      by (simp only: sides_of_rhs_seqcomp_at) (rule le_supI2[OF ih])
  qed
qed

lemma sides_side_rhs_fold_eff_es_mono:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  shows "sides_of_rhs (side_rhs_fold_eff etf acc [] cs) \<sigma> (Inr gg)
         \<le> sides_of_rhs (side_rhs_fold_eff etf acc es cs) \<sigma> (Inr gg)"
proof (induction es arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have acc_eq: "sides_of_rhs (side_rhs_fold_eff etf acc [] cs) \<sigma> (Inr gg)
              = sides_of_rhs (side_rhs_fold_eff etf
                  (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) [] cs) \<sigma> (Inr gg)"
    by (rule fun_cong[OF sides_side_rhs_fold_eff_acc_indep])
  have ih: "sides_of_rhs (side_rhs_fold_eff etf
              (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) [] cs) \<sigma> (Inr gg)
          \<le> sides_of_rhs (side_rhs_fold_eff etf
              (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) es cs) \<sigma> (Inr gg)"
    by (rule Cons.IH)
  show ?case unfolding x side_rhs_fold_eff.simps
    apply (simp only: sides_of_rhs_seqcomp_at)
    apply (subst acc_eq)
    by (rule le_supI2[OF ih])
qed

lemma sides_le_side_rhs_fold_eff_combine:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes "(cc, ex) \<in> set cs"
  shows "sides_of_rhs (etf_combine etf cc ex) \<sigma> (Inr gg)
         \<le> sides_of_rhs (side_rhs_fold_eff etf acc es cs) \<sigma> (Inr gg)"
  using sides_le_side_rhs_fold_eff_combine_nil[OF assms]
        sides_side_rhs_fold_eff_es_mono
  by (rule order_trans)

subsection \<open>Post-solution in usable form\<close>

lemma side_post_solution_le_local_eff:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g
  assumes "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) x \<sigma> vars"
      and "v \<in> vars"
  shows "side_acc_eff etf
           (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
           \<sigma> (predecessor_list g v) (combine_predecessor_list g v) \<le> \<sigma> (Inl v)"
proof -
  from assms have "eq (side_cfg_T_eff g etf bot0 s0 gseed) v \<sigma> \<le> \<sigma> (Inl v)" by auto
  thus ?thesis by (simp add: eq_side_cfg_T_eff)
qed

(* The fold's global contribution is below the packaged tree's (the entry Side
   wrapper only adds, at slot gseed). *)
lemma sides_fold_le_side_cfg_T_eff:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g
  shows "sides_of_rhs (side_rhs_fold_eff etf
           (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
           (predecessor_list g v) (combine_predecessor_list g v)) \<sigma> (Inr gg)
         \<le> sides_of_rhs (side_cfg_T_eff g etf bot0 s0 gseed v) \<sigma> (Inr gg)"
  unfolding side_cfg_T_eff_def make_side_rhs_tree_eff_def Let_def
  by (cases "v = cfg_entry g") (auto simp: fun_upd_def Let_def)

lemma side_post_solution_le_global_eff:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g
  assumes pp: "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) x \<sigma> vars"
      and v: "v \<in> vars"
  shows "sides_of_rhs (side_cfg_T_eff g etf bot0 s0 gseed v) \<sigma> (Inr gg) \<le> \<sigma> (Inr gg)"
proof -
  from pp v have "sides_of_rhs (side_cfg_T_eff g etf bot0 s0 gseed v) \<sigma> \<le> \<sigma>" by auto
  thus ?thesis by (rule le_funD)
qed

subsection \<open>Edge / combine closure of a post-solution\<close>

lemma etf_combined_le_eff:
  fixes etf :: "('g::finite, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g
  assumes pp:  "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) x \<sigma> vars"
      and v:   "v \<in> vars"
      and e:   "(u, a, v) \<in> edges g"
      and fin: "finite (edges g)"
  shows "etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> v"
proof -
  have mem: "(u, a) \<in> set (predecessor_list g v)"
    using e by (simp add: set_predecessor_list[OF fin] predecessors_def)
  have loc: "traverse_rhs (apply_etf etf a u) \<sigma> \<le> \<sigma> (Inl v)"
    using traverse_le_side_acc_eff_edge[OF mem]
          side_post_solution_le_local_eff[OF pp v]
    by (rule order_trans)
  have glob_name: "\<And>gg. sides_of_rhs (apply_etf etf a u) \<sigma> (Inr gg) \<le> \<sigma> (Inr gg)"
    using sides_le_side_rhs_fold_eff_edge[OF mem]
          sides_fold_le_side_cfg_T_eff
          side_post_solution_le_global_eff[OF pp v]
    by (meson order_trans)
  have glob: "all_sides (apply_etf etf a u) \<sigma> \<le> glob_env \<sigma>"
  proof -
    have "all_sides (apply_etf etf a u) \<sigma>
          \<le> glob_env (sides_of_rhs (apply_etf etf a u) \<sigma>)"
      by (rule all_sides_le_glob_env_sides)
    also have "\<dots> \<le> glob_env \<sigma>" by (rule glob_env_mono_Inr) (rule glob_name)
    finally show ?thesis .
  qed
  have "etf_full (apply_etf etf a u) \<sigma>
        = traverse_rhs (apply_etf etf a u) \<sigma> \<squnion> all_sides (apply_etf etf a u) \<sigma>"
    by (simp add: etf_full_def)
  also have "\<dots> \<le> \<sigma> (Inl v) \<squnion> glob_env \<sigma>" using loc glob by (rule sup_mono)
  finally show ?thesis unfolding side_env_def .
qed

lemma etf_combine_combined_le_eff:
  fixes etf :: "('g::finite, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g
  assumes pp:   "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) x \<sigma> vars"
      and v:    "v \<in> vars"
      and e:    "(cc, ex, v) \<in> combines g"
      and finC: "finite (combines g)"
  shows "etf_full (etf_combine etf cc ex) \<sigma> \<le> side_env \<sigma> v"
proof -
  have mem: "(cc, ex) \<in> set (combine_predecessor_list g v)"
    using e by (simp add: set_combine_predecessor_list[OF finC] combine_predecessors_def)
  have loc: "traverse_rhs (etf_combine etf cc ex) \<sigma> \<le> \<sigma> (Inl v)"
    using traverse_le_side_acc_eff_combine[OF mem]
          side_post_solution_le_local_eff[OF pp v]
    by (rule order_trans)
  have glob_name: "\<And>gg. sides_of_rhs (etf_combine etf cc ex) \<sigma> (Inr gg) \<le> \<sigma> (Inr gg)"
    using sides_le_side_rhs_fold_eff_combine[OF mem]
          sides_fold_le_side_cfg_T_eff
          side_post_solution_le_global_eff[OF pp v]
    by (meson order_trans)
  have glob: "all_sides (etf_combine etf cc ex) \<sigma> \<le> glob_env \<sigma>"
  proof -
    have "all_sides (etf_combine etf cc ex) \<sigma>
          \<le> glob_env (sides_of_rhs (etf_combine etf cc ex) \<sigma>)"
      by (rule all_sides_le_glob_env_sides)
    also have "\<dots> \<le> glob_env \<sigma>" by (rule glob_env_mono_Inr) (rule glob_name)
    finally show ?thesis .
  qed
  have "etf_full (etf_combine etf cc ex) \<sigma>
        = traverse_rhs (etf_combine etf cc ex) \<sigma> \<squnion> all_sides (etf_combine etf cc ex) \<sigma>"
    by (simp add: etf_full_def)
  also have "\<dots> \<le> \<sigma> (Inl v) \<squnion> glob_env \<sigma>" using loc glob by (rule sup_mono)
  finally show ?thesis unfolding side_env_def .
qed

end
