theory TD_Side_Eff_Bounds
  imports TD_Side_Tree Solver_Mono
begin

section \<open>Effectful side IP solver: general monotonicity\<close>

text \<open>
  Monotonicity of the effectful equation system for an arbitrary etf follows
  from a per-tree contract: each edge, enter and combine tree is monotone in the
  environment. A genuinely effectful etf supplies this contract directly, e.g.
  via seqcomp_mono on its QueryL/QueryG/Side construction.

  The per-tree contract is stated on traverse_rhs of the trees the fold composes
  (apply_etf etf a u for ordinary edges, etf_enter etf fs as cl for call entries,
  etf_combine_collect etf dst cc ex for caller continuations).  Everything here is generic
  in the named-global type 'g; the global-side closure bounds
  (etf_combined_le_eff / etf_enter_combined_le_eff / etf_combine_combined_le_eff)
  route the per-name side bound through glob_env, so they require 'g::finite.
\<close>

subsection \<open>Monotonicity of the effectful local fold\<close>

lemma fold_rhs_values_mono:
  fixes \<sigma>1 \<sigma>2 :: "'k + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot"
  assumes acc: "acc1 \<le> acc2"
    and trees: "\<And>t. t \<in> set ts \<Longrightarrow> traverse_rhs t \<sigma>1 \<le> traverse_rhs t \<sigma>2"
  shows "fold_rhs_values acc1 \<sigma>1 ts \<le> fold_rhs_values acc2 \<sigma>2 ts"
  using assms
proof (induction ts arbitrary: acc1 acc2)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have step: "acc1 \<squnion> traverse_rhs t \<sigma>1 \<le> acc2 \<squnion> traverse_rhs t \<sigma>2"
    by (rule sup_mono[OF Cons.prems(1) Cons.prems(2)]) simp
  have rest: "\<And>u. u \<in> set ts \<Longrightarrow> traverse_rhs u \<sigma>1 \<le> traverse_rhs u \<sigma>2"
    using Cons.prems(2) by simp
  show ?case by (simp add: Cons.IH[OF step rest])
qed

lemma side_acc_eff_mono_acc:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes "acc1 \<le> acc2"
  shows "side_acc_eff etf acc1 \<sigma> es ens cs \<le> side_acc_eff etf acc2 \<sigma> es ens cs"
  unfolding side_acc_eff_def
  by (rule fold_rhs_values_mono[OF assms]) simp

lemma side_acc_eff_mono:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and sigma1 sigma2 :: "pp + 'g \<Rightarrow> 'a abs_state lifted"
  assumes edge_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (apply_etf etf a u) s1 \<le> traverse_rhs (apply_etf etf a u) s2"
  assumes enter_mono:
    "\<And>cl fs as s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (etf_enter etf fs as cl) s1 \<le> traverse_rhs (etf_enter etf fs as cl) s2"
  assumes comb_mono:
    "\<And>cc dst ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (etf_combine_collect etf dst cc ex) s1 \<le> traverse_rhs (etf_combine_collect etf dst cc ex) s2"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_acc_eff etf acc sigma1 es ens cs \<le> side_acc_eff etf acc sigma2 es ens cs"
  unfolding side_acc_eff_def
  apply (rule fold_rhs_values_mono[OF order_refl])
  unfolding side_contribution_trees_def
  using edge_mono enter_mono comb_mono sigma_le
  by (auto split: prod.splits)


subsection \<open>is_mono_eq for an arbitrary etf\<close>

lemma side_cfg_T_eff_is_mono_eq_gen:
  fixes g :: cfg
    and etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state" and gseed :: 'g
  assumes edge_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (apply_etf etf a u) s1 \<le> traverse_rhs (apply_etf etf a u) s2"
  assumes enter_mono:
    "\<And>cl fs as s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (etf_enter etf fs as cl) s1 \<le> traverse_rhs (etf_enter etf fs as cl) s2"
  assumes comb_mono:
    "\<And>cc dst ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (etf_combine_collect etf dst cc ex) s1 \<le> traverse_rhs (etf_combine_collect etf dst cc ex) s2"
  shows "is_mono_eq (side_cfg_T_eff gs g etf bot0 s0 gseed)"
  unfolding is_mono_eq_def
proof (intro allI impI)
  fix x :: pp and \<sigma>1 \<sigma>2 :: "pp + 'g \<Rightarrow> 'a abs_state lifted"
  assume le: "\<sigma>1 \<le> \<sigma>2"
  show "eq (side_cfg_T_eff gs g etf bot0 s0 gseed) x \<sigma>1
        \<le> eq (side_cfg_T_eff gs g etf bot0 s0 gseed) x \<sigma>2"
    unfolding eq_side_cfg_T_eff
    by (rule side_acc_eff_mono[OF edge_mono enter_mono comb_mono le])
qed

subsection \<open>Side contributions: independent of acc, monotone in the environment\<close>

text \<open>
  The fold's Side contributions are carried only by the per-tree Side nodes; the
  accumulator flows into the final Answer (sides = bot), so the side map is
  independent of acc.
\<close>
lemma sides_side_rhs_fold_eff_acc_indep:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  shows "sides_of_rhs (side_rhs_fold_eff etf acc1 es ens cs) \<sigma>
         = sides_of_rhs (side_rhs_fold_eff etf acc2 es ens cs) \<sigma>"
proof (induction es arbitrary: acc1 acc2 ens cs)
  case Nil
  show ?case
  proof (induction ens arbitrary: acc1 acc2 cs)
    case Nil
    show ?case
    proof (induction cs arbitrary: acc1 acc2)
      case Nil show ?case by simp
    next
      case (Cons x cs)
      obtain cc dst ex where x: "x = (cc, dst, ex)" by (cases x)
      have step: "sides_of_rhs (side_rhs_fold_eff etf
                    (acc1 \<squnion> traverse_rhs (etf_combine_collect etf dst cc ex) \<sigma>) [] [] cs) \<sigma>
                = sides_of_rhs (side_rhs_fold_eff etf
                    (acc2 \<squnion> traverse_rhs (etf_combine_collect etf dst cc ex) \<sigma>) [] [] cs) \<sigma>"
        by (rule Cons.IH)
      show ?case unfolding x side_rhs_fold_eff_simps
        using step by (simp add: sides_of_rhs_seqcomp)
    qed
  next
    case (Cons x ens)
    obtain cl fs as where x: "x = (cl, fs, as)" by (cases x)
    have step: "sides_of_rhs (side_rhs_fold_eff etf
                  (acc1 \<squnion> traverse_rhs (etf_enter etf fs as cl) \<sigma>) [] ens cs) \<sigma>
              = sides_of_rhs (side_rhs_fold_eff etf
                  (acc2 \<squnion> traverse_rhs (etf_enter etf fs as cl) \<sigma>) [] ens cs) \<sigma>"
      by (rule Cons.IH)
    show ?case unfolding x side_rhs_fold_eff_simps
      using step by (simp add: sides_of_rhs_seqcomp)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have step: "sides_of_rhs (side_rhs_fold_eff etf
                (acc1 \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) es ens cs) \<sigma>
            = sides_of_rhs (side_rhs_fold_eff etf
                (acc2 \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) es ens cs) \<sigma>"
    by (rule Cons.IH)
  show ?case unfolding x side_rhs_fold_eff_simps
    using step by (simp add: sides_of_rhs_seqcomp)
qed

lemma sides_side_rhs_fold_eff_mono:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and sigma1 sigma2 :: "pp + 'g \<Rightarrow> 'a abs_state lifted"
  assumes edge_sides_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (apply_etf etf a u) s1 \<le> sides_of_rhs (apply_etf etf a u) s2"
  assumes enter_sides_mono:
    "\<And>cl fs as s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (etf_enter etf fs as cl) s1 \<le> sides_of_rhs (etf_enter etf fs as cl) s2"
  assumes comb_sides_mono:
    "\<And>cc dst ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (etf_combine_collect etf dst cc ex) s1 \<le> sides_of_rhs (etf_combine_collect etf dst cc ex) s2"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "sides_of_rhs (side_rhs_fold_eff etf acc es ens cs) sigma1
         \<le> sides_of_rhs (side_rhs_fold_eff etf acc es ens cs) sigma2"
proof (induction es arbitrary: acc ens cs)
  case Nil
  show ?case
  proof (induction ens arbitrary: acc cs)
    case Nil
    show ?case
    proof (induction cs arbitrary: acc)
      case Nil show ?case by simp
    next
      case (Cons x cs)
      obtain cc dst ex where x: "x = (cc, dst, ex)" by (cases x)
      have g_le: "sides_of_rhs (etf_combine_collect etf dst cc ex) sigma1
                    \<le> sides_of_rhs (etf_combine_collect etf dst cc ex) sigma2"
        by (rule comb_sides_mono[OF sigma_le])
      have ih: "sides_of_rhs (side_rhs_fold_eff etf
                  (acc \<squnion> traverse_rhs (etf_combine_collect etf dst cc ex) sigma1) [] [] cs) sigma1
              \<le> sides_of_rhs (side_rhs_fold_eff etf
                  (acc \<squnion> traverse_rhs (etf_combine_collect etf dst cc ex) sigma1) [] [] cs) sigma2"
        by (rule Cons.IH)
      have rest_le: "sides_of_rhs (side_rhs_fold_eff etf
                       (acc \<squnion> traverse_rhs (etf_combine_collect etf dst cc ex) sigma1) [] [] cs) sigma1
                   \<le> sides_of_rhs (side_rhs_fold_eff etf
                       (acc \<squnion> traverse_rhs (etf_combine_collect etf dst cc ex) sigma2) [] [] cs) sigma2"
        using ih sides_side_rhs_fold_eff_acc_indep by metis
      show ?case unfolding x side_rhs_fold_eff_simps
        by (simp only: sides_of_rhs_seqcomp) (rule sup_mono[OF g_le rest_le])
    qed
  next
    case (Cons x ens)
    obtain cl fs as where x: "x = (cl, fs, as)" by (cases x)
    have g_le: "sides_of_rhs (etf_enter etf fs as cl) sigma1
                  \<le> sides_of_rhs (etf_enter etf fs as cl) sigma2"
      by (rule enter_sides_mono[OF sigma_le])
    have ih: "sides_of_rhs (side_rhs_fold_eff etf
                (acc \<squnion> traverse_rhs (etf_enter etf fs as cl) sigma1) [] ens cs) sigma1
            \<le> sides_of_rhs (side_rhs_fold_eff etf
                (acc \<squnion> traverse_rhs (etf_enter etf fs as cl) sigma1) [] ens cs) sigma2"
      by (rule Cons.IH)
    have rest_le: "sides_of_rhs (side_rhs_fold_eff etf
                     (acc \<squnion> traverse_rhs (etf_enter etf fs as cl) sigma1) [] ens cs) sigma1
                 \<le> sides_of_rhs (side_rhs_fold_eff etf
                     (acc \<squnion> traverse_rhs (etf_enter etf fs as cl) sigma2) [] ens cs) sigma2"
      using ih sides_side_rhs_fold_eff_acc_indep by metis
    show ?case unfolding x side_rhs_fold_eff_simps
      by (simp only: sides_of_rhs_seqcomp) (rule sup_mono[OF g_le rest_le])
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have g_le: "sides_of_rhs (apply_etf etf a u) sigma1
                \<le> sides_of_rhs (apply_etf etf a u) sigma2"
    by (rule edge_sides_mono[OF sigma_le])
  have ih: "sides_of_rhs (side_rhs_fold_eff etf
              (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) es ens cs) sigma1
          \<le> sides_of_rhs (side_rhs_fold_eff etf
              (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) es ens cs) sigma2"
    by (rule Cons.IH)
  have rest_le: "sides_of_rhs (side_rhs_fold_eff etf
                   (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma1) es ens cs) sigma1
               \<le> sides_of_rhs (side_rhs_fold_eff etf
                   (acc \<squnion> traverse_rhs (apply_etf etf a u) sigma2) es ens cs) sigma2"
    using ih sides_side_rhs_fold_eff_acc_indep by metis
  show ?case unfolding x side_rhs_fold_eff_simps
    by (simp only: sides_of_rhs_seqcomp) (rule sup_mono[OF g_le rest_le])
qed

subsection \<open>mono_sides for an arbitrary etf\<close>


lemma side_cfg_T_eff_mono_sides_gen:
  fixes g :: cfg
    and etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state" and gseed :: 'g
  assumes edge_sides_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (apply_etf etf a u) s1 \<le> sides_of_rhs (apply_etf etf a u) s2"
  assumes enter_sides_mono:
    "\<And>cl fs as s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (etf_enter etf fs as cl) s1 \<le> sides_of_rhs (etf_enter etf fs as cl) s2"
  assumes comb_sides_mono:
    "\<And>cc dst ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (etf_combine_collect etf dst cc ex) s1 \<le> sides_of_rhs (etf_combine_collect etf dst cc ex) s2"

  shows "mono_sides (side_cfg_T_eff gs g etf bot0 s0 gseed)"
proof (unfold mono_sides_def, intro allI impI)
  fix w :: pp and \<sigma>1 \<sigma>2 :: "pp + 'g \<Rightarrow> 'a abs_state lifted"
  assume le: "\<sigma>1 \<le> \<sigma>2"
  have fold_le: "\<And>acc. sides_of_rhs (side_rhs_fold_eff etf acc
                   (intra_predecessor_list g w) (entry_seed_list g w) (return_call_list g w)) \<sigma>1
                 \<le> sides_of_rhs (side_rhs_fold_eff etf acc
                   (intra_predecessor_list g w) (entry_seed_list g w) (return_call_list g w)) \<sigma>2"
    by (rule sides_side_rhs_fold_eff_mono[OF edge_sides_mono enter_sides_mono comb_sides_mono le])
  show "sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed w) \<sigma>1
        \<le> sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed w) \<sigma>2"
  proof (cases "w = cfg_entry g")
    case False
    show ?thesis
      unfolding side_cfg_T_eff_def make_side_rhs_tree_eff_def Let_def
      using False fold_le[of Bot] by simp
  next
    case True
    have m_le: "sides_of_rhs (side_rhs_fold_eff etf (Lifted (bot0 \<squnion> restrict_local_for gs s0))
                  (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g))
                  (return_call_list g (cfg_entry g))) \<sigma>1
              \<le> sides_of_rhs (side_rhs_fold_eff etf (Lifted (bot0 \<squnion> restrict_local_for gs s0))
                  (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g))
                  (return_call_list g (cfg_entry g))) \<sigma>2"
      using fold_le[of "Lifted (bot0 \<squnion> restrict_local_for gs s0)"] True by simp
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
      and enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
      and comb_static: "\<And>cc dst ex. static_deps (etf_combine_collect etf dst cc ex)"
  shows "dep_aux \<sigma>1 (side_rhs_fold_eff etf acc1 es ens cs)
       = dep_aux \<sigma>2 (side_rhs_fold_eff etf acc2 es ens cs)"
proof (induction es arbitrary: acc1 acc2 ens cs \<sigma>1 \<sigma>2)
  case Nil
  show ?case
  proof (induction ens arbitrary: acc1 acc2 cs \<sigma>1 \<sigma>2)
    case Nil
    show ?case
    proof (induction cs arbitrary: acc1 acc2 \<sigma>1 \<sigma>2)
      case Nil show ?case by simp
    next
      case (Cons x cs)
      obtain cc dst ex where x: "x = (cc, dst, ex)" by (cases x)
      have e: "dep_aux \<sigma>1 (etf_combine_collect etf dst cc ex) = dep_aux \<sigma>2 (etf_combine_collect etf dst cc ex)"
        using comb_static unfolding static_deps_def by blast
      have ih: "dep_aux \<sigma>1 (side_rhs_fold_eff etf
                  (acc1 \<squnion> traverse_rhs (etf_combine_collect etf dst cc ex) \<sigma>1) [] [] cs)
              = dep_aux \<sigma>2 (side_rhs_fold_eff etf
                  (acc2 \<squnion> traverse_rhs (etf_combine_collect etf dst cc ex) \<sigma>2) [] [] cs)"
        by (rule Cons.IH)
      show ?case unfolding x side_rhs_fold_eff_simps
        by (simp add: dep_aux_seqcomp e ih)
    qed
  next
    case (Cons x ens)
    obtain cl fs as where x: "x = (cl, fs, as)" by (cases x)
    have e: "dep_aux \<sigma>1 (etf_enter etf fs as cl) = dep_aux \<sigma>2 (etf_enter etf fs as cl)"
      using enter_static unfolding static_deps_def by blast
    have ih: "dep_aux \<sigma>1 (side_rhs_fold_eff etf
                (acc1 \<squnion> traverse_rhs (etf_enter etf fs as cl) \<sigma>1) [] ens cs)
            = dep_aux \<sigma>2 (side_rhs_fold_eff etf
                (acc2 \<squnion> traverse_rhs (etf_enter etf fs as cl) \<sigma>2) [] ens cs)"
      by (rule Cons.IH)
    show ?case unfolding x side_rhs_fold_eff_simps
      by (simp add: dep_aux_seqcomp e ih)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have e: "dep_aux \<sigma>1 (apply_etf etf a u) = dep_aux \<sigma>2 (apply_etf etf a u)"
    using edge_static unfolding static_deps_def by blast
  have ih: "dep_aux \<sigma>1 (side_rhs_fold_eff etf
              (acc1 \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>1) es ens cs)
          = dep_aux \<sigma>2 (side_rhs_fold_eff etf
              (acc2 \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>2) es ens cs)"
    by (rule Cons.IH)
  show ?case unfolding x side_rhs_fold_eff_simps
    by (simp add: dep_aux_seqcomp e ih)
qed

lemma dep_aux_make_side_rhs_tree_eff:
  "dep_aux \<sigma> (make_side_rhs_tree_eff gs g etf bot0 s0 gseed v)
   = dep_aux \<sigma> (side_rhs_fold_eff etf
        (if v = cfg_entry g then Lifted (bot0 \<squnion> restrict_local_for gs s0) else Bot)
        (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v))"
  by (cases "v = cfg_entry g")
     (simp_all add: make_side_rhs_tree_eff_def Let_def)

lemma side_cfg_T_eff_mono_deps_gen:
  fixes g :: cfg
    and etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state" and gseed :: 'g
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
      and comb_static: "\<And>cc dst ex. static_deps (etf_combine_collect etf dst cc ex)"
  shows "mono_deps (side_cfg_T_eff gs g etf bot0 s0 gseed)"
  unfolding mono_deps_def side_cfg_T_eff_def dep_def
  apply clarify
  apply (simp only: dep_aux_make_side_rhs_tree_eff)
  apply (subst (asm) dep_aux_side_rhs_fold_eff_indep[OF edge_static enter_static comb_static])
  apply assumption
  done

subsection \<open>Fold upper bounds for contribution sides\<close>

text \<open>
  Every named-global side effect of a contribution tree lies below the side map
  of the complete fold.  The proof depends only on membership in the assembled
  contribution list, so all three source families share one induction.
\<close>

lemma sides_le_fold_rhs_trees:
  fixes ts :: "('k, 'g, 'a::bounded_semilattice_sup_bot) strategy_tree list"
  assumes "t \<in> set ts"
  shows "sides_of_rhs t \<sigma> k \<le> sides_of_rhs (fold_rhs_trees acc ts) \<sigma> k"
  using assms
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t' ts)
  then show ?case
    by (auto simp: sides_of_rhs_seqcomp_at intro: le_supI2)
qed

lemma sides_le_side_rhs_fold_eff_edge:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes "(u, a) \<in> set es"
  shows "sides_of_rhs (apply_etf etf a u) \<sigma> (Inr gg)
         \<le> sides_of_rhs (side_rhs_fold_eff etf acc es ens cs) \<sigma> (Inr gg)"
  unfolding side_rhs_fold_eff_def
  by (rule sides_le_fold_rhs_trees) (use assms in \<open>auto simp: side_contribution_trees_def\<close>)

lemma sides_le_side_rhs_fold_eff_enter:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes "(cl, fs, as) \<in> set ens"
  shows "sides_of_rhs (etf_enter etf fs as cl) \<sigma> (Inr gg)
         \<le> sides_of_rhs (side_rhs_fold_eff etf acc es ens cs) \<sigma> (Inr gg)"
  unfolding side_rhs_fold_eff_def
  by (rule sides_le_fold_rhs_trees) (use assms in \<open>force simp: side_contribution_trees_def\<close>)

lemma sides_le_side_rhs_fold_eff_combine:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes "(cc, dst, ex) \<in> set cs"
  shows "sides_of_rhs (etf_combine_collect etf dst cc ex) \<sigma> (Inr gg)
         \<le> sides_of_rhs (side_rhs_fold_eff etf acc es ens cs) \<sigma> (Inr gg)"
  unfolding side_rhs_fold_eff_def
  by (rule sides_le_fold_rhs_trees) (use assms in \<open>force simp: side_contribution_trees_def\<close>)


subsection \<open>Post-solution in usable form\<close>

lemma side_post_solution_le_local_eff:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g
  assumes "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) x \<sigma> vars"
      and "v \<in> vars"
  shows "side_acc_eff etf
           (if v = cfg_entry g then Lifted (bot0 \<squnion> restrict_local_for gs s0) else Bot)
           \<sigma> (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v) \<le> \<sigma> (Inl v)"
proof -
  from assms have "eq (side_cfg_T_eff gs g etf bot0 s0 gseed) v \<sigma> \<le> \<sigma> (Inl v)" by auto
  thus ?thesis by (simp add: eq_side_cfg_T_eff)
qed

text \<open>The fold's global contribution is below the packaged tree's (the entry Side
   wrapper only adds, at slot gseed).\<close>
lemma sides_fold_le_side_cfg_T_eff:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g
  shows "sides_of_rhs (side_rhs_fold_eff etf
           (if v = cfg_entry g then Lifted (bot0 \<squnion> restrict_local_for gs s0) else Bot)
           (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)) \<sigma> (Inr gg)
         \<le> sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed v) \<sigma> (Inr gg)"
  unfolding side_cfg_T_eff_def make_side_rhs_tree_eff_def Let_def
  by (cases "v = cfg_entry g") (auto simp: fun_upd_def Let_def)

lemma side_post_solution_le_global_eff:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g
  assumes pp: "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) x \<sigma> vars"
      and v: "v \<in> vars"
  shows "sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed v) \<sigma> (Inr gg) \<le> \<sigma> (Inr gg)"
proof -
  from pp v have "sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed v) \<sigma> \<le> \<sigma>" by auto
  thus ?thesis by (rule le_funD)
qed

subsection \<open>Edge / enter / combine closure of a post-solution\<close>

text \<open>
  Each closure bound additionally requires the edge/enter/combine tree to be
  \<^const>\<open>reachability_coherent_tree\<close> (see \<^theory>\<open>Voblint_Core.Constraint_System\<close>):
  without it a dead local Answer and a live Side of the same tree could
  recombine into a spuriously reachable \<^const>\<open>etf_full\<close> value.
  \<^const>\<open>unit_edge_tree\<close>/\<^const>\<open>local_edge_tree\<close>/\<^const>\<open>unit_combine_tree\<close> all
  discharge it (\<^theory>\<open>Voblint_Core.TD_Side_CFG\<close>'s
  \<open>reachability_coherent_unit_edge_tree\<close> and siblings), matching every concrete
  \<open>etf\<close> this codebase builds.
\<close>
lemma etf_combined_le_eff:
  fixes etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
    and gseed :: 'g
  assumes pp:  "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) x \<sigma> vars"
      and v:   "v \<in> vars"
      and e:   "(u, a, v) \<in> intra g"
      and fin: "finite (intra g)"
      and coh: "reachability_coherent_tree (apply_etf etf a u) \<sigma>"
  shows "etf_full (apply_etf etf a u) \<sigma> \<le> side_env_lift \<sigma> v"
proof -
  have mem: "(u, a) \<in> set (intra_predecessor_list g v)"
    using e by (simp add: set_intra_predecessor_list[OF fin] intra_predecessors_def)
  have loc: "traverse_rhs (apply_etf etf a u) \<sigma> \<le> \<sigma> (Inl v)"
    using side_acc_eff_edge_contributes[OF mem]
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
  show ?thesis
    unfolding side_env_lift_def
    by (rule etf_full_le_assemble_local_global[OF loc glob coh])
qed

lemma etf_enter_combined_le_eff:
  fixes etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
    and gseed :: 'g
  assumes pp:  "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) x \<sigma> vars"
      and v:   "v \<in> vars"
      and e:   "(cl, CallEdge dst fs as, v, k) \<in> calls g"
      and fin: "finite (calls g)"
      and coh: "reachability_coherent_tree (etf_enter etf fs as cl) \<sigma>"
  shows "etf_full (etf_enter etf fs as cl) \<sigma> \<le> side_env_lift \<sigma> v"
proof -
  have mem: "(cl, fs, as) \<in> set (entry_seed_list g v)"
    using fin e by (force simp: entry_seed_list_def entry_calls_def image_iff)
  have loc: "traverse_rhs (etf_enter etf fs as cl) \<sigma> \<le> \<sigma> (Inl v)"
    using side_acc_eff_enter_contributes[OF mem]
          side_post_solution_le_local_eff[OF pp v]
    by (rule order_trans)
  have glob_name: "\<And>gg. sides_of_rhs (etf_enter etf fs as cl) \<sigma> (Inr gg) \<le> \<sigma> (Inr gg)"
    using sides_le_side_rhs_fold_eff_enter[OF mem]
          sides_fold_le_side_cfg_T_eff
          side_post_solution_le_global_eff[OF pp v]
    by (meson order_trans)
  have glob: "all_sides (etf_enter etf fs as cl) \<sigma> \<le> glob_env \<sigma>"
  proof -
    have "all_sides (etf_enter etf fs as cl) \<sigma>
          \<le> glob_env (sides_of_rhs (etf_enter etf fs as cl) \<sigma>)"
      by (rule all_sides_le_glob_env_sides)
    also have "\<dots> \<le> glob_env \<sigma>" by (rule glob_env_mono_Inr) (rule glob_name)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding side_env_lift_def
    by (rule etf_full_le_assemble_local_global[OF loc glob coh])
qed

lemma etf_combine_combined_le_eff:
  fixes etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
    and gseed :: 'g
  assumes pp:   "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) x \<sigma> vars"
      and v:    "v \<in> vars"
      and e:    "(cc, ca, FunctionEntry p, v) \<in> calls g"
      and finC: "finite (calls g)"
      and coh:  "reachability_coherent_tree
                   (etf_combine_collect etf (call_info_of ca p) cc (FunctionResult p)) \<sigma>"
  shows "etf_full (etf_combine_collect etf (call_info_of ca p) cc (FunctionResult p)) \<sigma>
           \<le> side_env_lift \<sigma> v"
proof -
  have mem: "(cc, call_info_of ca p, FunctionResult p) \<in> set (return_call_list g v)"
    using e by (force simp: set_return_call_list[OF finC] return_calls_def)
  have loc: "traverse_rhs (etf_combine_collect etf (call_info_of ca p) cc (FunctionResult p)) \<sigma>
               \<le> \<sigma> (Inl v)"
    using side_acc_eff_combine_contributes[OF mem]
          side_post_solution_le_local_eff[OF pp v]
    by (rule order_trans)
  have glob_name: "\<And>gg. sides_of_rhs
      (etf_combine_collect etf (call_info_of ca p) cc (FunctionResult p)) \<sigma> (Inr gg) \<le> \<sigma> (Inr gg)"
    using sides_le_side_rhs_fold_eff_combine[OF mem]
          sides_fold_le_side_cfg_T_eff
          side_post_solution_le_global_eff[OF pp v]
    by (meson order_trans)
  have glob: "all_sides (etf_combine_collect etf (call_info_of ca p) cc (FunctionResult p)) \<sigma>
                \<le> glob_env \<sigma>"
  proof -
    have "all_sides (etf_combine_collect etf (call_info_of ca p) cc (FunctionResult p)) \<sigma>
          \<le> glob_env (sides_of_rhs
                (etf_combine_collect etf (call_info_of ca p) cc (FunctionResult p)) \<sigma>)"
      by (rule all_sides_le_glob_env_sides)
    also have "\<dots> \<le> glob_env \<sigma>" by (rule glob_env_mono_Inr) (rule glob_name)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding side_env_lift_def
    by (rule etf_full_le_assemble_local_global[OF loc glob coh])
qed

subsection \<open>Inr-slot local bot on least post-solutions\<close>

text \<open>
  Strip local components at Inr slots to @{const restrict_global_for}; locals are
  already bottom there.  A least post-solution is below every post-solution,
  hence below the stripped env, so its Inr locals stay bottom.
\<close>

lemma local_bot_on_locals_eq_restrict_global:
  fixes a :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "local_bot_on_locals gs a \<longleftrightarrow> a = restrict_global_for gs a"
  by (metis antisym dual_order.refl le_restrict_global_for_when_local_bot
      local_bot_on_locals_restrict_global restrict_local_for_global_join sup_ge2)

lemma local_bot_on_locals_lift_eq_restrict_global:
  fixes a :: "'a::sound_domain abs_state lifted"
  shows "local_bot_on_locals_lift gs a \<longleftrightarrow> a = map_lift (restrict_global_for gs) a"
  by (cases a) (simp_all add: local_bot_on_locals_eq_restrict_global)

lemma inr_slot_locals_bot_iff_local_bot_on_locals_lift:
  "inr_slot_locals_bot gs \<sigma> \<longleftrightarrow> (\<forall>g. local_bot_on_locals_lift gs (\<sigma> (Inr g)))"
  unfolding inr_slot_locals_bot_def local_bot_on_locals_lift_def local_bot_on_locals_def
  by (auto split: lifted.splits)

lemma inr_slot_locals_bot_iff_Inr_restrict_global:
  shows "inr_slot_locals_bot gs \<sigma> \<longleftrightarrow> (\<forall>g. \<sigma> (Inr g) = map_lift (restrict_global_for gs) (\<sigma> (Inr g)))"
  unfolding inr_slot_locals_bot_iff_local_bot_on_locals_lift
  using local_bot_on_locals_lift_eq_restrict_global by blast

definition strip_inr_globals ::
  "(vname => bool) => (pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state lifted)
   \<Rightarrow> pp + 'g \<Rightarrow> 'a abs_state lifted"
where
  "strip_inr_globals gs \<sigma> k =
     (case k of Inl p \<Rightarrow> \<sigma> (Inl p) | Inr g \<Rightarrow> map_lift (restrict_global_for gs) (\<sigma> (Inr g)))"

lemma strip_inr_globals_le:
  "strip_inr_globals gs \<sigma> \<le> \<sigma>"
  unfolding strip_inr_globals_def le_fun_def
  by (auto simp: map_lift_restrict_global_for_le split: sum.splits)

lemma strip_inr_globals_Inr:
  "strip_inr_globals gs \<sigma> (Inr g) = map_lift (restrict_global_for gs) (\<sigma> (Inr g))"
  unfolding strip_inr_globals_def by simp

lemma strip_inr_globals_Inl:
  "strip_inr_globals gs \<sigma> (Inl p) = \<sigma> (Inl p)"
  unfolding strip_inr_globals_def by simp

lemma sides_of_rhs_Side_Inr_local_bot:
  fixes \<sigma> :: "pp + 'g \<Rightarrow> 'a::sound_domain abs_state lifted"
    and g u :: 'g
    and t :: "(pp, 'g, 'a abs_state lifted) strategy_tree"
    and d :: "'a abs_state lifted"
  assumes lb_t: "local_bot_on_locals_lift gs (sides_of_rhs t \<sigma> (Inr u))"
  assumes lb_d: "local_bot_on_locals_lift gs d"
  shows "local_bot_on_locals_lift gs (sides_of_rhs (Side g d t) \<sigma> (Inr u))"
  unfolding sides_of_rhs.simps Let_def
  using local_bot_on_locals_lift_join[OF lb_d lb_t] lb_t
  by (auto simp: sup_commute)

lemma sides_side_rhs_fold_eff_Inr_local_bot:
  fixes etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
  assumes edge_inr:
    "\<And>a u \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (apply_etf etf a u) \<sigma>' (Inr g))"
  assumes enter_inr:
    "\<And>cl fs as \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (etf_enter etf fs as cl) \<sigma>' (Inr g))"
  assumes comb_inr:
    "\<And>cc dst ex \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (etf_combine_collect etf dst cc ex) \<sigma>' (Inr g))"
  shows "local_bot_on_locals_lift gs (sides_of_rhs (side_rhs_fold_eff etf acc ps ens cs) \<sigma> (Inr u))"
proof (induction ps arbitrary: acc ens cs)
  case Nil
  then show ?case
  proof (induction ens arbitrary: acc cs)
    case Nil
    then show ?case
    proof (induction cs arbitrary: acc)
      case Nil
      show ?case by simp
    next
      case (Cons ce cs)
      obtain cc dst ex where ce: "ce = (cc, dst, ex)" by (cases ce)
      have tree: "local_bot_on_locals_lift gs (sides_of_rhs (etf_combine_collect etf dst cc ex) \<sigma> (Inr u))"
        by (rule comb_inr)
      have rest: "local_bot_on_locals_lift gs
            (sides_of_rhs (side_rhs_fold_eff etf
               (acc \<squnion> traverse_rhs (etf_combine_collect etf dst cc ex) \<sigma>) [] [] cs) \<sigma> (Inr u))"
        by (rule Cons.IH)
      show ?case unfolding ce side_rhs_fold_eff_simps sides_of_rhs_seqcomp_at
        by (rule local_bot_on_locals_lift_join[OF tree rest])
    qed
  next
    case (Cons ee ens)
    obtain cl fs as where ee: "ee = (cl, fs, as)" by (cases ee)
    have tree: "local_bot_on_locals_lift gs (sides_of_rhs (etf_enter etf fs as cl) \<sigma> (Inr u))"
      by (rule enter_inr)
    have rest: "local_bot_on_locals_lift gs
          (sides_of_rhs (side_rhs_fold_eff etf
             (acc \<squnion> traverse_rhs (etf_enter etf fs as cl) \<sigma>) [] ens cs) \<sigma> (Inr u))"
      by (rule Cons.IH)
    show ?case unfolding ee side_rhs_fold_eff_simps sides_of_rhs_seqcomp_at
      by (rule local_bot_on_locals_lift_join[OF tree rest])
  qed
next
  case (Cons ea ps)
  obtain u' a where ea: "ea = (u', a)" by (cases ea)
  have tree: "local_bot_on_locals_lift gs (sides_of_rhs (apply_etf etf a u') \<sigma> (Inr u))"
    by (rule edge_inr)
  have rest: "local_bot_on_locals_lift gs
        (sides_of_rhs (side_rhs_fold_eff etf
           (acc \<squnion> traverse_rhs (apply_etf etf a u') \<sigma>) ps ens cs) \<sigma> (Inr u))"
    by (rule Cons.IH)
  show ?case unfolding ea side_rhs_fold_eff_simps sides_of_rhs_seqcomp_at
    by (rule local_bot_on_locals_lift_join[OF tree rest])
qed

lemma sides_make_side_rhs_tree_eff_Inr_local_bot:
  fixes etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
    and gseed :: 'g
  assumes edge_inr:
    "\<And>a u \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (apply_etf etf a u) \<sigma>' (Inr g))"
  assumes enter_inr:
    "\<And>cl fs as \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (etf_enter etf fs as cl) \<sigma>' (Inr g))"
  assumes comb_inr:
    "\<And>cc dst ex \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (etf_combine_collect etf dst cc ex) \<sigma>' (Inr g))"
  shows "local_bot_on_locals_lift gs (sides_of_rhs (make_side_rhs_tree_eff gs g etf bot0 s0 gseed v) \<sigma> (Inr u))"
proof -
  have fold_lb: "local_bot_on_locals_lift gs (sides_of_rhs (side_rhs_fold_eff etf acc' ps ens cs) \<sigma> (Inr u))"
    for acc' ps ens cs
    by (rule sides_side_rhs_fold_eff_Inr_local_bot[OF edge_inr enter_inr comb_inr])
  have d_lb: "local_bot_on_locals_lift gs (Lifted (restrict_global_for gs s0))"
    by (simp add: local_bot_on_locals_restrict_global)
  show ?thesis
  proof (cases "v = cfg_entry g")
    case True
    then show ?thesis
      unfolding make_side_rhs_tree_eff_def Let_def
      using sides_of_rhs_Side_Inr_local_bot[OF fold_lb d_lb]
      by simp
  next
    case False
    then show ?thesis
      unfolding make_side_rhs_tree_eff_def Let_def using fold_lb by simp
  qed
qed

lemma sides_side_cfg_T_eff_Inr_local_bot:
  fixes etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
    and gseed :: 'g
  assumes edge_inr:
    "\<And>a u \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (apply_etf etf a u) \<sigma>' (Inr g))"
  assumes enter_inr:
    "\<And>cl fs as \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (etf_enter etf fs as cl) \<sigma>' (Inr g))"
  assumes comb_inr:
    "\<And>cc dst ex \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (etf_combine_collect etf dst cc ex) \<sigma>' (Inr g))"
  shows "local_bot_on_locals_lift gs (sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed v) \<sigma> (Inr u))"
  unfolding side_cfg_T_eff_def
  by (rule sides_make_side_rhs_tree_eff_Inr_local_bot[OF edge_inr enter_inr comb_inr])

lemma part_post_solution_strip_inr_globals_eff:
  fixes etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
    and gseed :: 'g
  assumes pp: "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) x \<sigma> vars"
  assumes edge_inr:
    "\<And>a u \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (apply_etf etf a u) \<sigma>' (Inr g))"
  assumes enter_inr:
    "\<And>cl fs as \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (etf_enter etf fs as cl) \<sigma>' (Inr g))"
  assumes comb_inr:
    "\<And>cc dst ex \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (etf_combine_collect etf dst cc ex) \<sigma>' (Inr g))"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
  assumes comb_static: "\<And>cc dst ex. static_deps (etf_combine_collect etf dst cc ex)"
  assumes mono_eq: "is_mono_eq (side_cfg_T_eff gs g etf bot0 s0 gseed)"
  assumes mono_sides: "mono_sides (side_cfg_T_eff gs g etf bot0 s0 gseed)"
  shows "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) x (strip_inr_globals gs \<sigma>) vars"
proof -
  from pp obtain x_in: "x \<in> vars" and u_vars:
    "\<And>u. u \<in> vars \<Longrightarrow> dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> u \<subseteq> vars
      \<and> eq (side_cfg_T_eff gs g etf bot0 s0 gseed) u \<sigma> \<le> \<sigma> (Inl u)
      \<and> sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed u) \<sigma> \<le> \<sigma>"
    by auto
  show ?thesis
  proof (intro conjI ballI)
    show "x \<in> vars" by (rule x_in)
  next
    fix u assume u: "u \<in> vars"
    have dep: "dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> u \<subseteq> vars"
      using u_vars[OF u] by simp
    show "dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) (strip_inr_globals gs \<sigma>) u \<subseteq> vars"
    proof -
      have "dep (side_cfg_T_eff gs g etf bot0 s0 gseed) (strip_inr_globals gs \<sigma>) u
            = dep (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> u"
        unfolding dep_def side_cfg_T_eff_def
        by (simp add: dep_aux_make_side_rhs_tree_eff
             dep_aux_side_rhs_fold_eff_indep[OF edge_static enter_static comb_static])
      then show ?thesis unfolding dep\<^sub>L_def using dep
        by (simp add: dep\<^sub>L_def)
    qed

    have strip_le: "strip_inr_globals gs \<sigma> \<le> \<sigma>"
      by (rule strip_inr_globals_le)
    show "eq (side_cfg_T_eff gs g etf bot0 s0 gseed) u (strip_inr_globals gs \<sigma>)
          \<le> strip_inr_globals gs \<sigma> (Inl u)"
      by (metis (no_types, opaque_lifting) is_mono_eq_def mono_eq order.trans pp strip_inr_globals_Inl
          strip_le u)

    show "sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed u) (strip_inr_globals gs \<sigma>)
          \<le> strip_inr_globals gs \<sigma>"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed u) (strip_inr_globals gs \<sigma>) k
            \<le> strip_inr_globals gs \<sigma> k"
      proof (cases k)
        case (Inl p)
        have strip_le: "strip_inr_globals gs \<sigma> \<le> \<sigma>"
          by (rule strip_inr_globals_le)
        have sides_mono:
          "sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed u) (strip_inr_globals gs \<sigma>)
           \<le> sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed u) \<sigma>"
          using mono_sides strip_le unfolding mono_sides_def by blast
        have sides_le: "sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed u) \<sigma> (Inl p)
                       \<le> \<sigma> (Inl p)"
          using u_vars[OF u] by (simp add: le_funD)
        show ?thesis
          using sides_mono sides_le strip_inr_globals_Inl
          by (metis (no_types, lifting) Inl le_funE order_trans)
      next
        case (Inr g')
        have strip_le: "strip_inr_globals gs \<sigma> \<le> \<sigma>"
          by (rule strip_inr_globals_le)
        have sides_mono:
          "sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed u) (strip_inr_globals gs \<sigma>) (Inr g')
           \<le> sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed u) \<sigma> (Inr g')"
          using mono_sides strip_le unfolding mono_sides_def
          by (simp add: le_funD)
        have lb: "local_bot_on_locals_lift gs
              (sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed u) \<sigma> (Inr g'))"
          by (rule sides_side_cfg_T_eff_Inr_local_bot[OF edge_inr enter_inr comb_inr])
        have sides_le: "sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed u) \<sigma> (Inr g')
                       \<le> \<sigma> (Inr g')"
          using u_vars[OF u] by (simp add: le_funD)
        have bound: "sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed u) \<sigma> (Inr g')
                      \<le> map_lift (restrict_global_for gs) (\<sigma> (Inr g'))"
          by (rule le_map_lift_restrict_global_for_when_local_bot_lift[OF lb sides_le])
        show ?thesis
          using sides_mono bound strip_inr_globals_Inr
          by (metis (no_types, lifting) Inr le_funE order_trans)
      qed
    qed
  qed
qed

lemma inr_slot_locals_bot_strip:
  "inr_slot_locals_bot gs (strip_inr_globals gs \<sigma>)"
  unfolding inr_slot_locals_bot_iff_Inr_restrict_global strip_inr_globals_Inr
  by simp

lemma least_part_post_solution_inr_slot_locals_bot_eff:
  fixes etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
    and gseed :: 'g
  assumes least: "least_part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) x \<sigma> vars"
  assumes edge_inr:
    "\<And>a u \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (apply_etf etf a u) \<sigma>' (Inr g))"
  assumes enter_inr:
    "\<And>cl fs as \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (etf_enter etf fs as cl) \<sigma>' (Inr g))"
  assumes comb_inr:
    "\<And>cc dst ex \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (etf_combine_collect etf dst cc ex) \<sigma>' (Inr g))"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
  assumes comb_static: "\<And>cc dst ex. static_deps (etf_combine_collect etf dst cc ex)"
  assumes mono_eq: "is_mono_eq (side_cfg_T_eff gs g etf bot0 s0 gseed)"
  assumes mono_sides: "mono_sides (side_cfg_T_eff gs g etf bot0 s0 gseed)"
  shows "inr_slot_locals_bot gs \<sigma>"
proof -
  from least have pp: "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) x \<sigma> vars"
      and min: "\<And>\<sigma>'. part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) x \<sigma>' vars
                 \<Longrightarrow> \<sigma> \<le> \<sigma>'"
    by auto

  have strip_pp: "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) x (strip_inr_globals gs \<sigma>) vars"
    by (rule part_post_solution_strip_inr_globals_eff[OF pp edge_inr enter_inr comb_inr
          edge_static enter_static comb_static mono_eq mono_sides])
  have strip_le: "strip_inr_globals gs \<sigma> \<le> \<sigma>"
    by (rule strip_inr_globals_le)
  have \<sigma>_le_strip: "\<sigma> \<le> strip_inr_globals gs \<sigma>"
    using min[OF strip_pp] .
  show ?thesis
    unfolding inr_slot_locals_bot_iff_Inr_restrict_global
  proof (intro allI)
    fix g
    have "\<sigma> (Inr g) = strip_inr_globals gs \<sigma> (Inr g)"
      using \<sigma>_le_strip strip_le by (simp add: le_antisym le_funD)
    also have "\<dots> = map_lift (restrict_global_for gs) (\<sigma> (Inr g))"
      by (simp add: strip_inr_globals_Inr)
    finally show "\<sigma> (Inr g) = map_lift (restrict_global_for gs) (\<sigma> (Inr g))" .
  qed
qed

end
