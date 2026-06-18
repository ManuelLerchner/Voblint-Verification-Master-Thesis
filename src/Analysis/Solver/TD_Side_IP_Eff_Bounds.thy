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

end
