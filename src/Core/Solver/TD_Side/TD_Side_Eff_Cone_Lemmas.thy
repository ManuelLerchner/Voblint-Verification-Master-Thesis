theory TD_Side_Eff_Cone_Lemmas
  imports TD_Side_RHS_Generator "Voblint_CFG.CFG_Prune"
begin

section \<open>Dependency and cone lemmas for the effectful side IP solver (pruning)\<close>

text \<open>
  Standalone effectful IP collecting soundness with pruning, built on
  @{const side_cfg_T_eff}.  The dependency cone, exit pruning and entry seeding are
  re-established for the effectful equation system; the per-source post-fixpoint
  bounds come from TD_Side_Eff_Bounds and the collecting step from
  post_fixpoint_sound_at_eff.

  The three effectful contribution lists (intra, entry, combine) induce three
  static dependency shapes, matched by the three structural sources of
  @{const cfg_succ_rel}:

    * an edge tree queries its own source local (INTRA);
    * an entry tree queries the call site local (ENTRY);
    * a combine tree queries its caller and callee-result locals (COMB_CALLER,
      COMB_RESULT).

  Static dependencies (the queried-unknown skeleton does not depend on the
  environment) are already required for the TD_side mono_deps precondition.
\<close>

subsection \<open>Dependency membership for the effectful fold\<close>

text \<open>dep_aux of the fold is acc-independent when the per-tree query skeletons are static.\<close>

lemma dep_aux_side_rhs_fold_eff_acc_indep:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
      and comb_static: "\<And>cc dst ex. static_deps (etf_combine etf dst cc ex)"
  shows "dep_aux \<sigma> (side_rhs_fold_eff etf acc1 es ens cs)
       = dep_aux \<sigma> (side_rhs_fold_eff etf acc2 es ens cs)"
  by (rule dep_aux_side_rhs_fold_eff_indep[OF edge_static enter_static comb_static])

text \<open>The source local of an edge in the intra list is a dependency of the fold.\<close>

lemma Inl_dep_aux_side_rhs_fold_eff_edge:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes edge_dep: "\<And>b w \<sigma>'. Inl w \<in> dep_aux \<sigma>' (apply_etf etf b w)"
  assumes mem: "(u, a) \<in> set es"
  shows "Inl u \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc es ens cs)"
  using mem
proof (induction es arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x es)
  obtain w b where x: "x = (w, b)" by (cases x)
  show ?case
  proof (cases "(w, b) = (u, a)")
    case True
    have "Inl w \<in> dep_aux \<sigma> (apply_etf etf b w)" by (rule edge_dep)
    then have "Inl u \<in> dep_aux \<sigma> (apply_etf etf b w)" using True by simp
    thus ?thesis unfolding x side_rhs_fold_eff_simps dep_aux_seqcomp by simp
  next
    case False
    have mem': "(u, a) \<in> set es" using Cons.prems x False by auto
    have "Inl u \<in> dep_aux \<sigma> (side_rhs_fold_eff etf
            (acc \<squnion> traverse_rhs (apply_etf etf b w) \<sigma>) es ens cs)"
      by (rule Cons.IH[OF mem'])
    thus ?thesis unfolding x side_rhs_fold_eff_simps dep_aux_seqcomp by simp
  qed
qed

text \<open>Prepending edge or entry contributions preserves dependencies of the remaining fold.\<close>

lemma dep_aux_side_rhs_fold_eff_sub_es:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
      and comb_static: "\<And>cc dst ex. static_deps (etf_combine etf dst cc ex)"
  shows "dep_aux \<sigma> (side_rhs_fold_eff etf acc [] ens cs)
       \<subseteq> dep_aux \<sigma> (side_rhs_fold_eff etf acc es ens cs)"
proof (induction es arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x es)
  obtain w b where x: "x = (w, b)" by (cases x)
  let ?acc' = "acc \<squnion> traverse_rhs (apply_etf etf b w) \<sigma>"
  have "dep_aux \<sigma> (side_rhs_fold_eff etf acc [] ens cs)
        = dep_aux \<sigma> (side_rhs_fold_eff etf ?acc' [] ens cs)"
    by (rule dep_aux_side_rhs_fold_eff_acc_indep[OF edge_static enter_static comb_static])
  also have "... \<subseteq> dep_aux \<sigma> (side_rhs_fold_eff etf ?acc' es ens cs)"
    by (rule Cons.IH)
  also have "... \<subseteq> dep_aux \<sigma> (side_rhs_fold_eff etf acc (x # es) ens cs)"
    unfolding x side_rhs_fold_eff_simps dep_aux_seqcomp by auto
  finally show ?case .
qed

lemma dep_aux_side_rhs_fold_eff_sub_ens:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
      and comb_static: "\<And>cc dst ex. static_deps (etf_combine etf dst cc ex)"
  shows "dep_aux \<sigma> (side_rhs_fold_eff etf acc [] [] cs)
       \<subseteq> dep_aux \<sigma> (side_rhs_fold_eff etf acc [] ens cs)"
proof (induction ens arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x ens)
  obtain cl fs as where x: "x = (cl, fs, as)" by (cases x)
  let ?acc' = "acc \<squnion> traverse_rhs (etf_enter etf fs as cl) \<sigma>"
  have "dep_aux \<sigma> (side_rhs_fold_eff etf acc [] [] cs)
        = dep_aux \<sigma> (side_rhs_fold_eff etf ?acc' [] [] cs)"
    by (rule dep_aux_side_rhs_fold_eff_acc_indep[OF edge_static enter_static comb_static])
  also have "... \<subseteq> dep_aux \<sigma> (side_rhs_fold_eff etf ?acc' [] ens cs)"
    by (rule Cons.IH)
  also have "... \<subseteq> dep_aux \<sigma> (side_rhs_fold_eff etf acc [] (x # ens) cs)"
    unfolding x side_rhs_fold_eff_simps dep_aux_seqcomp by auto
  finally show ?case .
qed

text \<open>The call site is queried by the entry contribution.\<close>

lemma Inl_dep_aux_side_rhs_fold_eff_enter_esnil:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes enter_dep: "\<And>c2 f2 a2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_enter etf f2 a2 c2)"
  assumes mem: "(cl, fs, as) \<in> set ens"
  shows "Inl cl \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc [] ens cs)"
  using mem
proof (induction ens arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x ens)
  obtain c2 f2 a2 where x: "x = (c2, f2, a2)" by (cases x)
  show ?case
  proof (cases "(c2, f2, a2) = (cl, fs, as)")
    case True
    have "Inl c2 \<in> dep_aux \<sigma> (etf_enter etf f2 a2 c2)" by (rule enter_dep)
    then have "Inl cl \<in> dep_aux \<sigma> (etf_enter etf f2 a2 c2)" using True by simp
    thus ?thesis unfolding x side_rhs_fold_eff_simps dep_aux_seqcomp by simp
  next
    case False
    have mem': "(cl, fs, as) \<in> set ens" using Cons.prems x False by auto
    have "Inl cl \<in> dep_aux \<sigma> (side_rhs_fold_eff etf
            (acc \<squnion> traverse_rhs (etf_enter etf f2 a2 c2) \<sigma>) [] ens cs)"
      by (rule Cons.IH[OF mem'])
    thus ?thesis unfolding x side_rhs_fold_eff_simps dep_aux_seqcomp by simp
  qed
qed

lemma Inl_dep_aux_side_rhs_fold_eff_enter:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes enter_dep: "\<And>c2 f2 a2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_enter etf f2 a2 c2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
      and comb_static: "\<And>cc dst ex. static_deps (etf_combine etf dst cc ex)"
  assumes mem: "(cl, fs, as) \<in> set ens"
  shows "Inl cl \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc es ens cs)"
  using Inl_dep_aux_side_rhs_fold_eff_enter_esnil[OF enter_dep mem]
        dep_aux_side_rhs_fold_eff_sub_es[OF edge_static enter_static comb_static]
  by blast

text \<open>The caller and callee-result locals are queried by the combine contribution.\<close>

lemma Inl_dep_aux_side_rhs_fold_eff_call_nilnil:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes comb_dep: "\<And>c2 e2 d2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes mem: "(cc, dst, ex) \<in> set cs"
  shows "Inl cc \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc [] [] cs)"
  using mem
proof (induction cs arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x cs)
  obtain c2 d2 e2 where x: "x = (c2, d2, e2)" by (cases x)
  show ?case
  proof (cases "(c2, d2, e2) = (cc, dst, ex)")
    case True
    have "Inl c2 \<in> dep_aux \<sigma> (etf_combine etf d2 c2 e2)" by (rule comb_dep)
    then have "Inl cc \<in> dep_aux \<sigma> (etf_combine etf d2 c2 e2)" using True by simp
    thus ?thesis unfolding x side_rhs_fold_eff_simps dep_aux_seqcomp by simp
  next
    case False
    have mem': "(cc, dst, ex) \<in> set cs" using Cons.prems x False by auto
    have "Inl cc \<in> dep_aux \<sigma> (side_rhs_fold_eff etf
            (acc \<squnion> traverse_rhs (etf_combine etf d2 c2 e2) \<sigma>) [] [] cs)"
      by (rule Cons.IH[OF mem'])
    thus ?thesis unfolding x side_rhs_fold_eff_simps dep_aux_seqcomp by simp
  qed
qed

lemma Inl_dep_aux_side_rhs_fold_eff_exit_nilnil:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes comb_dep: "\<And>c2 e2 d2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes mem: "(cc, dst, ex) \<in> set cs"
  shows "Inl ex \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc [] [] cs)"
  using mem
proof (induction cs arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x cs)
  obtain c2 d2 e2 where x: "x = (c2, d2, e2)" by (cases x)
  show ?case
  proof (cases "(c2, d2, e2) = (cc, dst, ex)")
    case True
    have "Inl e2 \<in> dep_aux \<sigma> (etf_combine etf d2 c2 e2)" by (rule comb_dep)
    then have "Inl ex \<in> dep_aux \<sigma> (etf_combine etf d2 c2 e2)" using True by simp
    thus ?thesis unfolding x side_rhs_fold_eff_simps dep_aux_seqcomp by simp
  next
    case False
    have mem': "(cc, dst, ex) \<in> set cs" using Cons.prems x False by auto
    have "Inl ex \<in> dep_aux \<sigma> (side_rhs_fold_eff etf
            (acc \<squnion> traverse_rhs (etf_combine etf d2 c2 e2) \<sigma>) [] [] cs)"
      by (rule Cons.IH[OF mem'])
    thus ?thesis unfolding x side_rhs_fold_eff_simps dep_aux_seqcomp by simp
  qed
qed

lemma Inl_dep_aux_side_rhs_fold_eff_call:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes comb_dep: "\<And>c2 e2 d2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
      and comb_static: "\<And>cc dst ex. static_deps (etf_combine etf dst cc ex)"
  assumes mem: "(cc, dst, ex) \<in> set cs"
  shows "Inl cc \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc es ens cs)"
  using Inl_dep_aux_side_rhs_fold_eff_call_nilnil[OF comb_dep mem]
        dep_aux_side_rhs_fold_eff_sub_ens[OF edge_static enter_static comb_static]
        dep_aux_side_rhs_fold_eff_sub_es[OF edge_static enter_static comb_static]
  by blast

lemma Inl_dep_aux_side_rhs_fold_eff_exit:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes comb_dep: "\<And>c2 e2 d2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
      and comb_static: "\<And>cc dst ex. static_deps (etf_combine etf dst cc ex)"
  assumes mem: "(cc, dst, ex) \<in> set cs"
  shows "Inl ex \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc es ens cs)"
  using Inl_dep_aux_side_rhs_fold_eff_exit_nilnil[OF comb_dep mem]
        dep_aux_side_rhs_fold_eff_sub_ens[OF edge_static enter_static comb_static]
        dep_aux_side_rhs_fold_eff_sub_es[OF edge_static enter_static comb_static]
  by blast

subsection \<open>Dependency at the eqsT level (intra, entry, combine endpoints)\<close>

lemma dep_side_rhs_tree_eff_edge:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g and gs :: "vname => bool"
  assumes fin: "finite (intra g)"
  assumes ed: "(u, a, w) \<in> intra g"
  assumes edge_dep: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  shows "u \<in> dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> w"
proof -
  have mem: "(u, a) \<in> set (intra_predecessor_list g w)"
    using ed by (simp add: set_intra_predecessor_list[OF fin] intra_predecessors_def)
  have "Inl u \<in> dep_aux \<sigma> (make_side_rhs_tree_eff gs g etf bot0 s0 gseed w)"
    unfolding dep_aux_make_side_rhs_tree_eff
    by (rule Inl_dep_aux_side_rhs_fold_eff_edge[OF edge_dep mem])
  thus ?thesis unfolding side_cfg_T_eff_def dep\<^sub>L_def dep_def by simp
qed

lemma dep_side_rhs_tree_eff_enter:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g and gs :: "vname => bool"
  assumes finC: "finite (calls g)"
  assumes call: "(cl, CallEdge dst fs as, ce, k) \<in> calls g"
  assumes enter_dep: "\<And>c2 f2 a2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_enter etf f2 a2 c2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and enter_static: "\<And>c2 fs as. static_deps (etf_enter etf fs as c2)"
      and comb_static: "\<And>cc dst ex. static_deps (etf_combine etf dst cc ex)"
  shows "cl \<in> dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> ce"
proof -
  have mem: "(cl, fs, as) \<in> set (entry_seed_list g ce)"
    using finC call by (force simp: entry_seed_list_def entry_calls_def image_iff)
  have "Inl cl \<in> dep_aux \<sigma> (make_side_rhs_tree_eff gs g etf bot0 s0 gseed ce)"
    unfolding dep_aux_make_side_rhs_tree_eff
    by (rule Inl_dep_aux_side_rhs_fold_eff_enter[OF enter_dep edge_static enter_static comb_static mem])
  thus ?thesis unfolding side_cfg_T_eff_def dep\<^sub>L_def dep_def by simp
qed

lemma dep_side_rhs_tree_eff_combine:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g and gs :: "vname => bool"
  assumes finC: "finite (calls g)"
  assumes call: "(cl, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
  assumes comb_dep1: "\<And>c2 e2 d2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 d2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and enter_static: "\<And>c2 fs as. static_deps (etf_enter etf fs as c2)"
      and comb_static: "\<And>cc dst ex. static_deps (etf_combine etf dst cc ex)"
  shows "cl \<in> dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> k
       \<and> FunctionResult p \<in> dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> k"
proof -
  have mem: "(cl, dst, FunctionResult p) \<in> set (return_call_list g k)"
    using call by (force simp: set_return_call_list[OF finC] return_calls_def)
  have dc: "Inl cl \<in> dep_aux \<sigma> (make_side_rhs_tree_eff gs g etf bot0 s0 gseed k)"
    unfolding dep_aux_make_side_rhs_tree_eff
    by (rule Inl_dep_aux_side_rhs_fold_eff_call[OF comb_dep1 edge_static enter_static comb_static mem])
  have de: "Inl (FunctionResult p) \<in> dep_aux \<sigma> (make_side_rhs_tree_eff gs g etf bot0 s0 gseed k)"
    unfolding dep_aux_make_side_rhs_tree_eff
    by (rule Inl_dep_aux_side_rhs_fold_eff_exit[OF comb_dep2 edge_static enter_static comb_static mem])
  show ?thesis using dc de unfolding side_cfg_T_eff_def dep\<^sub>L_def dep_def by simp
qed

subsection \<open>Backward IP reachability lands in the effectful solver's dependency cone\<close>

lemma cfg_reaches_imp_trans_dep_or_eq_side_eff:
  fixes g :: cfg and etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state" and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state" and gseed :: 'g and gs :: "vname => bool"
  assumes fin: "finite (intra g)"
  assumes finC: "finite (calls g)"
  assumes wf: "wf_cfg g"
  assumes edge_dep: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  assumes enter_dep: "\<And>c2 f2 a2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_enter etf f2 a2 c2)"
  assumes comb_dep1: "\<And>c2 e2 d2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 d2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
  assumes comb_static: "\<And>cc dst ex. static_deps (etf_combine etf dst cc ex)"
  assumes reach: "cfg_reaches g w v0"
  shows "w = v0 \<or> w \<in> trans_dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> v0"
proof -
  from reach have "(w, v0) \<in> (cfg_succ_rel g)\<^sup>*" unfolding cfg_reaches_def .
  thus ?thesis
  proof (induction rule: converse_rtrancl_induct)
    case base
    show ?case by simp
  next
    case (step y z)
    have su: "(y, z) \<in> cfg_succ_rel g" using step.hyps(1) .
    have ydep: "y \<in> dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> z"
      using su
    proof (cases rule: cfg_succ_rel_cases)
      case (INTRA a)
      show ?thesis by (rule dep_side_rhs_tree_eff_edge[OF fin INTRA edge_dep])
    next
      case (ENTRY ca k)
      obtain dst fs as where ca: "ca = CallEdge dst fs as" by (cases ca)
      show ?thesis
        by (rule dep_side_rhs_tree_eff_enter[OF finC ENTRY[unfolded ca] enter_dep
              edge_static enter_static comb_static])
    next
      case (COMB_CALLER ca ce)
      obtain p where ce: "ce = FunctionEntry p"
        using wf COMB_CALLER unfolding wf_cfg_def by blast
      obtain dst fs as where ca: "ca = CallEdge dst fs as" by (cases ca)
      have "(y, CallEdge dst fs as, FunctionEntry p, z) \<in> calls g"
        using COMB_CALLER ca ce by simp
      then show ?thesis
        using dep_side_rhs_tree_eff_combine[OF finC _ comb_dep1 comb_dep2
              edge_static enter_static comb_static] by blast
    next
      case (COMB_RESULT cl ca p k)
      obtain dst fs as where ca: "ca = CallEdge dst fs as" by (cases ca)
      have "(cl, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
        using COMB_RESULT ca by simp
      then have "FunctionResult p \<in> dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> k"
        using dep_side_rhs_tree_eff_combine[OF finC _ comb_dep1 comb_dep2
              edge_static enter_static comb_static] by blast
      then show ?thesis using COMB_RESULT by simp
    qed
    show ?case
    proof (cases "z = v0")
      case True
      show ?thesis using ydep True trans_dep\<^sub>L_step_in by blast
    next
      case False
      have z_in: "z \<in> trans_dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> v0"
        using step.IH False by blast
      have "y \<in> trans_dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> v0"
        by (metis Nitpick.tranclp_unfold mem_Collect_eq
              tranclp.trancl_into_trancl ydep z_in)
      thus ?thesis by blast
    qed
  qed
qed

lemma side_cone_in_vars_eff:
  fixes g :: cfg and etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state" and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state" and gseed :: 'g and gs :: "vname => bool"
  assumes pp: "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) v0 \<sigma> vars"
  assumes fin: "finite (intra g)"
  assumes finC: "finite (calls g)"
  assumes wf: "wf_cfg g"
  assumes edge_dep: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  assumes enter_dep: "\<And>c2 f2 a2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_enter etf f2 a2 c2)"
  assumes comb_dep1: "\<And>c2 e2 d2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 d2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
  assumes comb_static: "\<And>cc dst ex. static_deps (etf_combine etf dst cc ex)"
  assumes reach: "cfg_reaches g w v0"
  shows "w \<in> vars"
proof -
  have v0v: "v0 \<in> vars" using pp by auto
  consider (eq) "w = v0"
    | (td) "w \<in> trans_dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> v0"
    using cfg_reaches_imp_trans_dep_or_eq_side_eff[OF fin finC wf edge_dep enter_dep
            comb_dep1 comb_dep2 edge_static enter_static comb_static reach] by blast
  thus ?thesis
  proof cases
    case eq thus ?thesis using v0v by simp
  next
    case td
    have "trans_dep\<^sub>L (side_cfg_T_eff gs g etf bot0 s0 gseed) \<sigma> v0 \<subseteq> vars"
      using part_post_solution_implies_trans_dep_subsumed[OF pp] by simp
    thus ?thesis using td by blast
  qed
qed

corollary side_cone_in_vars_eff_cone:
  fixes g :: cfg and etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state" and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state" and gseed :: 'g and gs :: "vname => bool"
  assumes pp:   "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) v0 \<sigma> vars"
  assumes fin:  "finite (intra g)"
  assumes finC: "finite (calls g)"
  assumes wf:   "wf_cfg g"
  assumes cone: "cone_compatible_etf gs etf"
  assumes reach: "cfg_reaches g w v0"
  shows "w \<in> vars"
  by (rule side_cone_in_vars_eff[OF pp fin finC wf
        cone_compatible_etf_edge_dep[OF cone]
        cone_compatible_etf_enter_dep[OF cone]
        cone_compatible_etf_comb_dep1[OF cone]
        cone_compatible_etf_comb_dep2[OF cone]
        cone_compatible_etf_edge_static[OF cone]
        cone_compatible_etf_enter_static[OF cone]
        cone_compatible_etf_comb_static[OF cone]
        reach])

subsection \<open>Entry coverage from an arbitrary initial state\<close>

text \<open>
  The entry node's wrapping Side gseed contributes restrict_global_for gs s0 to the
  designated named-global slot gseed, so the initial globals are below it in any
  post-solution.
\<close>

lemma restrict_global_s0_le_global_eff:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g and gs :: "vname => bool"
  assumes pp: "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) x \<sigma> vars"
      and entry_in: "cfg_entry g \<in> vars"
  shows "restrict_global_for gs s0 \<le> \<sigma> (Inr gseed)"
proof -
  from pp entry_in
  have "sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed (cfg_entry g)) \<sigma> \<le> \<sigma>" by auto
  hence le: "sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed (cfg_entry g)) \<sigma> (Inr gseed)
             \<le> \<sigma> (Inr gseed)"
    by (simp add: le_fun_def)
  have e: "sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed (cfg_entry g)) \<sigma> (Inr gseed)
           = sides_of_rhs (side_rhs_fold_eff etf (bot0 \<squnion> restrict_local_for gs s0)
                (intra_predecessor_list g (cfg_entry g))
                (entry_seed_list g (cfg_entry g))
                (return_call_list g (cfg_entry g))) \<sigma> (Inr gseed)
             \<squnion> restrict_global_for gs s0"
    unfolding side_cfg_T_eff_def make_side_rhs_tree_eff_def
    by (simp add: Let_def)
  have "restrict_global_for gs s0
        \<le> sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed (cfg_entry g)) \<sigma> (Inr gseed)"
    unfolding e by (rule sup_ge2)
  thus ?thesis using le by (rule order_trans)
qed

text \<open>
  At the entry point the local fold seeds restrict_local_for gs s0 and the wrapping
  Side gseed seeds restrict_global_for gs s0 into slot gseed (below glob_env), so s0
  itself is below the combined env at the entry -- for an arbitrary initial state.
\<close>
lemma s0_le_side_env_entry_eff:
  fixes etf :: "('g::finite, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g and gs :: "vname => bool"
  assumes pp: "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) v0 \<sigma> vars"
  assumes entry_in: "cfg_entry g \<in> vars"
  shows "s0 \<le> side_env \<sigma> (cfg_entry g)"
proof -
  have acc_le: "side_acc_eff etf (bot0 \<squnion> restrict_local_for gs s0) \<sigma>
                  (intra_predecessor_list g (cfg_entry g))
                  (entry_seed_list g (cfg_entry g))
                  (return_call_list g (cfg_entry g))
                \<le> \<sigma> (Inl (cfg_entry g))"
    using side_post_solution_le_local_eff[OF pp entry_in] by simp
  have "restrict_local_for gs s0 \<le> bot0 \<squnion> restrict_local_for gs s0" by simp
  also have "... \<le> side_acc_eff etf (bot0 \<squnion> restrict_local_for gs s0) \<sigma>
                     (intra_predecessor_list g (cfg_entry g))
                     (entry_seed_list g (cfg_entry g))
                     (return_call_list g (cfg_entry g))"
    by (rule acc_le_side_acc_eff)
  also have "... \<le> \<sigma> (Inl (cfg_entry g))" by (rule acc_le)
  finally have rl: "restrict_local_for gs s0 \<le> \<sigma> (Inl (cfg_entry g))" .
  have rg: "restrict_global_for gs s0 \<le> \<sigma> (Inr gseed)"
    by (rule restrict_global_s0_le_global_eff[OF pp entry_in])
  have "s0 = restrict_local_for gs s0 \<squnion> restrict_global_for gs s0"
    by (rule restrict_local_for_global_join[symmetric])
  also have "... \<le> \<sigma> (Inl (cfg_entry g)) \<squnion> \<sigma> (Inr gseed)"
    using rl rg by (rule sup_mono)
  also have "... \<le> \<sigma> (Inl (cfg_entry g)) \<squnion> glob_env \<sigma>"
    by (rule sup_mono[OF order_refl glob_env_upper])
  finally show ?thesis unfolding side_env_def .
qed

subsection \<open>Unit-global effectful record contracts\<close>

text \<open>
  Unit-global records have fixed QueryL/QueryG skeletons for edge, enter and combine
  trees.  The solver-side cone and monotonicity contracts follow from that tree
  shape and monotonicity of the edge / enter transformers.
\<close>

lemma cone_compatible_etf_unit_transfer:
  fixes etf :: "(unit, 'a::sound_domain) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and Fe :: "vname list \<Rightarrow> aexp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and gs :: "vname \<Rightarrow> bool"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree gs (F a) u"
  assumes enter: "\<And>cl fs as. etf_enter etf fs as cl = unit_edge_tree gs (Fe fs as) cl"
  assumes comb: "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree gs dst cc ex"
  shows "cone_compatible_etf gs etf"
proof -
  interpret mixed_rhs_generator gs etf F Fe
    by (unfold_locales; simp add: edge enter comb)
  show ?thesis by (rule cone_compatible)
qed

lemma threefold_mono_unit_transfer:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and Fe :: "vname list \<Rightarrow> aexp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and g :: cfg and bot0 s0 :: "'a abs_state" and gs :: "vname => bool"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree gs (F a) u"
  assumes enter: "\<And>cl fs as. etf_enter etf fs as cl = unit_edge_tree gs (Fe fs as) cl"
  assumes comb: "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree gs dst cc ex"
  assumes mono: "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2"
  assumes mono_e: "\<And>fs as s1 s2. s1 \<le> s2 \<Longrightarrow> Fe fs as s1 \<le> Fe fs as s2"
  shows "threefold_mono (side_cfg_T_eff gs g etf bot0 s0 ())"
proof -
  interpret mixed_rhs_generator_mono gs etf F Fe
  proof unfold_locales
    show "\<And>a u. apply_etf etf a u = local_edge_tree gs (F a) u
                \<or> apply_etf etf a u = unit_edge_tree gs (F a) u" by (simp add: edge)
    show "\<And>cl fs as. etf_enter etf fs as cl = unit_edge_tree gs (Fe fs as) cl" by (rule enter)
    show "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree gs dst cc ex" by (rule comb)
    show "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2" by (rule mono)
    show "\<And>fs as s1 s2. s1 \<le> s2 \<Longrightarrow> Fe fs as s1 \<le> Fe fs as s2" by (rule mono_e)
  qed
  show ?thesis by (rule threefold_mono)
qed

lemma cone_compatible_etf_local_unit_transfer:
  fixes etf :: "(unit, 'a::sound_domain) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and Fe :: "vname list \<Rightarrow> aexp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and gs :: "vname \<Rightarrow> bool"
  assumes edge: "\<And>a u. apply_etf etf a u =
    (if local_edge_action gs a then local_edge_tree gs (F a) u
     else unit_edge_tree gs (F a) u)"
  assumes enter: "\<And>cl fs as. etf_enter etf fs as cl = unit_edge_tree gs (Fe fs as) cl"
  assumes comb: "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree gs dst cc ex"
  shows "cone_compatible_etf gs etf"
proof -
  interpret mixed_rhs_generator gs etf F Fe
    by (unfold_locales; simp add: edge enter comb)
  show ?thesis by (rule cone_compatible)
qed

lemma threefold_mono_local_unit_transfer:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and Fe :: "vname list \<Rightarrow> aexp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and g :: cfg and bot0 s0 :: "'a abs_state" and gs :: "vname => bool"
  assumes edge: "\<And>a u. apply_etf etf a u =
    (if local_edge_action gs a then local_edge_tree gs (F a) u
     else unit_edge_tree gs (F a) u)"
  assumes enter: "\<And>cl fs as. etf_enter etf fs as cl = unit_edge_tree gs (Fe fs as) cl"
  assumes comb: "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree gs dst cc ex"
  assumes mono: "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2"
  assumes mono_e: "\<And>fs as s1 s2. s1 \<le> s2 \<Longrightarrow> Fe fs as s1 \<le> Fe fs as s2"
  shows "threefold_mono (side_cfg_T_eff gs g etf bot0 s0 ())"
proof -
  interpret mixed_rhs_generator_mono gs etf F Fe
  proof unfold_locales
    show "\<And>a u. apply_etf etf a u = local_edge_tree gs (F a) u
                \<or> apply_etf etf a u = unit_edge_tree gs (F a) u" by (simp add: edge)
    show "\<And>cl fs as. etf_enter etf fs as cl = unit_edge_tree gs (Fe fs as) cl" by (rule enter)
    show "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree gs dst cc ex" by (rule comb)
    show "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2" by (rule mono)
    show "\<And>fs as s1 s2. s1 \<le> s2 \<Longrightarrow> Fe fs as s1 \<le> Fe fs as s2" by (rule mono_e)
  qed
  show ?thesis by (rule threefold_mono)
qed

end
