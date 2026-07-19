theory TD_Side_Eff_Cone_Lemmas
  imports TD_Side_RHS_Generator "Voblint_CFG.CFG_Prune"
begin

section \<open>Dependency and cone lemmas for the effectful side IP solver (pruning)\<close>

text \<open>
  Standalone effectful IP collecting soundness with pruning, built on
  @{const side_cfg_T_eff}.  The dependency cone, exit pruning and entry seeding are re-established for the
  effectful equation system; the per-edge / per-combine post-fixpoint bounds come
  from TD_Side_Eff_Bounds and the collecting step from
  post_fixpoint_sound_at_eff.

  The cone needs two structural facts about each per-tree, supplied as hypotheses
  or discharged from the analysis record construction:

    * a query contract -- the per-edge tree queries its own source local and the
      combine tree queries its call and exit locals (edge / combine dependency
      membership);
    * static dependencies -- the queried-unknown skeleton does not depend on the
      environment (already required for the TD_side mono_deps precondition).
\<close>



subsection \<open>Dependency membership for the effectful fold\<close>

text \<open>dep_aux of the fold is acc-independent when the per-tree skeletons are static.\<close>

lemma dep_aux_side_rhs_fold_eff_acc_indep:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and comb_static: "\<And>cc ex dst. static_deps (etf_combine etf dst cc ex)"
  shows "dep_aux \<sigma> (side_rhs_fold_eff etf acc1 es cs)
       = dep_aux \<sigma> (side_rhs_fold_eff etf acc2 es cs)"
  by (rule dep_aux_side_rhs_fold_eff_indep[OF edge_static comb_static])

text \<open>The source local of an edge in the list is a dependency of the fold.\<close>

lemma Inl_dep_aux_side_rhs_fold_eff_edge:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes edge_dep: "\<And>b w \<sigma>'. Inl w \<in> dep_aux \<sigma>' (apply_etf etf b w)"
  assumes mem: "(u, a) \<in> set es"
  shows "Inl u \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc es cs)"
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
    thus ?thesis unfolding x side_rhs_fold_eff.simps dep_aux_seqcomp by simp
  next
    case False
    have mem': "(u, a) \<in> set es" using Cons.prems x False by auto
    have "Inl u \<in> dep_aux \<sigma> (side_rhs_fold_eff etf
            (acc \<squnion> traverse_rhs (apply_etf etf b w) \<sigma>) es cs)"
      by (rule Cons.IH[OF mem'])
    thus ?thesis unfolding x side_rhs_fold_eff.simps dep_aux_seqcomp by simp
  qed
qed

text \<open>The combine queries (call queries) survive the edge prefix.\<close>

lemma dep_aux_side_rhs_fold_eff_nil_sub_es:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and comb_static: "\<And>cc ex dst. static_deps (etf_combine etf dst cc ex)"
  shows "dep_aux \<sigma> (side_rhs_fold_eff etf acc [] cs)
       \<subseteq> dep_aux \<sigma> (side_rhs_fold_eff etf acc es cs)"
proof (induction es arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x es)
  obtain w b where x: "x = (w, b)" by (cases x)
  let ?acc' = "acc \<squnion> traverse_rhs (apply_etf etf b w) \<sigma>"
  have "dep_aux \<sigma> (side_rhs_fold_eff etf acc [] cs)
        = dep_aux \<sigma> (side_rhs_fold_eff etf ?acc' [] cs)"
    by (rule dep_aux_side_rhs_fold_eff_acc_indep[OF edge_static comb_static])
  also have "... \<subseteq> dep_aux \<sigma> (side_rhs_fold_eff etf ?acc' es cs)"
    by (rule Cons.IH)
  also have "... \<subseteq> dep_aux \<sigma> (side_rhs_fold_eff etf acc (x # es) cs)"
    unfolding x side_rhs_fold_eff.simps dep_aux_seqcomp by auto
  finally show ?case .
qed

lemma Inl_dep_aux_side_rhs_fold_eff_call:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes comb_dep: "\<And>c2 e2 d2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and comb_static: "\<And>cc ex dst. static_deps (etf_combine etf dst cc ex)"
  assumes mem: "(cc, ex, dst) \<in> set cs"
  shows "Inl cc \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc es cs)"
proof -
  have nil: "Inl cc \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc [] cs)"
    using mem
  proof (induction cs arbitrary: acc)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain c2 e2 d2 where x: "x = (c2, e2, d2)" by (cases x)
    show ?case
    proof (cases "(c2, e2, d2) = (cc, ex, dst)")
      case True
      have "Inl c2 \<in> dep_aux \<sigma> (etf_combine etf d2 c2 e2)" by (rule comb_dep)
      then have "Inl cc \<in> dep_aux \<sigma> (etf_combine etf d2 c2 e2)" using True by simp
      thus ?thesis unfolding x side_rhs_fold_eff.simps dep_aux_seqcomp by simp
    next
      case False
      have mem': "(cc, ex, dst) \<in> set cs" using Cons.prems x False by auto
      have "Inl cc \<in> dep_aux \<sigma> (side_rhs_fold_eff etf
              (acc \<squnion> traverse_rhs (etf_combine etf d2 c2 e2) \<sigma>) [] cs)"
        by (rule Cons.IH[OF mem'])
      thus ?thesis unfolding x side_rhs_fold_eff.simps dep_aux_seqcomp by simp
    qed
  qed
  show ?thesis
    using nil dep_aux_side_rhs_fold_eff_nil_sub_es[OF edge_static comb_static]
    by blast
qed

lemma Inl_dep_aux_side_rhs_fold_eff_exit:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes comb_dep: "\<And>c2 e2 d2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and comb_static: "\<And>cc ex dst. static_deps (etf_combine etf dst cc ex)"
  assumes mem: "(cc, ex, dst) \<in> set cs"
  shows "Inl ex \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc es cs)"
proof -
  have nil: "Inl ex \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc [] cs)"
    using mem
  proof (induction cs arbitrary: acc)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain c2 e2 d2 where x: "x = (c2, e2, d2)" by (cases x)
    show ?case
    proof (cases "(c2, e2, d2) = (cc, ex, dst)")
      case True
      have "Inl e2 \<in> dep_aux \<sigma> (etf_combine etf d2 c2 e2)" by (rule comb_dep)
      then have "Inl ex \<in> dep_aux \<sigma> (etf_combine etf d2 c2 e2)" using True by simp
      thus ?thesis unfolding x side_rhs_fold_eff.simps dep_aux_seqcomp by simp
    next
      case False
      have mem': "(cc, ex, dst) \<in> set cs" using Cons.prems x False by auto
      have "Inl ex \<in> dep_aux \<sigma> (side_rhs_fold_eff etf
              (acc \<squnion> traverse_rhs (etf_combine etf d2 c2 e2) \<sigma>) [] cs)"
        by (rule Cons.IH[OF mem'])
      thus ?thesis unfolding x side_rhs_fold_eff.simps dep_aux_seqcomp by simp
    qed
  qed
  show ?thesis
    using nil dep_aux_side_rhs_fold_eff_nil_sub_es[OF edge_static comb_static]
    by blast
qed

subsection \<open>Dependency at the eqsT level (edges and combine endpoints)\<close>

lemma dep_side_rhs_tree_eff_edge:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g
  assumes fin: "finite (edges g)"
  assumes ed: "(u, a, w) \<in> edges g"
  assumes edge_dep: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  shows "u \<in> dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) \<sigma> w"
proof -
  have mem: "(u, a) \<in> set (predecessor_list g w)"
    using ed by (simp add: set_predecessor_list[OF fin] predecessors_def)
  have "Inl u \<in> dep_aux \<sigma> (make_side_rhs_tree_eff g etf bot0 s0 gseed w)"
    unfolding dep_aux_make_side_rhs_tree_eff
    by (rule Inl_dep_aux_side_rhs_fold_eff_edge[OF edge_dep mem])
  thus ?thesis unfolding side_cfg_T_eff_def dep\<^sub>L_def dep_def by simp
qed

lemma dep_side_rhs_tree_eff_combine:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and c ex w :: pp and gseed :: 'g
  assumes finC: "finite (combines g)"
  assumes ce: "(c, ex, w, dst) \<in> combines g"
  assumes comb_dep1: "\<And>c2 e2 d2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 d2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes comb_static: "\<And>cc ex dst. static_deps (etf_combine etf dst cc ex)"
  shows "c \<in> dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) \<sigma> w
       \<and> ex \<in> dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) \<sigma> w"
proof -
  have mem: "(c, ex, dst) \<in> set (combine_predecessor_list g w)"
    using ce by (simp add: set_combine_predecessor_list[OF finC] combine_predecessors_eq)
  have dc: "Inl c \<in> dep_aux \<sigma> (make_side_rhs_tree_eff g etf bot0 s0 gseed w)"
    unfolding dep_aux_make_side_rhs_tree_eff
    by (rule Inl_dep_aux_side_rhs_fold_eff_call[OF comb_dep1 edge_static comb_static mem])
  have de: "Inl ex \<in> dep_aux \<sigma> (make_side_rhs_tree_eff g etf bot0 s0 gseed w)"
    unfolding dep_aux_make_side_rhs_tree_eff
    by (rule Inl_dep_aux_side_rhs_fold_eff_exit[OF comb_dep2 edge_static comb_static mem])
  show ?thesis using dc de unfolding side_cfg_T_eff_def dep\<^sub>L_def dep_def by simp
qed

subsection \<open>Backward IP reachability lands in the effectful solver's dependency cone\<close>

lemma cfg_reaches_imp_trans_dep_or_eq_side_eff:
  fixes g :: cfg and etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state" and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state" and gseed :: 'g
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes edge_dep: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  assumes comb_dep1: "\<And>c2 e2 d2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 d2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes comb_static: "\<And>cc ex dst. static_deps (etf_combine etf dst cc ex)"
  assumes reach: "cfg_reaches g w v0"
  shows "w = v0 \<or> w \<in> trans_dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) \<sigma> v0"
proof -
  from reach have "(w, v0) \<in> {(u, z). cfg_succ g u z}\<^sup>*"
    unfolding cfg_reaches_def by (simp add: cfg_succ_def)
  thus ?thesis
  proof (induction rule: converse_rtrancl_induct)
    case base
    show ?case by simp
  next
    case (step y z)
    have su: "cfg_succ g y z" using step.hyps(1) by simp
    have ydep: "y \<in> dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) \<sigma> z"
    proof -
      from su consider
        (e) a where "(y, a, z) \<in> edges g"
        | (cc) e d where "(y, e, z, d) \<in> combines g"
        | (ce) c d where "(c, y, z, d) \<in> combines g"
        unfolding cfg_succ_def cfg_succ_rel_def
        by (auto simp: combine_call_node_def combine_exit_node_def
                       combine_return_node_def
                 split: prod.splits)
      then show ?thesis
      proof cases
        case e
        thus ?thesis using dep_side_rhs_tree_eff_edge[OF fin _ edge_dep] by blast
      next
        case cc
        thus ?thesis
          using dep_side_rhs_tree_eff_combine[OF finC _ comb_dep1 comb_dep2
                  edge_static comb_static] by blast
      next
        case ce
        thus ?thesis
          using dep_side_rhs_tree_eff_combine[OF finC _ comb_dep1 comb_dep2
                  edge_static comb_static] by blast
      qed
    qed
    show ?case
    proof (cases "z = v0")
      case True
      show ?thesis using ydep True trans_dep\<^sub>L_step_in by blast
    next
      case False
      have z_in: "z \<in> trans_dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) \<sigma> v0"
        using step.IH False by blast
      have "y \<in> trans_dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) \<sigma> v0"
        by (metis Nitpick.tranclp_unfold mem_Collect_eq
              tranclp.trancl_into_trancl ydep z_in)
      thus ?thesis by blast
    qed
  qed
qed

lemma side_cone_in_vars_eff:
  fixes g :: cfg and etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state" and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state" and gseed :: 'g
  assumes pp: "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) v0 \<sigma> vars"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes edge_dep: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  assumes comb_dep1: "\<And>c2 e2 d2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 d2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes comb_static: "\<And>cc ex dst. static_deps (etf_combine etf dst cc ex)"
  assumes reach: "cfg_reaches g w v0"
  shows "w \<in> vars"
proof -
  have v0v: "v0 \<in> vars" using pp by auto
  consider (eq) "w = v0"
    | (td) "w \<in> trans_dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) \<sigma> v0"
    using cfg_reaches_imp_trans_dep_or_eq_side_eff[OF fin finC edge_dep comb_dep1
            comb_dep2 edge_static comb_static reach] by blast
  thus ?thesis
  proof cases
    case eq thus ?thesis using v0v by simp
  next
    case td
    have "trans_dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) \<sigma> v0 \<subseteq> vars"
      using part_post_solution_implies_trans_dep_subsumed[OF pp] by simp
    thus ?thesis using td by blast
  qed
qed

corollary side_cone_in_vars_eff_cone:
  fixes g :: cfg and etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state" and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state" and gseed :: 'g
  assumes pp:   "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) v0 \<sigma> vars"
  assumes fin:  "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes cone: "cone_compatible_etf etf"
  assumes reach: "cfg_reaches g w v0"
  shows "w \<in> vars"
  by (rule side_cone_in_vars_eff[OF pp fin finC
        cone_compatible_etf_edge_dep[OF cone]
        cone_compatible_etf_comb_dep1[OF cone]
        cone_compatible_etf_comb_dep2[OF cone]
        cone_compatible_etf_edge_static[OF cone]
        cone_compatible_etf_comb_static[OF cone]
        reach])

subsection \<open>Entry coverage from an arbitrary initial state\<close>

text \<open>
  The entry node's wrapping Side gseed contributes restrict_global s0 to the
  designated named-global slot gseed, so the initial globals are below it in any
  post-solution.
\<close>

lemma restrict_global_s0_le_global_eff:
  fixes etf :: "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g
  assumes pp: "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) x \<sigma> vars"
      and entry_in: "cfg_entry g \<in> vars"
  shows "restrict_global s0 \<le> \<sigma> (Inr gseed)"
proof -
  from pp entry_in
  have "sides_of_rhs (side_cfg_T_eff g etf bot0 s0 gseed (cfg_entry g)) \<sigma> \<le> \<sigma>" by auto
  hence le: "sides_of_rhs (side_cfg_T_eff g etf bot0 s0 gseed (cfg_entry g)) \<sigma> (Inr gseed)
             \<le> \<sigma> (Inr gseed)"
    by (simp add: le_fun_def)
  have e: "sides_of_rhs (side_cfg_T_eff g etf bot0 s0 gseed (cfg_entry g)) \<sigma> (Inr gseed)
           = sides_of_rhs (side_rhs_fold_eff etf (bot0 \<squnion> restrict_local s0)
                (predecessor_list g (cfg_entry g))
                (combine_predecessor_list g (cfg_entry g))) \<sigma> (Inr gseed)
             \<squnion> restrict_global s0"
    unfolding side_cfg_T_eff_def make_side_rhs_tree_eff_def
    by (simp add: Let_def)
  have "restrict_global s0
        \<le> sides_of_rhs (side_cfg_T_eff g etf bot0 s0 gseed (cfg_entry g)) \<sigma> (Inr gseed)"
    unfolding e by (rule sup_ge2)
  thus ?thesis using le by (rule order_trans)
qed

text \<open>
  At the entry point the local fold seeds restrict_local s0 and the wrapping
  Side gseed seeds restrict_global s0 into slot gseed (below glob_env), so s0
  itself is below the combined env at the entry -- for an arbitrary initial state.
\<close>
lemma s0_le_side_env_entry_eff:
  fixes etf :: "('g::finite, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and gseed :: 'g
  assumes pp: "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) v0 \<sigma> vars"
  assumes entry_in: "cfg_entry g \<in> vars"
  shows "s0 \<le> side_env \<sigma> (cfg_entry g)"
proof -
  have acc_le: "side_acc_eff etf (bot0 \<squnion> restrict_local s0) \<sigma>
                  (predecessor_list g (cfg_entry g))
                  (combine_predecessor_list g (cfg_entry g))
                \<le> \<sigma> (Inl (cfg_entry g))"
    using side_post_solution_le_local_eff[OF pp entry_in] by simp
  have "restrict_local s0 \<le> bot0 \<squnion> restrict_local s0" by simp
  also have "... \<le> side_acc_eff etf (bot0 \<squnion> restrict_local s0) \<sigma>
                     (predecessor_list g (cfg_entry g))
                     (combine_predecessor_list g (cfg_entry g))"
    by (rule side_acc_eff_ge_acc)
  also have "... \<le> \<sigma> (Inl (cfg_entry g))" by (rule acc_le)
  finally have rl: "restrict_local s0 \<le> \<sigma> (Inl (cfg_entry g))" .
  have rg: "restrict_global s0 \<le> \<sigma> (Inr gseed)"
    by (rule restrict_global_s0_le_global_eff[OF pp entry_in])
  have "s0 = restrict_local s0 \<squnion> restrict_global s0"
    by (rule restrict_local_global_join[symmetric])
  also have "... \<le> \<sigma> (Inl (cfg_entry g)) \<squnion> \<sigma> (Inr gseed)"
    using rl rg by (rule sup_mono)
  also have "... \<le> \<sigma> (Inl (cfg_entry g)) \<squnion> glob_env \<sigma>"
    by (rule sup_mono[OF order_refl glob_env_upper])
  finally show ?thesis unfolding side_env_def .
qed

subsection \<open>Exit-rooted collecting soundness with coverage discharged by pruning\<close>


subsection \<open>Unit-global effectful record contracts\<close>

text \<open>
  Unit-global records have fixed QueryL/QueryG skeletons for edge and combine
  trees.  The solver-side cone and monotonicity contracts follow from that tree
  shape and monotonicity of the edge transformers.
\<close>

lemma cone_compatible_etf_unit_transfer:
  fixes etf :: "(unit, 'a::sound_domain) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes comb: "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree dst cc ex"
  shows "cone_compatible_etf etf"
proof -
  interpret mixed_rhs_generator etf F by (unfold_locales; simp add: edge comb)
  show ?thesis by (rule cone_compatible)
qed

lemma threefold_mono_unit_transfer:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and g :: cfg and bot0 s0 :: "'a abs_state"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes comb: "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree dst cc ex"
  assumes mono: "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2"
  shows "threefold_mono (side_cfg_T_eff g etf bot0 s0 ())"
proof -
  interpret mixed_rhs_generator_mono etf F
  proof
    show "\<And>a u. apply_etf etf a u = local_edge_tree (F a) u
                \<or> apply_etf etf a u = unit_edge_tree (F a) u" by (simp add: edge)
    show "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree dst cc ex" by (rule comb)
    show "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2" by (rule mono)
  qed
  show ?thesis by (rule threefold_mono)
qed

lemma cone_compatible_etf_local_unit_transfer:
  fixes etf :: "(unit, 'a::sound_domain) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes edge: "\<And>a u. apply_etf etf a u =
    (if local_edge_action a then local_edge_tree (F a) u
     else unit_edge_tree (F a) u)"
  assumes comb: "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree dst cc ex"
  shows "cone_compatible_etf etf"
proof -
  interpret mixed_rhs_generator etf F by (unfold_locales; simp add: edge comb)
  show ?thesis by (rule cone_compatible)
qed

lemma threefold_mono_local_unit_transfer:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and g :: cfg and bot0 s0 :: "'a abs_state"
  assumes edge: "\<And>a u. apply_etf etf a u =
    (if local_edge_action a then local_edge_tree (F a) u
     else unit_edge_tree (F a) u)"
  assumes comb: "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree dst cc ex"
  assumes mono: "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2"
  shows "threefold_mono (side_cfg_T_eff g etf bot0 s0 ())"
proof -
  interpret mixed_rhs_generator_mono etf F
  proof
    show "\<And>a u. apply_etf etf a u = local_edge_tree (F a) u
                \<or> apply_etf etf a u = unit_edge_tree (F a) u" by (simp add: edge)
    show "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree dst cc ex" by (rule comb)
    show "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2" by (rule mono)
  qed
  show ?thesis by (rule threefold_mono)
qed

end
