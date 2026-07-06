theory TD_Side_Eff_Soundness
  imports TD_Side_RHS_Generator "Voblint_CFG.CFG_Prune"
begin

section \<open>Standalone effectful side IP solver: collecting soundness with pruning\<close>

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
      and comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
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
      and comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
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
  assumes comb_dep: "\<And>c2 e2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  assumes mem: "(cc, ex) \<in> set cs"
  shows "Inl cc \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc es cs)"
proof -
  have nil: "Inl cc \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc [] cs)"
    using mem
  proof (induction cs arbitrary: acc)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain c2 e2 where x: "x = (c2, e2)" by (cases x)
    show ?case
    proof (cases "(c2, e2) = (cc, ex)")
      case True
      have "Inl c2 \<in> dep_aux \<sigma> (etf_combine etf c2 e2)" by (rule comb_dep)
      then have "Inl cc \<in> dep_aux \<sigma> (etf_combine etf c2 e2)" using True by simp
      thus ?thesis unfolding x side_rhs_fold_eff.simps dep_aux_seqcomp by simp
    next
      case False
      have mem': "(cc, ex) \<in> set cs" using Cons.prems x False by auto
      have "Inl cc \<in> dep_aux \<sigma> (side_rhs_fold_eff etf
              (acc \<squnion> traverse_rhs (etf_combine etf c2 e2) \<sigma>) [] cs)"
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
  assumes comb_dep: "\<And>c2 e2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
      and comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  assumes mem: "(cc, ex) \<in> set cs"
  shows "Inl ex \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc es cs)"
proof -
  have nil: "Inl ex \<in> dep_aux \<sigma> (side_rhs_fold_eff etf acc [] cs)"
    using mem
  proof (induction cs arbitrary: acc)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain c2 e2 where x: "x = (c2, e2)" by (cases x)
    show ?case
    proof (cases "(c2, e2) = (cc, ex)")
      case True
      have "Inl e2 \<in> dep_aux \<sigma> (etf_combine etf c2 e2)" by (rule comb_dep)
      then have "Inl ex \<in> dep_aux \<sigma> (etf_combine etf c2 e2)" using True by simp
      thus ?thesis unfolding x side_rhs_fold_eff.simps dep_aux_seqcomp by simp
    next
      case False
      have mem': "(cc, ex) \<in> set cs" using Cons.prems x False by auto
      have "Inl ex \<in> dep_aux \<sigma> (side_rhs_fold_eff etf
              (acc \<squnion> traverse_rhs (etf_combine etf c2 e2) \<sigma>) [] cs)"
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
  assumes ce: "(c, ex, w) \<in> combines g"
  assumes comb_dep1: "\<And>c2 e2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  shows "c \<in> dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) \<sigma> w
       \<and> ex \<in> dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) \<sigma> w"
proof -
  have mem: "(c, ex) \<in> set (combine_predecessor_list g w)"
    using ce by (simp add: set_combine_predecessor_list[OF finC] combine_predecessors_def)
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
  assumes comb_dep1: "\<And>c2 e2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  assumes reach: "cfg_reaches g w v0"
  shows "w = v0 \<or> w \<in> trans_dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) \<sigma> v0"
proof -
  from reach have "(w, v0) \<in> {(u, z). cfg_succ g u z}\<^sup>*"
    unfolding cfg_reaches_def .
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
        | (cc) e where "(y, e, z) \<in> combines g"
        | (ce) c where "(c, y, z) \<in> combines g"
        unfolding cfg_succ_def by blast
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
  assumes comb_dep1: "\<And>c2 e2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
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

text \<open>
  Exit-rooted effectful collecting soundness: the solver runs on
  the full graph, while the collecting value at the exit depends only on the
  backward cone (connected by construction), so every edge target / combine
  return on the cone is in the solved stable set.  No coverage hypothesis is
  needed beyond the query / static contracts that drive the cone.

  Generic in the named-global type 'g (finite): the soundness contract is an
  explicit hypothesis and the generic abstract soundness is interpreted at 'g.
  The initial globals are seeded into the designated slot gseed at the entry.
\<close>

theorem side_collect_sound_exit_pruned_eff:
  fixes g :: cfg and \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and bot0 s0 :: "'a abs_state" and S :: "store set"
    and etf :: "('g, 'a) effectful_domain_transfer"
    and gseed :: 'g
  assumes se: "sound_effectful_transfer etf"
  assumes pp: "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed)
                 (cfg_exit g) \<sigma> vars"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes edge_dep: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  assumes comb_dep1: "\<And>c2 e2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  assumes inr: "inr_slot_locals_bot \<sigma>"
  shows "cfg_collect g S (cfg_exit g)
         \<le> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
proof -
  interpret se: sound_effectful_transfer etf by (rule se)
  define pg where "pg = prune_cfg g"
  have fin_pg: "finite (edges pg)"
    using fin by (auto simp: pg_def prune_cfg_def)
  have finC_pg: "finite (combines pg)"
    using finC by (auto simp: pg_def prune_cfg_def)
  have step_le:
    "\<And>u a w. (u, a, w) \<in> edges pg \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  proof -
    fix u a w assume e_pg: "(u, a, w) \<in> edges pg"
    have e_pg2: "(u, a, w) \<in> edges (prune_to g (cfg_exit g))"
      using e_pg by (simp add: pg_def prune_cfg_def)
    have ed_g: "(u, a, w) \<in> edges g" using e_pg2 by auto
    have w_cone: "cfg_reaches g w (cfg_exit g)" using e_pg2 by (simp add: cone_def)
    have wv: "w \<in> vars"
      by (rule side_cone_in_vars_eff[OF pp fin finC edge_dep comb_dep1 comb_dep2
            edge_static comb_static w_cone])
    show "etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
      by (rule etf_combined_le_eff[OF pp wv ed_g fin])
  qed
  have combine_le:
    "\<And>c ex ret. (c, ex, ret) \<in> combines pg \<Longrightarrow>
       etf_full (etf_combine etf c ex) \<sigma> \<le> side_env \<sigma> ret"
  proof -
    fix c ex ret assume cmb: "(c, ex, ret) \<in> combines pg"
    have cmb2: "(c, ex, ret) \<in> combines (prune_to g (cfg_exit g))"
      using cmb by (simp add: pg_def prune_cfg_def)
    have uce_g: "(c, ex, ret) \<in> combines g" using cmb2 by auto
    have r_cone: "cfg_reaches g ret (cfg_exit g)" using cmb2 by (simp add: cone_def)
    have rv: "ret \<in> vars"
      by (rule side_cone_in_vars_eff[OF pp fin finC edge_dep comb_dep1 comb_dep2
            edge_static comb_static r_cone])
    show "etf_full (etf_combine etf c ex) \<sigma> \<le> side_env \<sigma> ret"
      by (rule etf_combine_combined_le_eff[OF pp rv uce_g finC])
  qed
  have entry_pg: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry pg)\<rbrakk>"
    using entry by (simp add: pg_def prune_cfg_def)
  have collect_pg: "cfg_collect pg S (cfg_exit g) \<le> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
    by (rule se.post_fixpoint_sound_at_eff[OF inr entry_pg step_le combine_le order_refl])
  have frame: "cfg_collect g S (cfg_exit g) \<subseteq> cfg_collect pg S (cfg_exit g)"
    using cfg_collect_prune_exit[of g S] by (simp add: pg_def)
  show ?thesis using frame collect_pg by blast
qed

corollary side_collect_sound_exit_pruned_eff_cone:
  fixes g :: cfg and \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and bot0 s0 :: "'a abs_state" and S :: "store set"
    and etf :: "('g, 'a) effectful_domain_transfer" and gseed :: 'g
  assumes se:    "sound_effectful_transfer etf"
  assumes pp:    "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) (cfg_exit g) \<sigma> vars"
  assumes fin:   "finite (edges g)"
  assumes finC:  "finite (combines g)"
  assumes entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes cone:  "cone_compatible_etf etf"
  assumes inr: "inr_slot_locals_bot \<sigma>"
  shows "cfg_collect g S (cfg_exit g) \<le> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
  by (rule side_collect_sound_exit_pruned_eff[OF se pp fin finC entry
        cone_compatible_etf_edge_dep[OF cone]
        cone_compatible_etf_comb_dep1[OF cone]
        cone_compatible_etf_comb_dep2[OF cone]
        cone_compatible_etf_edge_static[OF cone]
        cone_compatible_etf_comb_static[OF cone] inr])

subsection \<open>Executable-facing standalone soundness\<close>

text \<open>
  Run the effectful side TD solver on the compiled program, read back the
  combined env (side_analyse_eff), and over-approximate the IP collecting
  semantics at the program exit.  The three TD_side preconditions and the cone
  query / static contracts are taken as hypotheses; domain instances discharge
  them from their effectful transfer record construction.
\<close>
theorem side_analyse_eff_collect_sound_exit_pruned_gen:
  fixes \<Pi> ps main and s0 :: "'a::sound_domain abs_state"
    and S :: "store set"
    and etf :: "('g::finite, 'a) effectful_domain_transfer"
    and gseed :: 'g
  assumes se: "sound_effectful_transfer etf"
  assumes mono_eq: "is_mono_eq (side_cfg_T_eff (compile_prog \<Pi> ps main) etf bot s0 gseed)"
  assumes mono_sides: "mono_sides (side_cfg_T_eff (compile_prog \<Pi> ps main) etf bot s0 gseed)"
  assumes mono_deps: "mono_deps (side_cfg_T_eff (compile_prog \<Pi> ps main) etf bot s0 gseed)"
  assumes dom: "side_cfg_solve_dom_eff (compile_prog \<Pi> ps main) etf bot s0 gseed
                  (cfg_exit (compile_prog \<Pi> ps main))"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes edge_dep: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  assumes comb_dep1: "\<And>c2 e2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  assumes edge_inr:
    "\<And>a u \<sigma>' g. local_bot_on_locals (sides_of_rhs (apply_etf etf a u) \<sigma>' (Inr g))"
  assumes comb_inr:
    "\<And>cc ex \<sigma>' g. local_bot_on_locals (sides_of_rhs (etf_combine etf cc ex) \<sigma>' (Inr g))"
  shows "cfg_collect (compile_prog \<Pi> ps main) S (cfg_exit (compile_prog \<Pi> ps main))
         \<le> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed
              (cfg_exit (compile_prog \<Pi> ps main))\<rbrakk>"
proof -
  interpret se: sound_effectful_transfer etf by (rule se)
  define g where "g = compile_prog \<Pi> ps main"
  define v0 where "v0 = cfg_exit g"
  interpret ip: td_cfg_side_solver_eff g etf bot s0 gseed
    using mono_eq mono_sides mono_deps unfolding g_def by unfold_locales
  define \<sigma> where "\<sigma> = ip.nu_at v0"
  have fin: "finite (edges g)" unfolding g_def using compile_prog_finite by simp
  have finC: "finite (combines g)" unfolding g_def using compile_prog_finite by simp
  have dom': "side_cfg_solve_dom_eff g etf bot s0 gseed v0"
    using dom unfolding g_def v0_def by simp
  have pp: "part_post_solution (side_cfg_T_eff g etf bot s0 gseed) v0 \<sigma> (ip.stabl_at v0)"
    using ip.part_post_at_cfg[OF dom'] unfolding \<sigma>_def by simp
  have entry_reach: "cfg_reaches g (cfg_entry g) v0"
    using compile_prog_entry_cfg_reaches_exit unfolding g_def v0_def by simp
  have entry_in: "cfg_entry g \<in> ip.stabl_at v0"
    by (rule side_cone_in_vars_eff[OF pp fin finC edge_dep comb_dep1 comb_dep2
          edge_static comb_static entry_reach])
  have entry_le: "s0 \<le> side_env \<sigma> (cfg_entry g)"
    by (rule s0_le_side_env_entry_eff[OF pp entry_in])
  have entry_cov: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
    using S_sound gamma_state_mono[OF entry_le] by blast
  have least: "least_part_post_solution (side_cfg_T_eff g etf bot s0 gseed) v0 \<sigma> (ip.stabl_at v0)"
    by (metis (mono_tags, opaque_lifting) dom' ip.cfg_pkg_eff_eq ip.least_part_post_at_cfg
        local.\<sigma>_def)
  have inr: "inr_slot_locals_bot \<sigma>"
    by (metis comb_inr comb_static edge_inr edge_static g_def least
        least_part_post_solution_inr_slot_locals_bot_eff mono_eq mono_sides)
  have collect: "cfg_collect g S (cfg_exit g) \<le> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
    by (rule side_collect_sound_exit_pruned_eff[OF se pp[unfolded v0_def] fin finC
          entry_cov edge_dep comb_dep1 comb_dep2 edge_static comb_static inr])


  have analyse_eq:
    "side_analyse_eff \<Pi> ps main etf bot s0 gseed (cfg_exit g) = side_env \<sigma> (cfg_exit g)"
    unfolding side_analyse_eff_def \<sigma>_def v0_def g_def by simp  show ?thesis using collect analyse_eq by (simp add: g_def)
qed

corollary side_analyse_eff_collect_sound_exit_pruned:
  fixes \<Pi> ps main and s0 :: "'a::sound_domain abs_state"
    and S :: "store set"
    and etf :: "('g::finite, 'a) effectful_domain_transfer"
    and gseed :: 'g
  assumes se:   "sound_effectful_transfer etf"
  assumes tfm:  "threefold_mono (side_cfg_T_eff (compile_prog \<Pi> ps main) etf bot s0 gseed)"
  assumes cone: "cone_compatible_etf etf"
  assumes dom:  "side_cfg_solve_dom_eff (compile_prog \<Pi> ps main) etf bot s0 gseed
                   (cfg_exit (compile_prog \<Pi> ps main))"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  shows "cfg_collect (compile_prog \<Pi> ps main) S (cfg_exit (compile_prog \<Pi> ps main))
         \<le> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed
               (cfg_exit (compile_prog \<Pi> ps main))\<rbrakk>"
  by (rule side_analyse_eff_collect_sound_exit_pruned_gen[OF se
        threefold_monoD_eq[OF tfm] threefold_monoD_sides[OF tfm]
        threefold_monoD_deps[OF tfm] dom S_sound
        cone_compatible_etf_edge_dep[OF cone]
        cone_compatible_etf_comb_dep1[OF cone]
        cone_compatible_etf_comb_dep2[OF cone]
        cone_compatible_etf_edge_static[OF cone]
        cone_compatible_etf_comb_static[OF cone]
        cone_compatible_etf_edge_inr[OF cone]
        cone_compatible_etf_comb_inr[OF cone]])


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
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
  shows "cone_compatible_etf etf"
proof -
  interpret unit_rhs_generator etf F using edge comb by unfold_locales
  show ?thesis by (rule cone_compatible)
qed

lemma threefold_mono_unit_transfer:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and g :: cfg and bot0 s0 :: "'a abs_state"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
  assumes mono: "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2"
  shows "threefold_mono (side_cfg_T_eff g etf bot0 s0 ())"
proof -
  interpret unit_rhs_generator_mono etf F using edge comb mono by unfold_locales
  show ?thesis by (rule threefold_mono)
qed

lemma cone_compatible_etf_local_unit_transfer:
  fixes etf :: "(unit, 'a::sound_domain) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes edge: "\<And>a u. apply_etf etf a u =
    (if local_edge_action a then local_edge_tree (F a) u
     else unit_edge_tree (F a) u)"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
  shows "cone_compatible_etf etf"
proof -
  interpret mixed_rhs_generator etf F using edge comb by unfold_locales
  show ?thesis by (rule cone_compatible)
qed

lemma threefold_mono_local_unit_transfer:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and g :: cfg and bot0 s0 :: "'a abs_state"
  assumes edge: "\<And>a u. apply_etf etf a u =
    (if local_edge_action a then local_edge_tree (F a) u
     else unit_edge_tree (F a) u)"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
  assumes mono: "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2"
  shows "threefold_mono (side_cfg_T_eff g etf bot0 s0 ())"
proof -
  interpret mixed_rhs_generator_mono etf F using edge comb mono by unfold_locales
  show ?thesis by (rule threefold_mono)
qed

end
