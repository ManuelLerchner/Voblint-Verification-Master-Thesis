theory TD_Side_IP_Soundness
  imports TD_Side_IP_Interface Constraint_System_IP_Sound "Voblint_CFG.CFG_Prune"
begin

section \<open>Side IP solver: collecting soundness\<close>

subsection \<open>Backward IP reachability lands in the side solver's dependency cone\<close>

lemma ip_reaches_imp_trans_dep_or_eq_side:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state" and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes "ip_reaches g w v0"
  shows "w = v0 \<or> w \<in> trans_dep\<^sub>L (side_cfg_T_ip g tf (\<squnion>) bot0 s0) \<sigma> v0"
proof -
  from assms(3) have "(w, v0) \<in> {(u, z). ip_succ g u z}\<^sup>*"
    unfolding ip_reaches_def .
  thus ?thesis
  proof (induction rule: converse_rtrancl_induct)
    case base
    show ?case by simp
  next
    case (step y z)
    have su: "ip_succ g y z" using step.hyps(1) by simp
    have ydep: "y \<in> dep\<^sub>L (side_cfg_T_ip g tf (\<squnion>) bot0 s0) \<sigma> z"
    proof -
      from su consider
        (e) a where "(y, a, z) \<in> edges g"
        | (cc) e where "(y, e, z) \<in> combines g"
        | (ce) c where "(c, y, z) \<in> combines g"
        unfolding ip_succ_def by blast
      then show ?thesis
      proof cases
        case e thus ?thesis using dep_side_rhs_tree_ip_edge[OF fin] by blast
      next
        case cc thus ?thesis using dep_side_rhs_tree_ip_combine[OF finC] by blast
      next
        case ce thus ?thesis using dep_side_rhs_tree_ip_combine[OF finC] by blast
      qed
    qed
    show ?case
    proof (cases "z = v0")
      case True
      show ?thesis using ydep True trans_dep\<^sub>L_step_in by blast
    next
      case False
      have z_in: "z \<in> trans_dep\<^sub>L (side_cfg_T_ip g tf (\<squnion>) bot0 s0) \<sigma> v0"
        using step.IH False by blast
      show ?thesis using trans_dep\<^sub>L_trans[OF z_in ydep] by blast
    qed
  qed
qed

(* Every node in the backward cone of the query point is in the solved stable
   set vars. *)
lemma side_ip_cone_in_vars:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state" and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes pp: "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0) v0 \<sigma> vars"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes reach: "ip_reaches g w v0"
  shows "w \<in> vars"
proof -
  have v0v: "v0 \<in> vars" using pp by auto
  consider (eq) "w = v0"
    | (td) "w \<in> trans_dep\<^sub>L (side_cfg_T_ip g tf (\<squnion>) bot0 s0) \<sigma> v0"
    using ip_reaches_imp_trans_dep_or_eq_side[OF fin finC reach] by blast
  thus ?thesis
  proof cases
    case eq thus ?thesis using v0v by simp
  next
    case td
    have "trans_dep\<^sub>L (side_cfg_T_ip g tf (\<squnion>) bot0 s0) \<sigma> v0 \<subseteq> vars"
      using part_post_solution_implies_trans_dep_subsumed[OF pp] by simp
    thus ?thesis using td by blast
  qed
qed

text \<open>
  Collecting soundness of a side-effecting interprocedural post-solution: the
  combined env of a side_cfg_T_ip post-solution soundly over-approximates the
  interprocedural CFG collecting semantics (cfg_collect_ip), which folds in the
  combine triples.

  Reuses the generic, solver-agnostic bridge post_fixpoint_sound_at_ip; the only
  IP-specific content is the per-edge bound (apply_tf_combined_le_ip) and the
  per-combine bound (combine_combined_le_ip) proved in TD_Side_IP_Bounds.

  Coverage (every edge target / combine return point lies in the solved stable
  set vars) is taken as a hypothesis here; on the backward cone of the query
  node it is discharged by pruning.
\<close>

context sound_transfer
begin

theorem side_collect_sound_ip_at:
  fixes \<sigma> :: "pp + unit => 'a abs_state"
    and bot0 s0 :: "'a abs_state" and v0 :: pp and S :: "store set"
  assumes pp: "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0) v0 \<sigma> vars"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes entry: "S \<le> gamma_state (side_env \<sigma> (cfg_entry g))"
  assumes edge_cov: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> w \<in> vars"
  assumes combine_cov: "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow> ret \<in> vars"
  shows "cfg_collect_ip g S v0 \<le> gamma_state (side_env \<sigma> v0)"
proof -
  have step_le:
    "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> apply_tf tf a (side_env \<sigma> u) \<le> side_env \<sigma> w"
  proof -
    fix u a w assume ed: "(u, a, w) \<in> edges g"
    have wv: "w \<in> vars" by (rule edge_cov[OF ed])
    show "apply_tf tf a (side_env \<sigma> u) \<le> side_env \<sigma> w"
      by (rule apply_tf_combined_le_ip[OF pp wv ed fin])
  qed
  have combine_le:
    "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow>
       combine_abs (side_env \<sigma> c) (side_env \<sigma> ex) \<le> side_env \<sigma> ret"
  proof -
    fix c ex ret assume cb: "(c, ex, ret) \<in> combines g"
    have rv: "ret \<in> vars" by (rule combine_cov[OF cb])
    show "combine_abs (side_env \<sigma> c) (side_env \<sigma> ex) \<le> side_env \<sigma> ret"
      by (rule combine_combined_le_ip[OF pp rv cb finC])
  qed
  have entry_le: "side_env \<sigma> (cfg_entry g) \<le> side_env \<sigma> (cfg_entry g)" by (rule order_refl)
  show ?thesis
    by (rule post_fixpoint_sound_at_ip[where env = "side_env \<sigma>",
          OF fin finC entry step_le combine_le entry_le])
qed

text \<open>
  Exit-rooted soundness with the coverage condition discharged by pruning: the
  solver runs on the full graph g, while the collecting value at the exit
  depends only on the backward cone, which is connected by construction, so
  every edge target / combine return on the cone is in the solved stable set.
  No coverage hypothesis is needed.
\<close>
theorem side_collect_sound_ip_exit_pruned:
  fixes g :: cfg and \<sigma> :: "pp + unit => 'a abs_state"
    and bot0 s0 :: "'a abs_state" and S :: "store set"
  assumes pp: "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0)
                 (cfg_exit g) \<sigma> vars"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes entry: "S \<le> gamma_state (side_env \<sigma> (cfg_entry g))"
  shows "cfg_collect_ip g S (cfg_exit g) \<le> gamma_state (side_env \<sigma> (cfg_exit g))"
proof -
  define pg where "pg = prune_cfg g"
  have fin_pg: "finite (edges pg)"
    unfolding pg_def prune_cfg_def using finite_edges_prune_to[OF fin] .
  have finC_pg: "finite (combines pg)"
    unfolding pg_def prune_cfg_def using finite_combines_prune_to[OF finC] .
  have step_le:
    "\<And>u a w. (u, a, w) \<in> edges pg \<Longrightarrow> apply_tf tf a (side_env \<sigma> u) \<le> side_env \<sigma> w"
  proof -
    fix u a w assume e_pg: "(u, a, w) \<in> edges pg"
    have e_pg2: "(u, a, w) \<in> edges (prune_to g (cfg_exit g))"
      using e_pg by (simp add: pg_def prune_cfg_def)
    have ed_g: "(u, a, w) \<in> edges g" using e_pg2 edges_prune_to_sub by blast
    have w_cone: "ip_reaches g w (cfg_exit g)" using e_pg2 by (simp add: cone_def)
    have wv: "w \<in> vars" by (rule side_ip_cone_in_vars[OF pp fin finC w_cone])
    show "apply_tf tf a (side_env \<sigma> u) \<le> side_env \<sigma> w"
      by (rule apply_tf_combined_le_ip[OF pp wv ed_g fin])
  qed
  have combine_le:
    "\<And>c ex ret. (c, ex, ret) \<in> combines pg \<Longrightarrow>
       combine_abs (side_env \<sigma> c) (side_env \<sigma> ex) \<le> side_env \<sigma> ret"
  proof -
    fix c ex ret assume cmb: "(c, ex, ret) \<in> combines pg"
    have cmb2: "(c, ex, ret) \<in> combines (prune_to g (cfg_exit g))"
      using cmb by (simp add: pg_def prune_cfg_def)
    have uce_g: "(c, ex, ret) \<in> combines g" using cmb2 combines_prune_to_sub by blast
    have r_cone: "ip_reaches g ret (cfg_exit g)" using cmb2 by (simp add: cone_def)
    have rv: "ret \<in> vars" by (rule side_ip_cone_in_vars[OF pp fin finC r_cone])
    show "combine_abs (side_env \<sigma> c) (side_env \<sigma> ex) \<le> side_env \<sigma> ret"
      by (rule combine_combined_le_ip[OF pp rv uce_g finC])
  qed
  have entry_pg: "S \<le> gamma_state (side_env \<sigma> (cfg_entry pg))"
    using entry by (simp add: pg_def prune_cfg_def)
  have entry_le: "side_env \<sigma> (cfg_entry pg) \<le> side_env \<sigma> (cfg_entry pg)"
    by (rule order_refl)
  have collect_pg: "cfg_collect_ip pg S (cfg_exit g) \<le> gamma_state (side_env \<sigma> (cfg_exit g))"
    by (rule post_fixpoint_sound_at_ip[where env = "side_env \<sigma>",
          OF fin_pg finC_pg entry_pg step_le combine_le entry_le])
  have frame: "cfg_collect_ip g S (cfg_exit g) \<subseteq> cfg_collect_ip pg S (cfg_exit g)"
    using cfg_collect_ip_prune_exit[of g S] by (simp add: pg_def)
  show ?thesis using frame collect_pg by blast
qed

text \<open>
  Executable-facing soundness: run the side TD solver on the compiled program,
  read back the combined env (side_analyse_ip), and over-approximate the IP
  collecting semantics at the program exit.  The entry condition is discharged
  from an arbitrary initial state s0 (the entry seeds both its locals and its
  globals).
\<close>
theorem side_analyse_ip_collect_sound_exit_pruned:
  fixes \<Pi> ps main and s0 :: "'a abs_state" and S :: "store set"
  assumes tf_mono: "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes dom: "side_cfg_ip_solve_dom (compile_prog \<Pi> ps main) tf bot s0
                  (cfg_exit (compile_prog \<Pi> ps main))"
  assumes S_sound: "S \<le> gamma_state s0"
  shows "cfg_collect_ip (compile_prog \<Pi> ps main) S (cfg_exit (compile_prog \<Pi> ps main))
         \<le> gamma_state (side_analyse_ip \<Pi> ps main tf bot s0
              (cfg_exit (compile_prog \<Pi> ps main)))"
proof -
  define g where "g = compile_prog \<Pi> ps main"
  define v0 where "v0 = cfg_exit g"
  interpret ip: td_cfg_side_ip_solver g tf bot s0
    using tf_mono by unfold_locales
  define \<sigma> where "\<sigma> = ip.side_nu_at v0"
  have fin: "finite (edges g)" unfolding g_def using compile_prog_finite by simp
  have finC: "finite (combines g)" unfolding g_def using compile_prog_finite by simp
  have dom': "side_cfg_ip_solve_dom g tf bot s0 v0"
    using dom unfolding g_def v0_def by simp
  have pp: "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot s0) v0 \<sigma> (ip.side_stabl_at v0)"
    using ip.side_solver_part_post_at_cfg[OF dom'] unfolding \<sigma>_def
    by (simp add: ip.cfg_side_T_ip_pkg_eq)
  have entry_reach: "ip_reaches g (cfg_entry g) v0"
    using compile_prog_entry_ip_reaches_exit unfolding g_def v0_def by simp
  have entry_in: "cfg_entry g \<in> ip.side_stabl_at v0"
    by (rule side_ip_cone_in_vars[OF pp fin finC entry_reach])
  have entry_le: "s0 \<le> side_env \<sigma> (cfg_entry g)"
    by (rule s0_le_side_env_entry_ip[OF pp entry_in])
  have entry_cov: "S \<le> gamma_state (side_env \<sigma> (cfg_entry g))"
    using S_sound gamma_state_mono[OF entry_le] by blast
  have collect: "cfg_collect_ip g S (cfg_exit g) \<le> gamma_state (side_env \<sigma> (cfg_exit g))"
    by (rule side_collect_sound_ip_exit_pruned[OF pp[unfolded v0_def] fin finC entry_cov])
  have analyse_eq:
    "side_analyse_ip \<Pi> ps main tf bot s0 (cfg_exit g) = side_env \<sigma> (cfg_exit g)"
    unfolding side_analyse_ip_def \<sigma>_def v0_def g_def by simp
  show ?thesis
    using collect analyse_eq by (simp add: g_def)
qed

end

end
