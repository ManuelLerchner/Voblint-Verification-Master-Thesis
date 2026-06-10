theory TD_IP_Soundness
  imports TD_Interface Constraint_System_IP_Sound CFG_Collect_IP_Adeq CFG_Prune
begin

context sound_transfer
begin

theorem td_analyse_ip_collect_sound_at:
  fixes pi ps main v0
  assumes S_sub: "S \<le> gamma_state s0"
  assumes fin_cfg: "finite (edges (compile_prog pi ps main))"
  assumes fin_comb: "finite (combines (compile_prog pi ps main))"
  assumes td_solve_dom:
    "TD_plain.solve_dom (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0) v0"
  assumes edge_reach:
    "\<And>u a w. (u, a, w) \<in> edges (compile_prog pi ps main)
       \<Longrightarrow> w \<in> reach (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0)
         (TD_plain_Interp_solve (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0) v0) v0"
  assumes combine_reach:
    "\<And>c ex w. (c, ex, w) \<in> combines (compile_prog pi ps main)
       \<Longrightarrow> w \<in> reach (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0)
         (TD_plain_Interp_solve (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0) v0) v0"
  assumes entry_reach:
    "cfg_entry (compile_prog pi ps main)
     \<in> reach (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0)
       (TD_plain_Interp_solve (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0) v0) v0"
  shows "cfg_collect_ip (compile_prog pi ps main) S v0
         \<le> gamma_state (td_analyse_ip pi ps main tf (\<squnion>) bot s0 v0)"
proof -
  define g where "g = compile_prog pi ps main"
  have fin_g: "finite (edges g)" unfolding g_def using fin_cfg by simp
  have finC_g: "finite (combines g)" unfolding g_def using fin_comb by simp
  interpret ip: td_cfg_ip_solver g tf "(\<squnion>)" bot s0
    using fin_g finC_g td_cfg_ip_core_def td_cfg_ip_solver.intro by blast
  define env where "env = ip.td_env_at v0"
  have cfi: "comp_fun_idem ((\<squnion>) :: 'a abs_state \<Rightarrow> _ \<Rightarrow> _)"
    by (rule join_state_comp_fun_idem)
  have join_sym: "\<And>x y :: 'a abs_state. x \<squnion> y = y \<squnion> x"
    by (rule sup.commute)
  have join_is_sup: "(\<squnion>) = (\<squnion>)" by simp
  have bot_is_bot: "bot = bot" by simp
  have cfg_T_ip_fn: "ip.cfg_T_ip = make_rhs_tree_ip g tf (\<squnion>) bot s0"
    by (simp add: ip.cfg_T_ip_def fun_eq_iff)
  have reach_tree: "reach ip.cfg_T_ip = reach (make_rhs_tree_ip g tf (\<squnion>) bot s0)"
    unfolding cfg_T_ip_fn by simp
  have sigma_solve: "ip.td_sigma_at v0 = TD_plain_Interp_solve (make_rhs_tree_ip g tf (\<squnion>) bot s0) v0"
    unfolding ip.td_sigma_at_def ip.td_sigma_at_solve cfg_T_ip_fn by simp
  have dom: "TD_plain.solve_dom ip.cfg_T_ip v0"
  proof -
    have "TD_plain.solve_dom (make_rhs_tree_ip g tf (\<squnion>) bot s0) v0"
      unfolding g_def by (rule td_solve_dom)
    thus ?thesis unfolding cfg_T_ip_fn by simp
  qed
  have step_le:
    "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> apply_tf tf a (env u) \<le> env w"
  proof -
    fix u a w
    assume ed: "(u, a, w) \<in> edges g"
    have ed': "(u, a, w) \<in> edges (compile_prog pi ps main)"
      using ed by (simp add: g_def)
    have w_reach': "w \<in> reach (make_rhs_tree_ip g tf (\<squnion>) bot s0)
        (TD_plain_Interp_solve (make_rhs_tree_ip g tf (\<squnion>) bot s0) v0) v0"
      using edge_reach[OF ed'] by (simp add: g_def)
    have w_reach: "w \<in> reach ip.cfg_T_ip (ip.td_sigma_at v0) v0"
      using w_reach' unfolding reach_tree sigma_solve by simp
    show "apply_tf tf a (env u) \<le> env w"
      using ip.td_env_at_edge_step_le_ip[OF cfi join_sym join_is_sup bot_is_bot dom ed w_reach]
      unfolding env_def .
  qed
  have combine_le:
    "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow> combine_abs (env c) (env ex) \<le> env ret"
  proof -
    fix c ex ret
    assume uce: "(c, ex, ret) \<in> combines g"
    have uce': "(c, ex, ret) \<in> combines (compile_prog pi ps main)"
      using uce by (simp add: g_def)
    have w_reach': "ret \<in> reach (make_rhs_tree_ip g tf (\<squnion>) bot s0)
        (TD_plain_Interp_solve (make_rhs_tree_ip g tf (\<squnion>) bot s0) v0) v0"
      using combine_reach[OF uce'] by (simp add: g_def)
    have w_reach: "ret \<in> reach ip.cfg_T_ip (ip.td_sigma_at v0) v0"
      using w_reach' unfolding reach_tree sigma_solve by simp
    show "combine_abs (env c) (env ex) \<le> env ret"
      using ip.td_env_at_combine_le_ip[OF cfi join_sym join_is_sup bot_is_bot dom uce w_reach]
      unfolding env_def .
  qed
  have entry_reach': "cfg_entry g \<in> reach ip.cfg_T_ip (ip.td_sigma_at v0) v0"
  proof -
    have er: "cfg_entry g \<in> reach (make_rhs_tree_ip g tf (\<squnion>) bot s0)
        (TD_plain_Interp_solve (make_rhs_tree_ip g tf (\<squnion>) bot s0) v0) v0"
      using entry_reach by (simp add: g_def)
    show ?thesis using er unfolding reach_tree sigma_solve by simp
  qed
  have entry_le: "s0 \<le> env (cfg_entry g)"
    using ip.td_env_at_entry_le_ip_reach[OF cfi join_sym join_is_sup bot_is_bot dom entry_reach']
    unfolding env_def .
  have collect_le: "cfg_collect_ip g S v0 \<le> gamma_state (env v0)"
  proof (rule post_fixpoint_sound_at_ip)
    show "finite (edges g)" by (rule fin_g)
    show "finite (combines g)" by (rule finC_g)
    show "S \<le> gamma_state s0" by (rule S_sub)
    show "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> apply_tf tf a (env u) \<le> env w"
      by (rule step_le)
    show "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow>
        combine_abs (env c) (env ex) \<le> env ret"
      by (rule combine_le)
    show "s0 \<le> env (cfg_entry g)" by (rule entry_le)
  qed
  show ?thesis
    using collect_le by (simp add: env_def g_def td_analyse_ip_eq_env_at)
qed

(* Exit-rooted soundness with the dead-procedure well-formedness hypothesis
   discharged by pruning (CFG_Prune): the solver runs on the full graph, while
   the collecting value at the exit depends only on the backward cone, which is
   connected by construction.  No `node_reach_exit` assumption. *)
theorem td_analyse_ip_collect_sound_at_exit_pruned:
  fixes pi ps main
  assumes S_sub: "S \<le> gamma_state s0"
  assumes td_solve_dom:
    "TD_plain.solve_dom (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0)
       (cfg_exit (compile_prog pi ps main))"
  shows "cfg_collect_ip (compile_prog pi ps main) S (cfg_exit (compile_prog pi ps main))
         \<le> gamma_state (td_analyse_ip pi ps main tf (\<squnion>) bot s0
              (cfg_exit (compile_prog pi ps main)))"
proof -
  define g where "g = compile_prog pi ps main"
  define v0 where "v0 = cfg_exit g"
  define pg where "pg = prune_cfg g"
  have fin_g: "finite (edges g)" unfolding g_def using compile_prog_finite by simp
  have finC_g: "finite (combines g)" unfolding g_def using compile_prog_finite by simp
  interpret ip: td_cfg_ip_solver g tf "(\<squnion>)" bot s0
    using fin_g finC_g td_cfg_ip_core_def td_cfg_ip_solver.intro by blast
  define env where "env = ip.td_env_at v0"
  have cfi: "comp_fun_idem ((\<squnion>) :: 'a abs_state \<Rightarrow> _ \<Rightarrow> _)"
    by (rule join_state_comp_fun_idem)
  have join_sym: "\<And>x y :: 'a abs_state. x \<squnion> y = y \<squnion> x" by (rule sup.commute)
  have join_is_sup: "(\<squnion>) = (\<squnion>)" by simp
  have bot_is_bot: "bot = bot" by simp
  have cfg_T_ip_fn: "ip.cfg_T_ip = make_rhs_tree_ip g tf (\<squnion>) bot s0"
    by (simp add: ip.cfg_T_ip_def fun_eq_iff)
  have reach_tree: "reach ip.cfg_T_ip = reach (make_rhs_tree_ip g tf (\<squnion>) bot s0)"
    unfolding cfg_T_ip_fn by simp
  have dom: "TD_plain.solve_dom ip.cfg_T_ip v0"
  proof -
    have "TD_plain.solve_dom (make_rhs_tree_ip g tf (\<squnion>) bot s0) v0"
      using td_solve_dom by (simp add: g_def v0_def)
    thus ?thesis unfolding cfg_T_ip_fn by simp
  qed
  have cone_reach:
    "\<And>w. ip_reaches g w v0 \<Longrightarrow> w \<in> reach ip.cfg_T_ip (ip.td_sigma_at v0) v0"
  proof -
    fix w assume "ip_reaches g w v0"
    hence "w \<in> reach (make_rhs_tree_ip g tf (\<squnion>) bot s0) (ip.td_sigma_at v0) v0"
      by (rule ip_reaches_imp_reach[OF fin_g finC_g])
    thus "w \<in> reach ip.cfg_T_ip (ip.td_sigma_at v0) v0" unfolding reach_tree by simp
  qed
  have step_le: "\<And>u a w. (u, a, w) \<in> edges pg \<Longrightarrow> apply_tf tf a (env u) \<le> env w"
  proof -
    fix u a w assume e_pg: "(u, a, w) \<in> edges pg"
    have e_pg2: "(u, a, w) \<in> edges (prune_to g v0)"
      using e_pg by (simp add: pg_def prune_cfg_def v0_def)
    have ed_g: "(u, a, w) \<in> edges g" using e_pg2 edges_prune_to_sub by blast
    have w_cone: "ip_reaches g w v0" using e_pg2 by (simp add: cone_def)
    have w_reach: "w \<in> reach ip.cfg_T_ip (ip.td_sigma_at v0) v0"
      using cone_reach[OF w_cone] .
    show "apply_tf tf a (env u) \<le> env w"
      using ip.td_env_at_edge_step_le_ip[OF cfi join_sym join_is_sup bot_is_bot dom ed_g w_reach]
      unfolding env_def .
  qed
  have combine_le:
    "\<And>c ex ret. (c, ex, ret) \<in> combines pg \<Longrightarrow> combine_abs (env c) (env ex) \<le> env ret"
  proof -
    fix c ex ret assume cmb: "(c, ex, ret) \<in> combines pg"
    have cmb2: "(c, ex, ret) \<in> combines (prune_to g v0)"
      using cmb by (simp add: pg_def prune_cfg_def v0_def)
    have uce_g: "(c, ex, ret) \<in> combines g" using cmb2 combines_prune_to_sub by blast
    have r_cone: "ip_reaches g ret v0" using cmb2 by (simp add: cone_def)
    have r_reach: "ret \<in> reach ip.cfg_T_ip (ip.td_sigma_at v0) v0"
      using cone_reach[OF r_cone] .
    show "combine_abs (env c) (env ex) \<le> env ret"
      using ip.td_env_at_combine_le_ip[OF cfi join_sym join_is_sup bot_is_bot dom uce_g r_reach]
      unfolding env_def .
  qed
  have entry_reach_g: "ip_reaches g (cfg_entry g) v0"
    using compile_prog_entry_ip_reaches_exit by (simp add: g_def v0_def)
  have entry_reach': "cfg_entry g \<in> reach ip.cfg_T_ip (ip.td_sigma_at v0) v0"
    using cone_reach[OF entry_reach_g] .
  have entry_le: "s0 \<le> env (cfg_entry g)"
    using ip.td_env_at_entry_le_ip_reach[OF cfi join_sym join_is_sup bot_is_bot dom entry_reach']
    unfolding env_def .
  have entry_le_pg: "s0 \<le> env (cfg_entry pg)"
    using entry_le by (simp add: pg_def prune_cfg_def)
  have fin_pg: "finite (edges pg)"
    unfolding pg_def prune_cfg_def using finite_edges_prune_to[OF fin_g] .
  have finC_pg: "finite (combines pg)"
    unfolding pg_def prune_cfg_def using finite_combines_prune_to[OF finC_g] .
  have collect_pg: "cfg_collect_ip pg S v0 \<le> gamma_state (env v0)"
  proof (rule post_fixpoint_sound_at_ip)
    show "finite (edges pg)" by (rule fin_pg)
    show "finite (combines pg)" by (rule finC_pg)
    show "S \<le> gamma_state s0" by (rule S_sub)
    show "\<And>u a w. (u, a, w) \<in> edges pg \<Longrightarrow> apply_tf tf a (env u) \<le> env w"
      by (rule step_le)
    show "\<And>c ex ret. (c, ex, ret) \<in> combines pg \<Longrightarrow>
        combine_abs (env c) (env ex) \<le> env ret"
      by (rule combine_le)
    show "s0 \<le> env (cfg_entry pg)" by (rule entry_le_pg)
  qed
  have frame: "cfg_collect_ip g S v0 \<subseteq> cfg_collect_ip pg S v0"
    using cfg_collect_ip_prune_exit[of g S] by (simp add: pg_def v0_def)
  have collect_g: "cfg_collect_ip g S v0 \<le> gamma_state (env v0)"
    using frame collect_pg by blast
  show ?thesis
    using collect_g by (simp add: env_def g_def v0_def td_analyse_ip_eq_env_at)
qed

theorem ip_sign_analysis_sound:
  fixes pi ps main and s t :: store and s0 :: "'a abs_state"
  assumes s_sound: "s \<in> gamma_state s0"
  assumes collect_exit:
    "t \<in> cfg_collect_ip (compile_prog pi ps main) {s}
       (cfg_exit (compile_prog pi ps main))"
  assumes td_solve_dom:
    "TD_plain.solve_dom (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0)
       (cfg_exit (compile_prog pi ps main))"
  shows "t \<in> gamma_state
       (td_analyse_ip pi ps main tf (\<squnion>) bot s0
         (cfg_exit (compile_prog pi ps main)))"
proof -
  have S_sub: "{s} \<le> gamma_state s0" using s_sound by auto
  have collect:
    "cfg_collect_ip (compile_prog pi ps main) {s} (cfg_exit (compile_prog pi ps main))
     \<le> gamma_state (td_analyse_ip pi ps main tf (\<squnion>) bot s0
         (cfg_exit (compile_prog pi ps main)))"
    by (rule td_analyse_ip_collect_sound_at_exit_pruned[OF S_sub td_solve_dom])
  show ?thesis using collect collect_exit by blast
qed

end

(* Domain instantiation: Domains/Sign_IP_Soundness.thy *)

end
