theory TD_IP_Soundness
  imports TD_Interface Constraint_System_IP_Sound CFG_Collect_IP_Adeq
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

theorem ip_sign_analysis_sound:
  fixes pi ps main and s t :: store and s0 :: "'a abs_state"
  assumes s_sound: "s \<in> gamma_state s0"
  assumes collect_exit:
    "t \<in> cfg_collect_ip (compile_prog pi ps main) {s}
       (cfg_exit (compile_prog pi ps main))"
  assumes fin_cfg: "finite (edges (compile_prog pi ps main))"
  assumes fin_comb: "finite (combines (compile_prog pi ps main))"
  assumes td_solve_dom:
    "TD_plain.solve_dom (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0)
       (cfg_exit (compile_prog pi ps main))"
  assumes edge_reach:
    "\<And>u a w. (u, a, w) \<in> edges (compile_prog pi ps main)
       \<Longrightarrow> w \<in> reach (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0)
         (TD_plain_Interp_solve (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0)
           (cfg_exit (compile_prog pi ps main))) (cfg_exit (compile_prog pi ps main))"
  assumes combine_reach:
    "\<And>c ex w. (c, ex, w) \<in> combines (compile_prog pi ps main)
       \<Longrightarrow> w \<in> reach (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0)
         (TD_plain_Interp_solve (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0)
           (cfg_exit (compile_prog pi ps main))) (cfg_exit (compile_prog pi ps main))"
  assumes entry_reach:
    "cfg_entry (compile_prog pi ps main)
     \<in> reach (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0)
       (TD_plain_Interp_solve (make_rhs_tree_ip (compile_prog pi ps main) tf (\<squnion>) bot s0)
         (cfg_exit (compile_prog pi ps main))) (cfg_exit (compile_prog pi ps main))"
  shows "t \<in> gamma_state
       (td_analyse_ip pi ps main tf (\<squnion>) bot s0
         (cfg_exit (compile_prog pi ps main)))"
proof -
  have S_sub: "{s} \<le> gamma_state s0" using s_sound by auto
  have collect:
    "cfg_collect_ip (compile_prog pi ps main) {s} (cfg_exit (compile_prog pi ps main))
     \<le> gamma_state (td_analyse_ip pi ps main tf (\<squnion>) bot s0
         (cfg_exit (compile_prog pi ps main)))"
    by (rule td_analyse_ip_collect_sound_at[OF S_sub fin_cfg fin_comb td_solve_dom
          edge_reach combine_reach entry_reach])
  show ?thesis using collect collect_exit by blast
qed

end

(* Domain instantiation: Domains/Sign_IP_Soundness.thy *)

end
