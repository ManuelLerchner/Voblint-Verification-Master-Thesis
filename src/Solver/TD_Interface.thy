theory TD_Interface
  imports TD_CFG_Core TD_CFG_IP_Core "TD.TD_plain" Constraint_System_Sound
          Constraint_System_IP_Sound IMP2_Proc_to_CFG
begin

(* Shared: generic part-solution helper, then interprocedural TD backend. *)

lemma part_solutionD:
  fixes T v0 sigma v
  assumes "part_solution T v0 sigma (reach T sigma v0)" and "v \<in> reach T sigma v0"
  shows "eq T v sigma = mlup sigma v"
  using assms by auto


(* -- Interprocedural TD backend (M1 slice 4) ----------------------- *)

locale td_cfg_ip_solver = td_cfg_ip_core + TD_plain cfg_T_ip
begin

definition td_sigma_at :: "pp \<Rightarrow> (pp, 'a abs_state) map"
where
  "td_sigma_at v0 = TD_plain_Interp_solve cfg_T_ip v0"

definition td_env_at :: "pp \<Rightarrow> pp \<Rightarrow> 'a abs_state"
where
  "td_env_at v0 w = lookup_bot (td_sigma_at v0) w"

lemma td_sigma_at_solve:
  "TD_plain_Interp_solve cfg_T_ip v0 = td_sigma_at v0"
  unfolding td_sigma_at_def by simp

lemma td_plain_part_solution_at:
  assumes dom: "TD_plain.solve_dom cfg_T_ip v0"
  shows "part_solution cfg_T_ip v0 (td_sigma_at v0) (reach cfg_T_ip (td_sigma_at v0) v0)"
proof (rule TD_plain_Interp.partial_correctness)
  show "TD_plain.solve_dom cfg_T_ip v0" by (fact dom)
  show "TD_plain_Interp_solve cfg_T_ip v0 = td_sigma_at v0"
    by (simp add: td_sigma_at_solve)
qed

lemma td_env_at_eq_le:
  assumes dom: "TD_plain.solve_dom cfg_T_ip v0"
  assumes w_reach: "w \<in> reach cfg_T_ip (td_sigma_at v0) v0"
  shows "(eq cfg_T_ip) w (td_sigma_at v0) \<le> mlup (td_sigma_at v0) w"
  using part_solutionD[OF td_plain_part_solution_at[OF dom] w_reach] by simp

lemma td_sigma_at_eq_le_on_reach:
  assumes dom: "TD_plain.solve_dom cfg_T_ip v0"
  assumes v_reach: "v \<in> reach cfg_T_ip (td_sigma_at v0) v0"
  shows "(eq cfg_T_ip) v (td_sigma_at v0) \<le> mlup (td_sigma_at v0) v"
  using td_env_at_eq_le[OF dom v_reach] by simp

lemma td_env_at_rhs_ip_le:
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes dom: "TD_plain.solve_dom cfg_T_ip v0"
  assumes w_reach: "w \<in> reach cfg_T_ip (td_sigma_at v0) v0"
  shows "rhs_ip g tf join_abs bot_abs s0 (td_env_at v0) w \<le> td_env_at v0 w"
proof -
  have eq_le: "(eq cfg_T_ip) w (td_sigma_at v0) \<le> mlup (td_sigma_at v0) w"
    using td_env_at_eq_le[OF dom w_reach] .
  show ?thesis
    using eq_le_mlup_imp_rhs_ip_le[OF cfg_T_ip_eq fin fin_combines cfi join_sym eq_le]
      unfolding td_env_at_def by simp
qed

lemma td_env_at_entry_le_ip:
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes join_is_sup: "join_abs = (\<squnion>)"
  assumes bot_is_bot: "bot_abs = bot"
  assumes dom: "TD_plain.solve_dom cfg_T_ip v0"
  assumes entry_path: "cfg_path g (cfg_entry g) es v0"
  shows "s0 \<le> td_env_at v0 (cfg_entry g)"
proof -
  have entry_reach: "cfg_entry g \<in> reach cfg_T_ip (td_sigma_at v0) v0"
    using cfg_path_node_in_reach_ip[OF entry_path] .
  have rhs_le: "rhs_ip g tf join_abs bot_abs s0 (td_env_at v0) (cfg_entry g)
    \<le> td_env_at v0 (cfg_entry g)"
    using td_env_at_rhs_ip_le[OF cfi join_sym dom entry_reach] .
  have s0_rhs: "s0 \<le> rhs_ip g tf join_abs bot_abs s0 (td_env_at v0) (cfg_entry g)"
    by (smt (verit, ccfv_SIG) bot_is_bot fin fin_combines join_is_sup order_trans rhs_le_rhs_ip
        s0_le_rhs_entry)
  show ?thesis using order_trans[OF s0_rhs rhs_le] .
qed

lemma td_env_at_path_step_le_ip:
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes join_is_sup: "join_abs = (\<squnion>)"
  assumes bot_is_bot: "bot_abs = bot"
  assumes dom: "TD_plain.solve_dom cfg_T_ip v0"
  assumes path: "cfg_path g u ((a, w) # es') v0"
  shows "apply_tf tf a (td_env_at v0 u) \<le> td_env_at v0 w"
proof -
  from path obtain ed: "(u, a, w) \<in> edges g" and p2: "cfg_path g w es' v0"
    by (cases rule: cfg_path.cases) auto
  have w_reach: "w \<in> reach cfg_T_ip (td_sigma_at v0) v0"
    using cfg_path_node_in_reach_ip[OF p2] .
  have le_rhs: "apply_tf tf a (td_env_at v0 u)
    \<le> rhs_ip g tf join_abs bot_abs s0 (td_env_at v0) w"
    using apply_tf_le_rhs_ip[where env="td_env_at v0", OF fin fin_combines ed]
      join_is_sup bot_is_bot by (simp add: join_is_sup bot_is_bot)
  show ?thesis
    using order_trans[OF le_rhs td_env_at_rhs_ip_le[OF cfi join_sym dom w_reach]] .
qed

lemma td_env_at_edge_step_le_ip:
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes join_is_sup: "join_abs = (\<squnion>)"
  assumes bot_is_bot: "bot_abs = bot"
  assumes dom: "TD_plain.solve_dom cfg_T_ip v0"
  assumes ed: "(u, a, w) \<in> edges g"
  assumes w_reach: "w \<in> reach cfg_T_ip (td_sigma_at v0) v0"
  shows "apply_tf tf a (td_env_at v0 u) \<le> td_env_at v0 w"
proof -
  have le_rhs: "apply_tf tf a (td_env_at v0 u)
    \<le> rhs_ip g tf join_abs bot_abs s0 (td_env_at v0) w"
    using apply_tf_le_rhs_ip[where env="td_env_at v0", OF fin fin_combines ed]
      join_is_sup bot_is_bot by (simp add: join_is_sup bot_is_bot)
  show ?thesis
    using order_trans[OF le_rhs td_env_at_rhs_ip_le[OF cfi join_sym dom w_reach]] .
qed

lemma td_env_at_combine_le_ip:
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes join_is_sup: "join_abs = (\<squnion>)"
  assumes bot_is_bot: "bot_abs = bot"
  assumes dom: "TD_plain.solve_dom cfg_T_ip v0"
  assumes uce: "(c, ex, w) \<in> combines g"
  assumes w_reach: "w \<in> reach cfg_T_ip (td_sigma_at v0) v0"
  shows "combine_abs (td_env_at v0 c) (td_env_at v0 ex) \<le> td_env_at v0 w"
proof -
  have le_rhs: "combine_abs (td_env_at v0 c) (td_env_at v0 ex)
    \<le> rhs_ip g tf join_abs bot_abs s0 (td_env_at v0) w"
    using combine_abs_le_rhs_ip[where env="td_env_at v0", OF fin fin_combines uce]
      join_is_sup bot_is_bot
    by (simp add: join_is_sup bot_is_bot)
  show ?thesis
    using order_trans[OF le_rhs td_env_at_rhs_ip_le[OF cfi join_sym dom w_reach]] .
qed

lemma td_env_at_entry_le_ip_reach:
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes join_is_sup: "join_abs = (\<squnion>)"
  assumes bot_is_bot: "bot_abs = bot"
  assumes dom: "TD_plain.solve_dom cfg_T_ip v0"
  assumes entry_reach: "cfg_entry g \<in> reach cfg_T_ip (td_sigma_at v0) v0"
  shows "s0 \<le> td_env_at v0 (cfg_entry g)"
proof -
  have rhs_le: "rhs_ip g tf join_abs bot_abs s0 (td_env_at v0) (cfg_entry g)
    \<le> td_env_at v0 (cfg_entry g)"
    using td_env_at_rhs_ip_le[OF cfi join_sym dom entry_reach] .
  have s0_rhs: "s0 \<le> rhs_ip g tf join_abs bot_abs s0 (td_env_at v0) (cfg_entry g)"
  proof -
    have "s0 \<le> rhs g tf join_abs bot_abs s0 (td_env_at v0) (cfg_entry g)"
      using s0_le_rhs_entry[where env="td_env_at v0", OF fin] join_is_sup bot_is_bot
      by (simp add: join_is_sup bot_is_bot)
    also have "\<dots> \<le> rhs_ip g tf join_abs bot_abs s0 (td_env_at v0) (cfg_entry g)"
      using rhs_le_rhs_ip[OF fin fin_combines] by (simp add: join_is_sup bot_is_bot)
    finally show ?thesis .
  qed
  show ?thesis using order_trans[OF s0_rhs rhs_le] .
qed

(* cfg_env_post_fixpoint_ip_from_solver needs eq \<le> mlup at every pp; TD_plain
   only yields equality on dependency reach from v0.  Soundness at a query node
   should follow the path-based post_fixpoint_sound_at_ip route (see TD_Soundness),
   not this lemma. *)

end

definition td_analyse_ip ::
    "proc_table
     \<Rightarrow> pname list
     \<Rightarrow> pcom
     \<Rightarrow> 'a::bounded_semilattice_sup_bot domain_transfer
     \<Rightarrow> ('a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state
     \<Rightarrow> pp
     \<Rightarrow> 'a abs_state"
where
  "td_analyse_ip pi ps main tf join_abs bot_abs s0 v =
     lookup_bot (TD_plain_Interp_solve
       (make_rhs_tree_ip (compile_prog pi ps main) tf join_abs bot_abs s0) v) v"

lemma td_analyse_ip_def_expand:
  "td_analyse_ip pi ps main tf join_abs bot_abs s0 v =
     lookup_bot (TD_plain_Interp_solve
       (make_rhs_tree_ip (compile_prog pi ps main) tf join_abs bot_abs s0) v) v"
  unfolding td_analyse_ip_def by simp

lemma td_analyse_ip_eq_env_at:
  fixes pi ps main and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bot_abs s0 :: "'a abs_state" and v
  shows "td_analyse_ip pi ps main tf join_abs bot_abs s0 v =
         td_cfg_ip_solver.td_env_at (compile_prog pi ps main) tf join_abs bot_abs s0 v v"
proof -
  interpret ip: td_cfg_ip_solver "compile_prog pi ps main" tf join_abs bot_abs s0
    using compile_prog_finite td_cfg_ip_core_def td_cfg_ip_solver.intro by blast 
  
  show ?thesis
    unfolding td_analyse_ip_def ip.td_env_at_def ip.td_sigma_at_def ip.cfg_T_ip_def by simp
qed

end
