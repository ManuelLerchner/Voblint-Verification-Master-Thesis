theory TD_Interface
  imports TD_CFG_Core "TD.TD_plain" Constraint_System_Sound
begin

(* Plain TD backend (join only, no widening). *)

lemma part_solutionD:
  fixes T v0 sigma v
  assumes "part_solution T v0 sigma (reach T sigma v0)" and "v \<in> reach T sigma v0"
  shows "eq T v sigma = mlup sigma v"
  using assms by auto

locale td_cfg_plain_solver = td_cfg_core + TD_plain cfg_T
begin

definition td_sigma_at :: "pp \<Rightarrow> (pp, 'a abs_state) map"
where
  "td_sigma_at v0 = TD_plain_Interp_solve cfg_T v0"

definition td_env_at :: "pp \<Rightarrow> pp \<Rightarrow> 'a abs_state"
where
  "td_env_at v0 w = lookup_bot (td_sigma_at v0) w"

lemma td_sigma_at_solve:
  "TD_plain_Interp_solve cfg_T v0 = td_sigma_at v0"
  unfolding td_sigma_at_def by simp

lemma td_plain_part_solution_at:
  assumes dom: "TD_plain.solve_dom cfg_T v0"
  shows "part_solution cfg_T v0 (td_sigma_at v0) (reach cfg_T (td_sigma_at v0) v0)"
proof (rule TD_plain_Interp.partial_correctness)
  show "TD_plain.solve_dom cfg_T v0"
    by (fact dom)
  show "TD_plain_Interp_solve cfg_T v0 = td_sigma_at v0"
    by (simp add: td_sigma_at_solve)
qed

lemma td_env_at_eq_le:
  assumes dom: "TD_plain.solve_dom cfg_T v0"
  assumes w_reach: "w \<in> reach cfg_T (td_sigma_at v0) v0"
  shows "(eq cfg_T) w (td_sigma_at v0) \<le> mlup (td_sigma_at v0) w"
  using part_solutionD[OF td_plain_part_solution_at[OF dom] w_reach] by simp

lemma td_env_at_rhs_le:
  assumes fin: "finite (edges g)"
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes dom: "TD_plain.solve_dom cfg_T v0"
  assumes w_reach: "w \<in> reach cfg_T (td_sigma_at v0) v0"
  shows "rhs g tf join_abs bot_abs s0 (td_env_at v0) w \<le> td_env_at v0 w"
proof -
  have eq_le: "(eq cfg_T) w (td_sigma_at v0) \<le> mlup (td_sigma_at v0) w"
    using td_env_at_eq_le[OF dom w_reach] .
  show ?thesis
    using eq_le_mlup_imp_rhs_le[OF cfg_T_eq fin cfi join_sym eq_le]
    unfolding td_env_at_def by simp
qed

lemma td_env_at_entry_le:
  assumes fin: "finite (edges g)"
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes join_is_sup: "join_abs = (\<squnion>)"
  assumes bot_is_bot: "bot_abs = bot"
  assumes dom: "TD_plain.solve_dom cfg_T v0"
  assumes entry_path: "cfg_path g (cfg_entry g) es v0"
  shows "s0 \<le> td_env_at v0 (cfg_entry g)"
proof -
  have entry_reach: "cfg_entry g \<in> reach cfg_T (td_sigma_at v0) v0"
    using cfg_path_node_in_reach[OF fin entry_path] .
  have rhs_le: "rhs g tf join_abs bot_abs s0 (td_env_at v0) (cfg_entry g)
    \<le> td_env_at v0 (cfg_entry g)"
    using td_env_at_rhs_le[OF fin cfi join_sym dom entry_reach] .
  have s0_rhs: "s0 \<le> rhs g tf join_abs bot_abs s0 (td_env_at v0) (cfg_entry g)"
    using s0_le_rhs_entry[where env="td_env_at v0", OF fin] join_is_sup bot_is_bot
    by (simp add: join_is_sup bot_is_bot)
  show ?thesis
    using order_trans[OF s0_rhs rhs_le] .
qed

lemma td_env_at_path_step_le:
  assumes fin: "finite (edges g)"
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes join_is_sup: "join_abs = (\<squnion>)"
  assumes bot_is_bot: "bot_abs = bot"
  assumes dom: "TD_plain.solve_dom cfg_T v0"
  assumes path: "cfg_path g u ((a, w) # es') v0"
  shows "apply_tf tf a (td_env_at v0 u) \<le> td_env_at v0 w"
proof -
  from path obtain ed: "(u, a, w) \<in> edges g" and p2: "cfg_path g w es' v0"
    by (cases rule: cfg_path.cases) auto
  have w_reach: "w \<in> reach cfg_T (td_sigma_at v0) v0"
    using cfg_path_node_in_reach[OF fin p2] .
  have le_rhs: "apply_tf tf a (td_env_at v0 u)
    \<le> rhs g tf join_abs bot_abs s0 (td_env_at v0) w"
    using apply_tf_le_rhs[where env="td_env_at v0", OF fin ed] join_is_sup bot_is_bot
    by (simp add: join_is_sup bot_is_bot)
  show ?thesis
    using order_trans[OF le_rhs td_env_at_rhs_le[OF fin cfi join_sym dom w_reach]] .
qed

end

definition td_analyse ::
    "com
     => 'a::bot domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state
     => pp => 'a abs_state"
where
  "td_analyse c tf join_abs bot_abs s0 v =
     lookup_bot (TD_plain_Interp_solve (make_rhs_tree (to_cfg c) tf join_abs bot_abs s0) v) v"

lemma td_analyse_def_expand:
  "td_analyse c tf join_abs bot_abs s0 v =
     lookup_bot (TD_plain_Interp_solve (make_rhs_tree (to_cfg c) tf join_abs bot_abs s0) v) v"
  unfolding td_analyse_def by simp

lemma td_analyse_eq_env_at:
  fixes c and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bot_abs s0 :: "'a abs_state" and v
  shows "td_analyse c tf join_abs bot_abs s0 v =
         td_cfg_plain_solver.td_env_at (to_cfg c) tf join_abs bot_abs s0 v v"
proof -
  interpret plain: td_cfg_plain_solver "to_cfg c" tf join_abs bot_abs s0 .
  show ?thesis
    unfolding td_analyse_def plain.td_env_at_def plain.td_sigma_at_def plain.cfg_T_def by simp
qed

end
