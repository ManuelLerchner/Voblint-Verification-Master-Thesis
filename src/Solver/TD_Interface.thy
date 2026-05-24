theory TD_Interface
  imports TD_CFG_Core "TD.TD_plain"
begin

(* Plain TD backend (join only, no widening). *)

lemma part_solutionD:
  fixes T v0 sigma v
  assumes "part_solution T v0 sigma (reach T sigma v0)" and "v \<in> reach T sigma v0"
  shows "eq T v sigma = mlup sigma v"
  using assms by auto

locale td_cfg_plain_solver = td_cfg_core + TD_plain cfg_T
begin

definition td_sigma :: "(pp, 'a abs_state) map"
where
  "td_sigma = TD_plain_Interp_solve cfg_T (cfg_entry g)"

definition td_env :: "pp \<Rightarrow> 'a abs_state"
where
  "td_env v = lookup_bot td_sigma v"

lemma td_sigma_solve:
  "TD_plain_Interp_solve cfg_T (cfg_entry g) = td_sigma"
  unfolding td_sigma_def by simp

lemma td_plain_part_solution:
  assumes dom: "TD_plain.solve_dom cfg_T (cfg_entry g)"
  shows "part_solution cfg_T (cfg_entry g) td_sigma (reach cfg_T td_sigma (cfg_entry g))"
proof (rule TD_plain_Interp.partial_correctness)
  show "TD_plain.solve_dom cfg_T (cfg_entry g)"
    by (fact dom)
  show "TD_plain_Interp_solve cfg_T (cfg_entry g) = td_sigma"
    by (simp add: td_sigma_solve)
qed

lemma td_env_post_fixpoint:
  assumes fin: "finite (edges g)"
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes dom: "TD_plain.solve_dom cfg_T (cfg_entry g)"
  assumes reach: "\<And>v. v \<in> reach cfg_T td_sigma (cfg_entry g)"
  shows "is_post_fixpoint g tf join_abs bot_abs s0 td_env"
proof (rule cfg_env_post_fixpoint[where env=td_env and \<sigma>=td_sigma, OF fin cfi join_sym])
  show "\<And>w. td_env w = lookup_bot td_sigma w"
    unfolding td_env_def by simp
next
  fix v
  show "(eq cfg_T) v td_sigma \<le> mlup td_sigma v"
  proof -
    have v_reach: "v \<in> reach cfg_T td_sigma (cfg_entry g)"
      using reach by simp
    have psol: "part_solution cfg_T (cfg_entry g) td_sigma (reach cfg_T td_sigma (cfg_entry g))"
      using td_plain_part_solution[OF dom] .
    show ?thesis
      using part_solutionD[OF psol v_reach] by simp
  qed
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
     lookup_bot (TD_plain_Interp_solve (make_rhs_tree (to_cfg c) tf join_abs bot_abs s0)
                   (cfg_entry (to_cfg c))) v"

lemma td_analyse_def_expand:
  "td_analyse c tf join_abs bot_abs s0 v =
     lookup_bot (TD_plain_Interp_solve (make_rhs_tree (to_cfg c) tf join_abs bot_abs s0)
                   (cfg_entry (to_cfg c))) v"
  unfolding td_analyse_def by simp

theorem td_analyse_post_fixpoint:
  fixes c tf join_abs bot_abs s0
  assumes fin: "finite (edges (to_cfg c))"
  assumes cfi: "comp_fun_idem (join_abs :: 'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes solve_dom:
    "TD_plain.solve_dom (make_rhs_tree (to_cfg c) tf join_abs bot_abs s0) (cfg_entry (to_cfg c))"
  assumes cfg_in_reach:
    "\<And>v::pp. v \<in> reach (make_rhs_tree (to_cfg c) tf join_abs bot_abs s0)
                    (TD_plain_Interp_solve (make_rhs_tree (to_cfg c) tf join_abs bot_abs s0)
                      (cfg_entry (to_cfg c)))
                    (cfg_entry (to_cfg c))"
  shows "is_post_fixpoint (to_cfg c) tf join_abs bot_abs s0
           (td_analyse c tf join_abs bot_abs s0)"
proof -
  interpret plain: td_cfg_plain_solver "to_cfg c" tf join_abs bot_abs s0 .
  have dom': "TD_plain.solve_dom plain.cfg_T (cfg_entry (to_cfg c))"
  proof -
    have "plain.cfg_T = make_rhs_tree (to_cfg c) tf join_abs bot_abs s0"
      by (simp add: fun_eq_iff plain.cfg_T_eq)
    then show ?thesis using solve_dom by simp
  qed
  have cfg_T: "plain.cfg_T = make_rhs_tree (to_cfg c) tf join_abs bot_abs s0"
    by (simp add: fun_eq_iff plain.cfg_T_eq)
  have env_eq: "td_analyse c tf join_abs bot_abs s0 = plain.td_env"
    unfolding td_analyse_def plain.td_env_def plain.td_sigma_def
    using cfg_T
    by (intro ext, simp)  have reach': "\<And>v. v \<in> reach plain.cfg_T plain.td_sigma (cfg_entry (to_cfg c))"
    using cfg_in_reach
    by (simp add: plain.td_sigma_def cfg_T fun_eq_iff)
  show ?thesis
    unfolding env_eq
    using plain.td_env_post_fixpoint[OF fin cfi join_sym dom' reach'] .
qed

end
