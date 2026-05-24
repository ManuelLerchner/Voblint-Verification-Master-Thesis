theory TD_WN_Interface
  imports TD_CFG_Core "TD.TD_wn_post"
begin

(*
  Full W/N backend (TD_wn_post): widening and narrowing phases, destabilization.
  Uses TD_CFG_Core for make_rhs_tree and is_post_fixpoint readback.
*)

definition widen_abs ::
    "('a::bounded_lattice \<Rightarrow> 'a \<Rightarrow> 'a)
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state"
where
  "widen_abs widen s1 s2 x = widen (s1 x) (s2 x)"

definition narrow_abs ::
    "('a::bounded_lattice \<Rightarrow> 'a \<Rightarrow> 'a)
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state"
where
  "narrow_abs narrow s1 s2 x = narrow (s1 x) (s2 x)"

lemma widen_abs_ge:
  fixes widen :: "'a::bounded_lattice \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes "\<And>a b. a \<squnion> b \<le> widen a b"
  shows "s1 \<squnion> s2 \<le> widen_abs widen s1 s2"
  unfolding widen_abs_def le_fun_def
proof (intro allI)
  fix x
  show "(s1 \<squnion> s2) x \<le> widen (s1 x) (s2 x)"
    using assms[of "s1 x" "s2 x"] by simp
qed

lemma narrow_abs_ge:
  fixes narrow :: "'a::bounded_lattice \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes "\<And>a b. a \<sqinter> b \<le> narrow a b"
  shows "s1 \<sqinter> s2 \<le> narrow_abs narrow s1 s2"
  unfolding narrow_abs_def le_fun_def
proof (intro allI)
  fix x
  show "(s1 \<sqinter> s2) x \<le> narrow (s1 x) (s2 x)"
    using assms[of "s1 x" "s2 x"] by simp
qed

lemma narrow_abs_le:
  fixes narrow :: "'a::bounded_lattice \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes "\<And>a b. narrow a b \<le> a"
  shows "narrow_abs narrow s1 s2 \<le> s1"
  unfolding narrow_abs_def le_fun_def by (simp add: assms)

lemma reach_in_stabl:
  fixes T :: "pp \<Rightarrow> (pp, 'd::order_bot) strategy_tree" and x :: pp and stabl :: "pp set"
    and sigma :: "(pp, 'd) map"
  assumes post: "part_post_solution T x sigma stabl"
  assumes x_in: "x \<in> stabl"
  assumes v_reach: "v \<in> reach T sigma x"
  shows "v \<in> stabl"
  using v_reach proof induct
  case base
  then show ?case using x_in by simp
next
  case (step y z)
  then have y_stabl: "y \<in> stabl" by simp
  then have "dep T sigma y \<subseteq> stabl"
    by (simp add: post)
  then show ?case using step.hyps(3) by auto
qed

locale td_cfg_wn_solver =
  fixes g :: cfg and
  tf :: "'a::bounded_lattice domain_transfer" and
  join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" and
  bot_abs s0 :: "'a abs_state" and
  widen narrow :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes widen_ge: "s1 \<squnion> s2 \<le> widen s1 s2"
  assumes widen_bounded: "s2 \<le> s1 \<Longrightarrow> widen s1 s2 = s1"
  assumes narrow_ge: "s1 \<sqinter> s2 \<le> narrow s1 s2"
  assumes narrow_le: "narrow s1 s2 \<le> s1"
begin

definition cfg_T :: "pp \<Rightarrow> (pp, 'a abs_state) strategy_tree"
where
  "cfg_T v = make_rhs_tree g tf join_abs bot_abs s0 v"

interpretation td_wn: TD_wn_post cfg_T widen narrow
  using TD_wn_post.intro narrow_ge narrow_le widen_bounded widen_ge by blast

definition td_wn_sigma :: "(pp, 'a abs_state) map"
where
  "td_wn_sigma = snd (td_wn.solve (cfg_entry g))"

definition td_wn_env :: "pp \<Rightarrow> 'a abs_state"
where
  "td_wn_env v = lookup_bot td_wn_sigma v"

lemma td_wn_eq_le_on_reach:
  fixes stabl :: "pp set" and sigma :: "(pp, 'a abs_state) map"
  assumes mono: "is_mono_eq cfg_T"
  assumes deps: "mono_deps cfg_T"
  assumes dom: "td_wn.solve_dom (cfg_entry g)"
  assumes sol: "td_wn.solve (cfg_entry g) = (stabl, sigma)"
  assumes v_reach: "v \<in> reach cfg_T sigma (cfg_entry g)"
  shows "(eq cfg_T) v sigma \<le> mlup sigma v"
proof -
  have post: "part_post_solution cfg_T (cfg_entry g) sigma stabl"
    using td_wn.partial_correctness[OF mono deps dom sol] by simp
  then have entry_stabl: "cfg_entry g \<in> stabl" by blast
  have v_stabl: "v \<in> stabl"
    using post reach_in_stabl v_reach entry_stabl by blast
  show ?thesis using post v_stabl by fastforce
qed

lemma td_wn_env_post_fixpoint:
  assumes fin: "finite (edges g)"
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes mono: "is_mono_eq cfg_T"
  assumes deps: "mono_deps cfg_T"
  assumes dom: "td_wn.solve_dom (cfg_entry g)"
  assumes reach: "\<And>v. v \<in> reach cfg_T td_wn_sigma (cfg_entry g)"
  shows "is_post_fixpoint g tf join_abs bot_abs s0 td_wn_env"
proof -
  obtain stabl sigma where sol: "td_wn.solve (cfg_entry g) = (stabl, sigma)"
    and sigma_eq: "td_wn_sigma = sigma"
    unfolding td_wn_sigma_def by (metis prod.collapse)
  show ?thesis
    using cfg_env_post_fixpoint[where T=cfg_T, OF cfg_T_def fin cfi join_sym]
    using deps dom mono reach sigma_eq sol td_wn_env_def td_wn_eq_le_on_reach by blast
qed

end

end
