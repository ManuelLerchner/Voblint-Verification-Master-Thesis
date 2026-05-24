theory TD_Widen_Interface
  imports TD_CFG_Core "TD.TD_plain_widen"
begin

(*
  Middle step: TD_plain_widen (widening at dynamic points, no narrowing phases).

  TD_plain_widen fixes T :: pp => (pp, 'd) strategy_tree with 'd :: bounded_lattice_bot.
  Do not put  T v = make_rhs_tree ... v  in the locale header: that forces
  'd = 'a abs_state (= vname => 'a), which needs bounded_lattice (inf+sup) on 'a.
  Sign/interval today only have bounded_semilattice_sup_bot.

  Instantiate with T = make_rhs_tree g tf join_abs bot_abs s0 once 'a abs_state
  is bounded_lattice_bot (interval + inf instance).
*)

definition widen_abs ::
    "('a::bounded_lattice_bot \<Rightarrow> 'a \<Rightarrow> 'a)
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state"
where
  "widen_abs widen s1 s2 x = widen (s1 x) (s2 x)"

lemma widen_abs_ge:
  fixes widen :: "'a::bounded_lattice_bot \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes "\<And>a b. a \<squnion> b \<le> widen a b"
  shows "s1 \<squnion> s2 \<le> widen_abs widen s1 s2"
  unfolding widen_abs_def le_fun_def
proof (intro allI)
  fix x
  show "(s1 \<squnion> s2) x \<le> widen (s1 x) (s2 x)"
    using assms[of "s1 x" "s2 x"] by simp
qed

locale td_cfg_plain_widen_solver = TD_plain_widen T widening
for
  g :: cfg and
  tf :: "'a::bounded_semilattice_sup_bot domain_transfer" and
  join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" and
  bot_abs s0 :: "'a abs_state" and
  T :: "pp \<Rightarrow> (pp, 'd :: bounded_lattice_bot) strategy_tree" and
  widening :: "'d \<Rightarrow> 'd \<Rightarrow> 'd"
begin

definition td_widen_sigma :: "(pp, 'd) map"
where
  "td_widen_sigma = solve (cfg_entry g)"

definition td_widen_env :: "pp \<Rightarrow> 'd"
where
  "td_widen_env v = lookup_bot td_widen_sigma v"

lemma td_widen_post_on_reach:
  assumes dom: "solve_dom (cfg_entry g)"
  assumes sol: "solve (cfg_entry g) = td_widen_sigma"
  shows "\<And>v. v \<in> reach T td_widen_sigma (cfg_entry g)
           \<Longrightarrow> (eq T) v td_widen_sigma \<le> mlup td_widen_sigma v"
proof -
  have post: "part_post_solution td_widen_sigma (reach T td_widen_sigma (cfg_entry g))"
    using partial_correctness[OF dom sol] .
  show "\<And>v. v \<in> reach T td_widen_sigma (cfg_entry g)
           \<Longrightarrow> (eq T) v td_widen_sigma \<le> mlup td_widen_sigma v"
    using post by blast
qed

end

end
