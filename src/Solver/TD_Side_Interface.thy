theory TD_Side_Interface
  imports TD_Side_CFG "TD.TD_side"
begin

(*
  Side-effecting TD backend (TD_side on side_cfg_T).

  Mirrors TD_Interface for the plain solver: package side_cfg_T as cfg_side_T,
  run TD_side_mono.solve, read back sigma / stabl, expose side_env_at.

  Monotonicity of side_cfg_T is derived from transfer-function monotonicity
  (side_cfg_T_is_mono_eq / _mono_sides / _mono_deps in TD_Side_CFG).
*)

definition side_cfg_solve_dom ::
  "cfg \<Rightarrow> 'a::bounded_semilattice_sup_bot domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> pp \<Rightarrow> bool"
where
  "side_cfg_solve_dom g tf bot0 s0 v =
     TD_side.solve_dom destab_opt True (side_cfg_T g tf (\<squnion>) bot0 s0) v"

locale td_cfg_side_solver =
  fixes g :: cfg and
  tf :: "'a::bounded_semilattice_sup_bot domain_transfer" and
  bot0 s0 :: "'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
begin

definition cfg_side_T :: "(pp, unit, 'a abs_state) eqsT"
  where "cfg_side_T = side_cfg_T g tf (\<squnion>) bot0 s0"

lemma cfg_side_T_eq[simp]:
  "cfg_side_T = side_cfg_T g tf (\<squnion>) bot0 s0"
  unfolding cfg_side_T_def by rule

interpretation side: TD_side_mono cfg_side_T
proof (unfold_locales)
  show "is_mono_eq cfg_side_T" unfolding cfg_side_T_def
    by (rule side_cfg_T_is_mono_eq[OF tf_mono])
  show "mono_sides cfg_side_T" unfolding cfg_side_T_def
    by (rule side_cfg_T_mono_sides[OF tf_mono])
  show "mono_deps cfg_side_T" unfolding cfg_side_T_def
    by (rule side_cfg_T_mono_deps)
qed

(* Solver output at query node x: stable set and combined unknown assignment. *)
definition side_stabl_at :: "pp \<Rightarrow> pp set"
  where "side_stabl_at x = fst (side.solve x)"

definition side_sigma_at :: "pp \<Rightarrow> pp + unit \<Rightarrow> 'a abs_state"
  where "side_sigma_at x = snd (side.solve x)"

definition side_env_at :: "pp \<Rightarrow> pp \<Rightarrow> 'a abs_state"
  where "side_env_at x0 v = side_env (side_sigma_at x0) v"

(* Combined env at the CFG entry, queried from the entry node. *)
definition side_env_entry :: "pp \<Rightarrow> 'a abs_state"
  where "side_env_entry v = side_env_at (cfg_entry g) v"

lemma side_sigma_at_solve:
  "side_sigma_at x = snd (side.solve x)"
  unfolding side_sigma_at_def by simp

lemma side_stabl_at_solve:
  "side_stabl_at x = fst (side.solve x)"
  unfolding side_stabl_at_def by simp

lemma side_solve_prod:
  "side.solve x = (side_stabl_at x, side_sigma_at x)"
  unfolding side_stabl_at_def side_sigma_at_def
  by (rule prod_eqI) simp_all

lemma side_part_post_solution_at:
  assumes dom: "side.solve_dom x"
  shows "part_post_solution cfg_side_T x (side_sigma_at x) (side_stabl_at x)"
proof -
  from side.least_partial_post_solution[OF dom side_solve_prod] show ?thesis by simp
qed

lemma side_part_solution_at:
  assumes dom: "side.solve_dom x"
  shows "part_solution cfg_side_T x (side_sigma_at x) (side_stabl_at x)"
  using side.partial_solution[OF dom side_solve_prod] by simp

lemma side_query_in_stabl:
  assumes dom: "side.solve_dom x"
  shows "x \<in> side_stabl_at x"
  using side_part_post_solution_at[OF dom] by auto

lemma side_entry_in_stabl:
  assumes dom: "side.solve_dom (cfg_entry g)"
  shows "cfg_entry g \<in> side_stabl_at (cfg_entry g)"
  using side_query_in_stabl[OF dom] by simp

(* Discharge the pp assumption of TD_Side_Soundness from a successful solve. *)
lemma side_solver_part_post_at_entry:
  assumes dom: "side.solve_dom (cfg_entry g)"
  shows "part_post_solution cfg_side_T (cfg_entry g) (side_sigma_at (cfg_entry g))
           (side_stabl_at (cfg_entry g))"
  using side_part_post_solution_at[OF dom] by simp

lemma side_solver_part_post_at:
  assumes dom: "side.solve_dom v0"
  shows "part_post_solution cfg_side_T v0 (side_sigma_at v0) (side_stabl_at v0)"
  using side_part_post_solution_at[OF dom] by simp

lemma side_solve_dom_eq:
  "side_cfg_solve_dom g tf bot0 s0 v = side.solve_dom v"
  unfolding side_cfg_solve_dom_def cfg_side_T_def by simp

lemma side_solver_part_post_at_cfg:
  assumes "side_cfg_solve_dom g tf bot0 s0 v0"
  shows "part_post_solution cfg_side_T v0 (side_sigma_at v0) (side_stabl_at v0)"
  using side_solver_part_post_at assms unfolding side_solve_dom_eq by simp

lemma side_env_at_eq [simp]:
  "side_env_at x0 v = side_env (side_sigma_at x0) v"
  unfolding side_env_at_def by simp

end

(* Executable-facing name: combined abstract env at each pp (entry query). *)
definition side_analyse ::
    "com
     => 'a::bounded_semilattice_sup_bot domain_transfer
     => 'a abs_state
     => 'a abs_state
     => pp
     => 'a abs_state"
where
  "side_analyse prog tf bot0 s0 v =
     side_env (td_cfg_side_solver.side_sigma_at (to_cfg prog) tf bot0 s0 v) v"

lemma side_analyse_eq_env_at:
  fixes prog and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state" and v :: pp
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  shows "side_analyse prog tf bot0 s0 v =
         td_cfg_side_solver.side_env_at (to_cfg prog) tf bot0 s0 v v"
proof -
  interpret side: td_cfg_side_solver "to_cfg prog" tf bot0 s0
    using tf_mono by unfold_locales
  show ?thesis unfolding side_analyse_def side.side_env_at_eq by simp
qed

end
