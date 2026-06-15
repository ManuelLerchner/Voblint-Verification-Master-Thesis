theory TD_Side_IP_Interface
  imports TD_Side_IP_Bounds "TD.TD_side"
begin

section \<open>Side IP solver: TD_side backend interface\<close>

text \<open>
  Side-effecting TD backend for the interprocedural CFG (TD_side on
  side_cfg_T_ip).  Packages side_cfg_T_ip as cfg_side_T_ip_pkg, interprets it
  as TD_side_mono, reads back the stable set and unknown assignment
  (side_stabl_at / side_nu_at), and exposes the combined env (side_env_at).

  Monotonicity of side_cfg_T_ip is derived from transfer-function monotonicity
  (side_cfg_T_ip_is_mono_eq / _mono_sides / _mono_deps in TD_Side_IP_Mono).
\<close>

definition side_cfg_ip_solve_dom ::
  "cfg \<Rightarrow> 'a::bounded_semilattice_sup_bot domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> pp \<Rightarrow> bool"
where
  "side_cfg_ip_solve_dom g tf bot0 s0 v =
     TD_side.solve_dom destab_opt True (side_cfg_T_ip g tf (\<squnion>) bot0 s0) v"

locale td_cfg_side_ip_solver =
  fixes g :: cfg and
  tf :: "'a::bounded_semilattice_sup_bot domain_transfer" and
  bot0 s0 :: "'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
begin

definition cfg_side_T_ip_pkg :: "(pp, unit, 'a abs_state) eqsT"
  where "cfg_side_T_ip_pkg = side_cfg_T_ip g tf (\<squnion>) bot0 s0"

lemma cfg_side_T_ip_pkg_eq[simp]:
  "cfg_side_T_ip_pkg = side_cfg_T_ip g tf (\<squnion>) bot0 s0"
  unfolding cfg_side_T_ip_pkg_def by rule

interpretation side: TD_side_mono cfg_side_T_ip_pkg
proof (unfold_locales)
  show "is_mono_eq cfg_side_T_ip_pkg" unfolding cfg_side_T_ip_pkg_def
    by (rule side_cfg_T_ip_is_mono_eq[OF tf_mono])
  show "mono_sides cfg_side_T_ip_pkg" unfolding cfg_side_T_ip_pkg_def
    by (rule side_cfg_T_ip_mono_sides[OF tf_mono])
  show "mono_deps cfg_side_T_ip_pkg" unfolding cfg_side_T_ip_pkg_def
    by (rule side_cfg_T_ip_mono_deps)
qed

(* Solver output at query node x: stable set and combined unknown assignment. *)
definition side_stabl_at :: "pp \<Rightarrow> pp set"
  where "side_stabl_at x = fst (side.solve x)"

definition side_nu_at :: "pp \<Rightarrow> pp + unit \<Rightarrow> 'a abs_state"
  where "side_nu_at x = snd (side.solve x)"

definition side_env_at :: "pp \<Rightarrow> pp \<Rightarrow> 'a abs_state"
  where "side_env_at x0 v = side_env (side_nu_at x0) v"

(* Combined env at the CFG entry, queried from the entry node. *)
definition side_env_entry :: "pp \<Rightarrow> 'a abs_state"
  where "side_env_entry v = side_env_at (cfg_entry g) v"

lemma side_nu_at_solve:
  "side_nu_at x = snd (side.solve x)"
  unfolding side_nu_at_def by simp

lemma side_stabl_at_solve:
  "side_stabl_at x = fst (side.solve x)"
  unfolding side_stabl_at_def by simp

lemma side_solve_prod:
  "side.solve x = (side_stabl_at x, side_nu_at x)"
  unfolding side_stabl_at_def side_nu_at_def
  by (rule prod_eqI) simp_all

lemma side_part_post_solution_at:
  assumes dom: "side.solve_dom x"
  shows "part_post_solution cfg_side_T_ip_pkg x (side_nu_at x) (side_stabl_at x)"
proof -
  from side.least_partial_post_solution[OF dom side_solve_prod] show ?thesis by simp
qed

lemma side_part_solution_at:
  assumes dom: "side.solve_dom x"
  shows "part_solution cfg_side_T_ip_pkg x (side_nu_at x) (side_stabl_at x)"
  using side.partial_solution[OF dom side_solve_prod] by simp

lemma side_query_in_stabl:
  assumes dom: "side.solve_dom x"
  shows "x \<in> side_stabl_at x"
  using side_part_post_solution_at[OF dom] by auto

lemma side_entry_in_stabl:
  assumes dom: "side.solve_dom (cfg_entry g)"
  shows "cfg_entry g \<in> side_stabl_at (cfg_entry g)"
  using side_query_in_stabl[OF dom] by simp

lemma side_solver_part_post_at_entry:
  assumes dom: "side.solve_dom (cfg_entry g)"
  shows "part_post_solution cfg_side_T_ip_pkg (cfg_entry g) (side_nu_at (cfg_entry g))
           (side_stabl_at (cfg_entry g))"
  using side_part_post_solution_at[OF dom] by simp

lemma side_solver_part_post_at:
  assumes dom: "side.solve_dom v0"
  shows "part_post_solution cfg_side_T_ip_pkg v0 (side_nu_at v0) (side_stabl_at v0)"
  using side_part_post_solution_at[OF dom] by simp

lemma side_solve_dom_eq:
  "side_cfg_ip_solve_dom g tf bot0 s0 v = side.solve_dom v"
  unfolding side_cfg_ip_solve_dom_def cfg_side_T_ip_pkg_def by simp

lemma side_solver_part_post_at_cfg:
  assumes "side_cfg_ip_solve_dom g tf bot0 s0 v0"
  shows "part_post_solution cfg_side_T_ip_pkg v0 (side_nu_at v0) (side_stabl_at v0)"
  using side_solver_part_post_at assms unfolding side_solve_dom_eq by simp

lemma side_env_at_eq [simp]:
  "side_env_at x0 v = side_env (side_nu_at x0) v"
  unfolding side_env_at_def by simp

end

(* Executable-facing name: combined abstract env at each pp (entry query). *)
definition side_analyse_ip ::
    "proc_table
     \<Rightarrow> pname list
     \<Rightarrow> com
     => 'a::bounded_semilattice_sup_bot domain_transfer
     => 'a abs_state
     => 'a abs_state
     => pp
     => 'a abs_state"
where
  "side_analyse_ip \<Pi> ps main tf bot0 s0 v =
     side_env (td_cfg_side_ip_solver.side_nu_at (compile_prog \<Pi> ps main) tf bot0 s0 v) v"

lemma side_analyse_ip_eq_env_at:
  fixes \<Pi> ps main and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state" and v :: pp
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  shows "side_analyse_ip \<Pi> ps main tf bot0 s0 v =
         td_cfg_side_ip_solver.side_env_at (compile_prog \<Pi> ps main) tf bot0 s0 v v"
proof -
  interpret side: td_cfg_side_ip_solver "compile_prog \<Pi> ps main" tf bot0 s0
    using tf_mono by unfold_locales
  show ?thesis unfolding side_analyse_ip_def side.side_env_at_eq by simp
qed

end
