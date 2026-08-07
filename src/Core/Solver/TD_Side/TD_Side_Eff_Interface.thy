theory TD_Side_Eff_Interface
  imports TD_Side_Tree "TD.TD_side"
begin

section \<open>Effectful side IP solver: TD_side backend interface\<close>

text \<open>
  TD_side backend for the effectful interprocedural equation system
  (side_cfg_T_eff).  The locale fixes an effectful_domain_transfer and assumes
  the three TD_side preconditions on side_cfg_T_eff directly.
\<close>

definition side_cfg_solve_dom_eff ::
  "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g \<Rightarrow> pp \<Rightarrow> bool"
where
  "side_cfg_solve_dom_eff gs g etf bot0 s0 gseed v =
     TD_side.solve_dom destab_opt True (side_cfg_T_eff gs g etf bot0 s0 gseed) v"

locale td_cfg_side_solver_eff =
  fixes gs :: "vname \<Rightarrow> bool" and g :: cfg and
  etf :: "('g::finite, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer" and
  bot0 s0 :: "'a abs_state" and gseed :: 'g
  assumes mono_eq[intro]:    "is_mono_eq (side_cfg_T_eff gs g etf bot0 s0 gseed)"
    and   mono_sides[intro]: "mono_sides (side_cfg_T_eff gs g etf bot0 s0 gseed)"
    and   mono_deps[intro]:  "mono_deps (side_cfg_T_eff gs g etf bot0 s0 gseed)"
begin

definition cfg_pkg_eff :: "(pp, 'g, 'a abs_state) eqsT"
  where "cfg_pkg_eff = side_cfg_T_eff gs g etf bot0 s0 gseed"

lemma cfg_pkg_eff_eq[simp]: "cfg_pkg_eff = side_cfg_T_eff gs g etf bot0 s0 gseed"
  unfolding cfg_pkg_eff_def by rule

interpretation side: TD_side_mono cfg_pkg_eff
proof (unfold_locales)
  show "is_mono_eq cfg_pkg_eff" unfolding cfg_pkg_eff_def by (rule mono_eq)
  show "mono_sides cfg_pkg_eff" unfolding cfg_pkg_eff_def by (rule mono_sides)
  show "mono_deps cfg_pkg_eff" unfolding cfg_pkg_eff_def by (rule mono_deps)
qed

definition stabl_at :: "pp \<Rightarrow> pp set"
  where "stabl_at x = fst (side.solve x)"

definition nu_at :: "pp \<Rightarrow> pp + 'g \<Rightarrow> 'a abs_state"
  where "nu_at x = snd (side.solve x)"

definition env_at :: "pp \<Rightarrow> pp \<Rightarrow> 'a abs_state"
  where "env_at x0 v = side_env (nu_at x0) v"

lemma solve_prod: "side.solve x = (stabl_at x, nu_at x)"
  unfolding stabl_at_def nu_at_def by (rule prod_eqI) simp_all

lemma part_post_at:
  assumes dom: "side.solve_dom x"
  shows "part_post_solution cfg_pkg_eff x (nu_at x) (stabl_at x)"
  using side.least_partial_post_solution[OF dom solve_prod] by simp

lemma solve_dom_eq:
  "side_cfg_solve_dom_eff gs g etf bot0 s0 gseed v = side.solve_dom v"
  unfolding side_cfg_solve_dom_eff_def cfg_pkg_eff_def by simp

lemma part_post_at_cfg:
  assumes "side_cfg_solve_dom_eff gs g etf bot0 s0 gseed v"
  shows "part_post_solution cfg_pkg_eff v (nu_at v) (stabl_at v)"
  using part_post_at assms unfolding solve_dom_eq by simp

lemma least_part_post_at_cfg:
  assumes dom: "side_cfg_solve_dom_eff gs g etf bot0 s0 gseed v"
  shows "least_part_post_solution cfg_pkg_eff v (nu_at v) (stabl_at v)"
proof -
  have dv: "side.solve_dom v" using dom unfolding solve_dom_eq .  show ?thesis
    using side.least_partial_post_solution[OF dv solve_prod] by blast
qed

lemma env_at_eq [simp]: "env_at x0 v = side_env (nu_at x0) v"
  unfolding env_at_def by simp

end

text \<open>Executable-facing combined env at each pp (entry query).\<close>
definition side_analyse_eff ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
     \<Rightarrow> ('g::finite, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
     \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g \<Rightarrow> pp \<Rightarrow> 'a abs_state"
where
  "side_analyse_eff gs \<Pi> ps mnm main etf bot0 s0 gseed v =
     side_env (td_cfg_side_solver_eff.nu_at gs (compile_prog \<Pi> ps mnm main) etf bot0 s0 gseed v) v"

end

