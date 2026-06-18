theory TD_Side_IP_Eff_Interface
  imports TD_Side_IP_Mono TD_Side_IP_Interface TD_Side_IP_Soundness "TD.TD_side"
begin

section \<open>Effectful side IP solver: TD_side backend interface\<close>

text \<open>
  TD_side backend for the effectful interprocedural equation system
  (side_cfg_T_ip_eff).  Mirrors td_cfg_side_ip_solver but fixes an
  effectful_domain_transfer and assumes the three TD_side preconditions on
  side_cfg_T_ip_eff directly (a non-shim etf supplies them from the monad lemmas;
  the pure shim from side_cfg_T_ip_eff_etf_from_tf).
\<close>

definition side_cfg_ip_solve_dom_eff ::
  "cfg \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> pp \<Rightarrow> bool"
where
  "side_cfg_ip_solve_dom_eff g etf bot0 s0 v =
     TD_side.solve_dom destab_opt True (side_cfg_T_ip_eff g etf bot0 s0) v"

locale td_cfg_side_ip_solver_eff =
  fixes g :: cfg and
  etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer" and
  bot0 s0 :: "'a abs_state"
  assumes mono_eq:    "is_mono_eq (side_cfg_T_ip_eff g etf bot0 s0)"
    and   mono_sides: "mono_sides (side_cfg_T_ip_eff g etf bot0 s0)"
    and   mono_deps:  "mono_deps (side_cfg_T_ip_eff g etf bot0 s0)"
begin

definition cfg_pkg_eff :: "(pp, unit, 'a abs_state) eqsT"
  where "cfg_pkg_eff = side_cfg_T_ip_eff g etf bot0 s0"

lemma cfg_pkg_eff_eq[simp]: "cfg_pkg_eff = side_cfg_T_ip_eff g etf bot0 s0"
  unfolding cfg_pkg_eff_def by rule

interpretation side: TD_side_mono cfg_pkg_eff
proof (unfold_locales)
  show "is_mono_eq cfg_pkg_eff" unfolding cfg_pkg_eff_def by (rule mono_eq)
  show "mono_sides cfg_pkg_eff" unfolding cfg_pkg_eff_def by (rule mono_sides)
  show "mono_deps cfg_pkg_eff" unfolding cfg_pkg_eff_def by (rule mono_deps)
qed

definition stabl_at :: "pp \<Rightarrow> pp set"
  where "stabl_at x = fst (side.solve x)"

definition nu_at :: "pp \<Rightarrow> pp + unit \<Rightarrow> 'a abs_state"
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
  "side_cfg_ip_solve_dom_eff g etf bot0 s0 v = side.solve_dom v"
  unfolding side_cfg_ip_solve_dom_eff_def cfg_pkg_eff_def by simp

lemma part_post_at_cfg:
  assumes "side_cfg_ip_solve_dom_eff g etf bot0 s0 v"
  shows "part_post_solution cfg_pkg_eff v (nu_at v) (stabl_at v)"
  using part_post_at assms unfolding solve_dom_eq by simp

lemma env_at_eq [simp]: "env_at x0 v = side_env (nu_at x0) v"
  unfolding env_at_def by simp

end

text \<open>Executable-facing combined env at each pp (entry query).\<close>
definition side_analyse_ip_eff ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com
     \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
     \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> pp \<Rightarrow> 'a abs_state"
where
  "side_analyse_ip_eff \<Pi> ps main etf bot0 s0 v =
     side_env (td_cfg_side_ip_solver_eff.nu_at (compile_prog \<Pi> ps main) etf bot0 s0 v) v"

subsection \<open>Pure shim: the effectful solver coincides with the pure one\<close>

text \<open>
  For etf = etf_from_tf tf the effectful equation system is the pure one
  (side_cfg_T_ip_eff_etf_from_tf), so the effectful solver reads back the same
  unknown assignment and side_analyse_ip_eff coincides with side_analyse_ip.
\<close>

lemma td_cfg_side_ip_solver_eff_from_tf:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  shows "td_cfg_side_ip_solver_eff g (etf_from_tf tf) bot0 s0"
  by unfold_locales
     (simp_all add: side_cfg_T_ip_eff_is_mono_eq side_cfg_T_ip_eff_mono_sides
        side_cfg_T_ip_eff_mono_deps tf_mono)

lemma nu_at_eff_from_tf:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  shows "td_cfg_side_ip_solver_eff.nu_at g (etf_from_tf tf) bot0 s0
         = td_cfg_side_ip_solver.side_nu_at g tf bot0 s0"
proof -
  interpret e: td_cfg_side_ip_solver_eff g "etf_from_tf tf" bot0 s0
    by (rule td_cfg_side_ip_solver_eff_from_tf[OF tf_mono])
  interpret p: td_cfg_side_ip_solver g tf bot0 s0
    using tf_mono by unfold_locales
  show ?thesis
    unfolding e.nu_at_def p.side_nu_at_def
    by (simp add: side_cfg_T_ip_eff_etf_from_tf)
qed

lemma side_analyse_ip_eff_from_tf:
  fixes \<Pi> ps main and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  shows "side_analyse_ip_eff \<Pi> ps main (etf_from_tf tf) bot0 s0
         = side_analyse_ip \<Pi> ps main tf bot0 s0"
  unfolding side_analyse_ip_eff_def side_analyse_ip_def
  by (simp add: nu_at_eff_from_tf[OF tf_mono])

lemma side_cfg_ip_solve_dom_eff_from_tf:
  "side_cfg_ip_solve_dom_eff g (etf_from_tf tf) bot0 s0 v
   = side_cfg_ip_solve_dom g tf bot0 s0 v"
  unfolding side_cfg_ip_solve_dom_eff_def side_cfg_ip_solve_dom_def
  by (simp add: side_cfg_T_ip_eff_etf_from_tf)

subsection \<open>Pure shim: end-to-end effectful soundness\<close>

text \<open>
  The effectful analyser, instantiated at a pure domain via the shim, soundly
  over-approximates the IP collecting semantics at the program exit.  Obtained by
  transporting the pure end-to-end theorem (side_analyse_ip_collect_sound_exit_pruned)
  across the shim equalities -- the effectful pipeline inherits soundness for free
  for every sound pure domain.
\<close>

theorem (in sound_transfer) side_analyse_ip_eff_collect_sound_exit_pruned:
  fixes \<Pi> ps main and s0 :: "'a abs_state" and S :: "store set"
  assumes tf_mono: "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes dom: "side_cfg_ip_solve_dom_eff (compile_prog \<Pi> ps main) (etf_from_tf tf) bot s0
                  (cfg_exit (compile_prog \<Pi> ps main))"
  assumes S_sound: "S \<le> gamma_state s0"
  shows "cfg_collect_ip (compile_prog \<Pi> ps main) S (cfg_exit (compile_prog \<Pi> ps main))
         \<le> gamma_state (side_analyse_ip_eff \<Pi> ps main (etf_from_tf tf) bot s0
              (cfg_exit (compile_prog \<Pi> ps main)))"
proof -
  have dom': "side_cfg_ip_solve_dom (compile_prog \<Pi> ps main) tf bot s0
                (cfg_exit (compile_prog \<Pi> ps main))"
    using dom by (simp add: side_cfg_ip_solve_dom_eff_from_tf)
  have "cfg_collect_ip (compile_prog \<Pi> ps main) S (cfg_exit (compile_prog \<Pi> ps main))
        \<le> gamma_state (side_analyse_ip \<Pi> ps main tf bot s0
             (cfg_exit (compile_prog \<Pi> ps main)))"
    by (rule side_analyse_ip_collect_sound_exit_pruned[OF tf_mono dom' S_sound])
  thus ?thesis by (simp add: side_analyse_ip_eff_from_tf[OF tf_mono])
qed

end
