theory Mixed_Flow_Sound
  imports "Voblint_Core.LTR_TD_Side_Eff_Exit"
begin

section \<open>Mixed flow-sensitivity soundness against the collecting semantics\<close>

text \<open>Local answers are indexed by program point, while side effects join into one
  unknown per global name. \<open>mixed_flow_analysis_sound\<close> accepts any partial
  post-solution. \<open>mixed_flow_analysis_optimal\<close> obtains the least partial
  post-solution from the solver under @{const threefold_mono} and
  @{const cone_compatible_etf}. Monotonicity of side effects rules out routing decisions
  that reverse when the input environment grows.\<close>

subsection \<open>Generic soundness from any partial post-solution\<close>

theorem mixed_flow_analysis_sound:
  fixes g :: cfg and \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state lifted"
    and bot0 s0 :: "'a abs_state" and S :: "store set"
    and etf :: "('g, 'a) effectful_domain_transfer" and gseed :: 'g
    and gs :: "vname \<Rightarrow> bool"
  assumes se:    "sound_effectful_transfer gs etf"
  assumes pp:    "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) (cfg_exit g) \<sigma> vars"
  assumes entry: "S \<le> gamma_state_lift (side_env_lift \<sigma> (cfg_entry g))"
  assumes cone:  "cone_compatible_etf gs etf"
  assumes fin:   "finite (intra g)"
  assumes finC:  "finite (calls g)"
  assumes wf:    "wf_cfg g"
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  shows "ltr_collect gs g S (cfg_exit g) \<le> gamma_state_lift (side_env_lift \<sigma> (cfg_exit g))"
  by (rule side_collect_sound_exit_eff_ltr_cone[OF se pp fin finC wf entry cone inr])

subsection \<open>Optimal soundness via the TD solver (threefold monotonicity)\<close>

theorem mixed_flow_analysis_optimal:
  fixes \<Pi> ps mnm main and s0 :: "'a::sound_domain abs_state"
    and etf :: "('g::finite, 'a) effectful_domain_transfer" and gseed :: 'g
    and S :: "store set" and gs :: "vname \<Rightarrow> bool"
  assumes g_eq:  "g = compile_prog \<Pi> ps mnm main"
  assumes T_eq:  "T = side_cfg_T_eff gs g etf bot s0 gseed"
  assumes se:    "sound_effectful_transfer gs etf"
  assumes tfm:   "threefold_mono T"
  assumes cone:  "cone_compatible_etf gs etf"
  assumes dom:   "side_cfg_solve_dom_eff gs g etf bot s0 gseed (cfg_exit g)"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  shows sound:
    "ltr_collect gs g S (cfg_exit g)
       \<le> gamma_state_lift (side_analyse_eff gs \<Pi> ps mnm main etf bot s0 gseed (cfg_exit g))"
    and optimal:
    "least_part_post_solution (side_cfg_T_eff gs g etf bot s0 gseed) (cfg_exit g)
       (td_cfg_side_solver_eff.nu_at gs g etf bot s0 gseed (cfg_exit g))
       (td_cfg_side_solver_eff.stabl_at gs g etf bot s0 gseed (cfg_exit g))"
proof -
  interpret ip: td_cfg_side_solver_eff gs g etf bot s0 gseed
    using threefold_monoD_eq[OF tfm[unfolded T_eq]]
          threefold_monoD_sides[OF tfm[unfolded T_eq]]
          threefold_monoD_deps[OF tfm[unfolded T_eq]]
    by unfold_locales
  show sound:
    "ltr_collect gs g S (cfg_exit g)
       \<le> gamma_state_lift (side_analyse_eff gs \<Pi> ps mnm main etf bot s0 gseed (cfg_exit g))"
    unfolding g_eq
    by (rule side_analyse_eff_collect_sound_exit_ltr_cone[OF se
          tfm[unfolded T_eq g_eq] cone dom[unfolded g_eq] S_sound])
  have opt_full:
    "least_part_post_solution ip.cfg_pkg_eff (cfg_exit g)
       (ip.nu_at (cfg_exit g)) (ip.stabl_at (cfg_exit g))"
    by (rule ip.least_part_post_at_cfg[OF dom])
  show optimal:
    "least_part_post_solution (side_cfg_T_eff gs g etf bot s0 gseed) (cfg_exit g)
       (td_cfg_side_solver_eff.nu_at gs g etf bot s0 gseed (cfg_exit g))
       (td_cfg_side_solver_eff.stabl_at gs g etf bot s0 gseed (cfg_exit g))"
    using opt_full[simplified ip.cfg_pkg_eff_def] by blast
qed



end


