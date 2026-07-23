theory Mixed_Flow_Sound
  imports "Voblint_Analysis.LTR_TD_Side_Eff_Exit"
begin

section \<open>Mixed flow-sensitivity soundness against the collecting semantics\<close>

text \<open>
  The interprocedural analysis is mixed flow-sensitive:
  - locals are flow-sensitive  (one unknown per program point, indexed by pp)
  - globals are flow-insensitive (one unknown per global name, joined over all
    contributions via side effects, read back as glob_env)

  Two theorems are provided at the plain collecting-semantics level.

  mixed_flow_analysis_sound: generic soundness given any partial post-solution.
  No threefold monotonicity required; the caller supplies sigma directly.
  This is the minimal soundness result: any over-approximating fixpoint works.

  mixed_flow_analysis_optimal: soundness via the TD solver, plus the optimality
  guarantee that the solver's environment is the *least* partial post-solution.
  Requires threefold_mono (paper Def. 7) and cone_compatible_etf.  The
  mono_sides component of threefold_mono is the monotone-routing precondition
  that excludes non-monotone conditional side-routing (flag_etf, Meeting 7 s3).

  side_analyse_eff ... v x unfolds to
    side_env (nu_at ...) v x = (nu_at ...) (Inl v) x |_| glob_env (nu_at ...) x
  The local component is flow-sensitive (indexed by v).  The global component is
  flow-insensitive: all named-global side contributions are joined through
  glob_env before reads at any program point.
\<close>

subsection \<open>Generic soundness from any partial post-solution\<close>

theorem mixed_flow_analysis_sound:
  fixes g :: cfg and \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and bot0 s0 :: "'a abs_state" and S :: "store set"
    and etf :: "('g, 'a) effectful_domain_transfer" and gseed :: 'g
  assumes se:    "sound_effectful_transfer etf"
  assumes pp:    "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) (cfg_exit g) \<sigma> vars"
  assumes entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes cone:  "cone_compatible_etf etf"
  assumes fin:   "finite (intra g)"
  assumes finC:  "finite (calls g)"
  assumes wf:    "wf_cfg g"
  assumes inr: "inr_slot_locals_bot \<sigma>"
  shows "ltr_collect g S (cfg_exit g) \<le> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
  by (rule side_collect_sound_exit_eff_ltr_cone[OF se pp fin finC wf entry cone inr])

subsection \<open>Optimal soundness via the TD solver (threefold monotonicity)\<close>

theorem mixed_flow_analysis_optimal:
  fixes \<Pi> ps mnm main and s0 :: "'a::sound_domain abs_state"
    and etf :: "('g::finite, 'a) effectful_domain_transfer" and gseed :: 'g
    and S :: "store set"
  assumes g_eq:  "g = compile_prog \<Pi> ps mnm main"
  assumes T_eq:  "T = side_cfg_T_eff g etf bot s0 gseed"
  assumes se:    "sound_effectful_transfer etf"
  assumes tfm:   "threefold_mono T"
  assumes cone:  "cone_compatible_etf etf"
  assumes dom:   "side_cfg_solve_dom_eff g etf bot s0 gseed (cfg_exit g)"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  shows sound:
    "ltr_collect g S (cfg_exit g)
       \<le> \<lbrakk>side_analyse_eff \<Pi> ps mnm main etf bot s0 gseed (cfg_exit g)\<rbrakk>"
    and optimal:
    "least_part_post_solution (side_cfg_T_eff g etf bot s0 gseed) (cfg_exit g)
       (td_cfg_side_solver_eff.nu_at g etf bot s0 gseed (cfg_exit g))
       (td_cfg_side_solver_eff.stabl_at g etf bot s0 gseed (cfg_exit g))"
proof -
  interpret ip: td_cfg_side_solver_eff g etf bot s0 gseed
    using threefold_monoD_eq[OF tfm[unfolded T_eq]]
          threefold_monoD_sides[OF tfm[unfolded T_eq]]
          threefold_monoD_deps[OF tfm[unfolded T_eq]]
    by unfold_locales
  show sound:
    "ltr_collect g S (cfg_exit g)
       \<le> \<lbrakk>side_analyse_eff \<Pi> ps mnm main etf bot s0 gseed (cfg_exit g)\<rbrakk>"
    unfolding g_eq
    by (rule side_analyse_eff_collect_sound_exit_ltr_cone[OF se
          tfm[unfolded T_eq g_eq] cone dom[unfolded g_eq] S_sound])
  have opt_full:
    "least_part_post_solution ip.cfg_pkg_eff (cfg_exit g)
       (ip.nu_at (cfg_exit g)) (ip.stabl_at (cfg_exit g))"
    by (rule ip.least_part_post_at_cfg[OF dom])
  show optimal:
    "least_part_post_solution (side_cfg_T_eff g etf bot s0 gseed) (cfg_exit g)
       (td_cfg_side_solver_eff.nu_at g etf bot s0 gseed (cfg_exit g))
       (td_cfg_side_solver_eff.stabl_at g etf bot s0 gseed (cfg_exit g))"
    using opt_full[simplified ip.cfg_pkg_eff_def] by blast
qed



end


