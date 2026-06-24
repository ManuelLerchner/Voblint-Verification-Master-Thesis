theory Mixed_Flow_Sound
  imports Trace_Analysis_Sound "Voblint_Analysis.TD_Side_Eff_Soundness"
begin

section \<open>Mixed flow-sensitivity soundness against the trace semantics\<close>

text \<open>
  The interprocedural analysis is mixed flow-sensitive:
  - locals are flow-sensitive  (one unknown per program point, indexed by pp)
  - globals are flow-insensitive (one unknown per global name, joined over all
    contributions via side effects, read back as glob_env)

  Two theorems are provided at the trace-semantics level.

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
  In the pure-shim case (etf = etf_from_tf tf):
  - for local x (not is_global x): glob_env s x = bot, result = s (Inl v) x
  - for global x (is_global x):    s (Inl v) x = bot, result = glob_env s x
  So the local component is flow-sensitive (indexed by v) and the global component
  is flow-insensitive (v-independent).
\<close>

subsection \<open>Generic soundness from any partial post-solution\<close>

theorem mixed_flow_analysis_sound:
  fixes g :: cfg and \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and bot0 s0 :: "'a abs_state" and S :: "store set" and tr :: "store list"
    and etf :: "('g, 'a) effectful_domain_transfer" and gseed :: 'g
  assumes se:    "sound_effectful_transfer etf"
  assumes pp:    "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) (cfg_exit g) \<sigma> vars"
  assumes entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes cone:  "cone_compatible_etf etf"
  assumes fin:   "finite (edges g)"
  assumes finC:  "finite (combines g)"
  assumes tr_in: "tr \<in> cfg_collect_trace g S (cfg_exit g)"
  shows "\<forall>x. (last tr) x \<in> gamma (side_env \<sigma> (cfg_exit g) x)"
proof -
  have state_sound:
    "cfg_collect g S (cfg_exit g) \<le> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
    by (rule side_collect_sound_exit_pruned_eff_cone[OF se pp fin finC entry cone])
  have trace_proj:
    "alpha_last (cfg_collect_trace g S (cfg_exit g)) \<le> cfg_collect g S (cfg_exit g)"
    by (rule alpha_last_cfg_collect_trace_le)
  have last_in: "last tr \<in> alpha_last (cfg_collect_trace g S (cfg_exit g))"
    using tr_in unfolding alpha_last_def by blast
  have "last tr \<in> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
    using last_in trace_proj state_sound by blast
  thus ?thesis unfolding gamma_state_def by blast
qed

subsection \<open>Optimal soundness via the TD solver (threefold monotonicity)\<close>

theorem mixed_flow_analysis_optimal:
  fixes \<Pi> ps main and s0 :: "'a::sound_domain abs_state"
    and etf :: "('g::finite, 'a) effectful_domain_transfer" and gseed :: 'g
    and S :: "store set" and tr :: "store list"
  assumes g_eq:  "g = compile_prog \<Pi> ps main"
  assumes T_eq:  "T = side_cfg_T_eff g etf bot s0 gseed"
  assumes se:    "sound_effectful_transfer etf"
  assumes tfm:   "threefold_mono T"
  assumes cone:  "cone_compatible_etf etf"
  assumes dom:   "side_cfg_solve_dom_eff g etf bot s0 gseed (cfg_exit g)"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes tr_in: "tr \<in> cfg_collect_trace g S (cfg_exit g)"
  shows sound:
    "\<forall>x. (last tr) x \<in> gamma (side_analyse_eff \<Pi> ps main etf bot s0 gseed (cfg_exit g) x)"
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
  have state_sound:
    "cfg_collect g S (cfg_exit g) \<le>
       \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed (cfg_exit g)\<rbrakk>"
    unfolding g_eq
    by (rule side_analyse_eff_collect_sound_exit_pruned[OF se
          tfm[unfolded T_eq g_eq] cone dom[unfolded g_eq] S_sound])
  have trace_proj:
    "alpha_last (cfg_collect_trace g S (cfg_exit g)) \<le> cfg_collect g S (cfg_exit g)"
    by (rule alpha_last_cfg_collect_trace_le)
  have last_in: "last tr \<in> alpha_last (cfg_collect_trace g S (cfg_exit g))"
    using tr_in unfolding alpha_last_def by blast
  have last_sound: "last tr \<in> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed (cfg_exit g)\<rbrakk>"
    using last_in trace_proj state_sound by blast
  show sound: "\<forall>x. (last tr) x \<in> gamma (side_analyse_eff \<Pi> ps main etf bot s0 gseed (cfg_exit g) x)"
    using last_sound unfolding gamma_state_def by blast
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

subsection \<open>Pure-shim specializations (etf_from_tf)\<close>

text \<open>
  When etf = etf_from_tf tf, cone_compatible_etf holds structurally
  (cone_compatible_etf_from_tf) and, given tf_mono, threefold_mono holds too
  (threefold_mono_from_tf).  These corollaries drop both preconditions: the caller
  only supplies domain-specific transfer-function obligations (soundness,
  monotonicity, solve_dom) and program-level obligations (S_sound, tr_in).
\<close>

corollary mixed_flow_analysis_sound_tf:
  fixes g :: cfg and \<sigma> :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state"
    and bot0 s0 :: "'a abs_state" and S :: "store set" and tr :: "store list"
    and tf :: "'a domain_transfer"
  assumes se:    "sound_effectful_transfer (etf_from_tf tf)"
  assumes pp:    "part_post_solution (side_cfg_T_eff g (etf_from_tf tf) bot0 s0 ())
                    (cfg_exit g) \<sigma> vars"
  assumes entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes fin:   "finite (edges g)"
  assumes finC:  "finite (combines g)"
  assumes tr_in: "tr \<in> cfg_collect_trace g S (cfg_exit g)"
  shows "\<forall>x. (last tr) x \<in> gamma (side_env \<sigma> (cfg_exit g) x)"
  by (rule mixed_flow_analysis_sound[OF se pp entry cone_compatible_etf_from_tf
        fin finC tr_in])

corollary mixed_flow_analysis_optimal_tf:
  fixes \<Pi> ps main and s0 :: "'a::sound_domain abs_state"
    and tf :: "'a domain_transfer" and S :: "store set" and tr :: "store list"
  assumes g_eq:  "g = compile_prog \<Pi> ps main"
  assumes T_eq:  "T = side_cfg_T_eff g (etf_from_tf tf) bot s0 ()"
  assumes se:    "sound_effectful_transfer (etf_from_tf tf)"
  assumes tf_mono: "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes dom:   "side_cfg_solve_dom_eff g (etf_from_tf tf) bot s0 () (cfg_exit g)"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes tr_in: "tr \<in> cfg_collect_trace g S (cfg_exit g)"
  shows
    "\<forall>x. (last tr) x \<in> gamma
       (side_analyse_eff \<Pi> ps main (etf_from_tf tf) bot s0 () (cfg_exit g) x)"
    and
    "least_part_post_solution (side_cfg_T_eff g (etf_from_tf tf) bot s0 ()) (cfg_exit g)
       (td_cfg_side_solver_eff.nu_at g (etf_from_tf tf) bot s0 () (cfg_exit g))
       (td_cfg_side_solver_eff.stabl_at g (etf_from_tf tf) bot s0 () (cfg_exit g))"
proof -
  have tfm: "threefold_mono T"
    unfolding T_eq by (rule threefold_mono_from_tf[OF tf_mono])
  show "\<forall>x. (last tr) x \<in> gamma
       (side_analyse_eff \<Pi> ps main (etf_from_tf tf) bot s0 () (cfg_exit g) x)"
    by (rule sound[OF g_eq T_eq se tfm cone_compatible_etf_from_tf dom S_sound tr_in])
  show "least_part_post_solution (side_cfg_T_eff g (etf_from_tf tf) bot s0 ()) (cfg_exit g)
       (td_cfg_side_solver_eff.nu_at g (etf_from_tf tf) bot s0 () (cfg_exit g))
       (td_cfg_side_solver_eff.stabl_at g (etf_from_tf tf) bot s0 () (cfg_exit g))"
    by (rule optimal[OF g_eq T_eq se tfm cone_compatible_etf_from_tf dom S_sound tr_in])
qed

end
