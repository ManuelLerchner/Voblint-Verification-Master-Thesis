theory Sign_Side_IP_Soundness
  imports Sign_Domain TD_Side_IP_Soundness
begin

section \<open>Sign domain: side-effecting interprocedural TD solver instantiation\<close>

text \<open>Instantiates the side IP solver (side_analyse_ip) at the Sign domain.\<close>

theorem side_ip_sign_analysis_sound:
  fixes \<Pi> ps main and s t :: store and s0 :: "sign abs_state"
  assumes s_sound: "s \<in> sign_domain.gamma_state s0"
  assumes collect_exit:
    "t \<in> cfg_collect_ip (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))"
  assumes side_solve_dom:
    "side_cfg_ip_solve_dom (compile_prog \<Pi> ps main) sign_tf bot s0
       (cfg_exit (compile_prog \<Pi> ps main))"
  shows "t \<in> sign_domain.gamma_state
       (side_analyse_ip \<Pi> ps main sign_tf bot s0
         (cfg_exit (compile_prog \<Pi> ps main)))"
proof -
  have gs: "{s} \<le> sound_domain.gamma_state gamma_sign s0"
    using s_sound
    unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by auto
  have collect:
    "cfg_collect_ip (compile_prog \<Pi> ps main) {s} (cfg_exit (compile_prog \<Pi> ps main))
     \<le> sound_domain.gamma_state gamma_sign
         (side_analyse_ip \<Pi> ps main sign_tf bot s0
           (cfg_exit (compile_prog \<Pi> ps main)))"
    by (rule sound_transfer.side_analyse_ip_collect_sound_exit_pruned
          [OF sign_sound_tf.sound_transfer_axioms sign_tf_mono side_solve_dom gs])
  have "t \<in> sound_domain.gamma_state gamma_sign
       (side_analyse_ip \<Pi> ps main sign_tf bot s0
         (cfg_exit (compile_prog \<Pi> ps main)))"
    using collect collect_exit by blast
  then show ?thesis
    unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by auto
qed

section \<open>Sign domain: effectful transfer instance\<close>

text \<open>
  The Sign domain's effectful transfer functions, obtained by wrapping the pure
  sign_tf record via the pure_edge_tree shim.  This is the concrete witness that
  a real domain instantiates the Goblint-aligned effectful interface.

  Because sign_etf is etf_from_tf sign_tf, its effectful equation system is the
  pure one (side_cfg_T_ip_eff_etf_from_tf), so the three TD_side solver
  preconditions follow from sign_tf_mono.
\<close>

definition sign_etf :: "(unit, sign) effectful_domain_transfer" where
  "sign_etf = etf_from_tf sign_tf"

lemma sign_etf_eq_pure:
  "side_cfg_T_ip_eff g sign_etf bot0 s0 = side_cfg_T_ip g sign_tf (\<squnion>) bot0 s0"
  unfolding sign_etf_def by (rule side_cfg_T_ip_eff_etf_from_tf)

lemma sign_etf_is_mono_eq:
  "is_mono_eq (side_cfg_T_ip_eff g sign_etf bot0 s0)"
  unfolding sign_etf_def by (rule side_cfg_T_ip_eff_is_mono_eq[OF sign_tf_mono])

lemma sign_etf_mono_sides:
  "mono_sides (side_cfg_T_ip_eff g sign_etf bot0 s0)"
  unfolding sign_etf_def by (rule side_cfg_T_ip_eff_mono_sides[OF sign_tf_mono])

lemma sign_etf_mono_deps:
  "mono_deps (side_cfg_T_ip_eff g sign_etf bot0 s0)"
  unfolding sign_etf_def by (rule side_cfg_T_ip_eff_mono_deps)

text \<open>
  The Sign domain satisfies the effectful soundness contract: every per-action
  tree's reassembled full result over-approximates the concrete edge step.  This
  is the concrete instantiation of sound_effectful_transfer, discharged from the
  existing sign_sound_tf via the shim -- closing the instantiation gap for the
  Goblint-aligned effectful interface.
\<close>

lemma sign_sound_etf:
  "sound_effectful_transfer gamma_sign sign_etf"
  unfolding sign_etf_def
  by (rule sound_transfer_imp_sound_effectful[OF sign_sound_tf.sound_transfer_axioms])

end
