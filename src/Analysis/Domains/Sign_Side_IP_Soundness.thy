theory Sign_Side_IP_Soundness
  imports Sign_Domain TD_Side_IP_Soundness
begin

section \<open>Sign domain: side-effecting interprocedural TD solver instantiation\<close>

text \<open>Instantiates the side IP solver (side_analyse_ip) at the Sign domain.\<close>

theorem side_ip_sign_analysis_sound:
  fixes pi ps main and s t :: store and s0 :: "sign abs_state"
  assumes s_sound: "s \<in> sign_domain.gamma_state s0"
  assumes collect_exit:
    "t \<in> cfg_collect_ip (compile_prog pi ps main) {s}
       (cfg_exit (compile_prog pi ps main))"
  assumes side_solve_dom:
    "side_cfg_ip_solve_dom (compile_prog pi ps main) sign_tf bot s0
       (cfg_exit (compile_prog pi ps main))"
  shows "t \<in> sign_domain.gamma_state
       (side_analyse_ip pi ps main sign_tf bot s0
         (cfg_exit (compile_prog pi ps main)))"
proof -
  have gs: "{s} \<le> sound_domain.gamma_state gamma_sign s0"
    using s_sound
    unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by auto
  have collect:
    "cfg_collect_ip (compile_prog pi ps main) {s} (cfg_exit (compile_prog pi ps main))
     \<le> sound_domain.gamma_state gamma_sign
         (side_analyse_ip pi ps main sign_tf bot s0
           (cfg_exit (compile_prog pi ps main)))"
    by (rule sound_transfer.side_analyse_ip_collect_sound_exit_pruned
          [OF sign_sound_tf.sound_transfer_axioms sign_tf_mono side_solve_dom gs])
  have "t \<in> sound_domain.gamma_state gamma_sign
       (side_analyse_ip pi ps main sign_tf bot s0
         (cfg_exit (compile_prog pi ps main)))"
    using collect collect_exit by blast
  then show ?thesis
    unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by auto
qed

end
