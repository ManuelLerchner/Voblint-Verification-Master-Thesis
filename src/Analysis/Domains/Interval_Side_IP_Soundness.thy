theory Interval_Side_IP_Soundness
  imports Interval_Domain TD_Side_IP_Soundness
begin

section \<open>Interval domain: side-effecting interprocedural TD solver instantiation\<close>

text \<open>Instantiates the side IP solver (side_analyse_ip) at the Interval domain.\<close>

theorem side_ip_ivl_analysis_sound:
  fixes \<Pi> ps main and s t :: store and s0 :: "ivl abs_state"
  assumes s_sound: "s \<in> ivl_domain.gamma_state s0"
  assumes collect_exit:
    "t \<in> cfg_collect_ip (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))"
  assumes side_solve_dom:
    "side_cfg_ip_solve_dom (compile_prog \<Pi> ps main) ivl_tf bot s0
       (cfg_exit (compile_prog \<Pi> ps main))"
  shows "t \<in> ivl_domain.gamma_state
       (side_analyse_ip \<Pi> ps main ivl_tf bot s0
         (cfg_exit (compile_prog \<Pi> ps main)))"
proof -
  have gs: "{s} \<le> sound_domain.gamma_state gamma_ivl s0"
    using s_sound
    unfolding ivl_domain.gamma_state_def sound_domain.gamma_state_def by auto
  have collect:
    "cfg_collect_ip (compile_prog \<Pi> ps main) {s} (cfg_exit (compile_prog \<Pi> ps main))
     \<le> sound_domain.gamma_state gamma_ivl
         (side_analyse_ip \<Pi> ps main ivl_tf bot s0
           (cfg_exit (compile_prog \<Pi> ps main)))"
    by (rule sound_transfer.side_analyse_ip_collect_sound_exit_pruned
          [OF ivl_sound_tf.sound_transfer_axioms ivl_tf_mono side_solve_dom gs])
  have "t \<in> sound_domain.gamma_state gamma_ivl
       (side_analyse_ip \<Pi> ps main ivl_tf bot s0
         (cfg_exit (compile_prog \<Pi> ps main)))"
    using collect collect_exit by blast
  then show ?thesis
    unfolding ivl_domain.gamma_state_def sound_domain.gamma_state_def by auto
qed

end
