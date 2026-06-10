theory Sign_IP_Soundness
  imports Sign_Domain TD_IP_Soundness
begin

(* Sign domain: interprocedural TD solver instantiation. *)

theorem ip_sign_analysis_sound:
  fixes pi ps main and s t :: store and s0 :: "sign abs_state"
  assumes s_sound: "s \<in> sign_domain.gamma_state s0"
  assumes collect_exit:
    "t \<in> cfg_collect_ip (compile_prog pi ps main) {s}
       (cfg_exit (compile_prog pi ps main))"
  assumes td_solve_dom:
    "TD_plain.solve_dom (make_rhs_tree_ip (compile_prog pi ps main) sign_tf (\<squnion>) bot s0)
       (cfg_exit (compile_prog pi ps main))"
  shows "t \<in> sign_domain.gamma_state
       (td_analyse_ip pi ps main sign_tf (\<squnion>) bot s0
         (cfg_exit (compile_prog pi ps main)))"
proof -
  have gs: "s \<in> sound_domain.gamma_state gamma_sign s0"
    using s_sound
    unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by auto
  have "t \<in> sound_domain.gamma_state gamma_sign
       (td_analyse_ip pi ps main sign_tf (\<squnion>) bot s0
         (cfg_exit (compile_prog pi ps main)))"
    using collect_exit gs sign_sound_tf.sound_transfer_axioms
      sound_transfer.ip_sign_analysis_sound td_solve_dom
    by blast
  then show ?thesis
    unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by auto
qed

end
