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
  assumes fin_cfg: "finite (edges (compile_prog pi ps main))"
  assumes fin_comb: "finite (combines (compile_prog pi ps main))"
  assumes td_solve_dom:
    "TD_plain.solve_dom (make_rhs_tree_ip (compile_prog pi ps main) sign_tf (\<squnion>) bot s0)
       (cfg_exit (compile_prog pi ps main))"
  assumes edge_reach:
    "\<And>u a w. (u, a, w) \<in> edges (compile_prog pi ps main)
       \<Longrightarrow> w \<in> reach (make_rhs_tree_ip (compile_prog pi ps main) sign_tf (\<squnion>) bot s0)
         (TD_plain_Interp_solve (make_rhs_tree_ip (compile_prog pi ps main) sign_tf (\<squnion>) bot s0)
           (cfg_exit (compile_prog pi ps main))) (cfg_exit (compile_prog pi ps main))"
  assumes combine_reach:
    "\<And>c ex w. (c, ex, w) \<in> combines (compile_prog pi ps main)
       \<Longrightarrow> w \<in> reach (make_rhs_tree_ip (compile_prog pi ps main) sign_tf (\<squnion>) bot s0)
         (TD_plain_Interp_solve (make_rhs_tree_ip (compile_prog pi ps main) sign_tf (\<squnion>) bot s0)
           (cfg_exit (compile_prog pi ps main))) (cfg_exit (compile_prog pi ps main))"
  assumes entry_reach:
    "cfg_entry (compile_prog pi ps main)
     \<in> reach (make_rhs_tree_ip (compile_prog pi ps main) sign_tf (\<squnion>) bot s0)
       (TD_plain_Interp_solve (make_rhs_tree_ip (compile_prog pi ps main) sign_tf (\<squnion>) bot s0)
         (cfg_exit (compile_prog pi ps main))) (cfg_exit (compile_prog pi ps main))"
  shows "t \<in> sign_domain.gamma_state
       (td_analyse_ip pi ps main sign_tf (\<squnion>) bot s0
         (cfg_exit (compile_prog pi ps main)))"
proof -
  have gs: "s \<in> sound_domain.gamma_state gamma_sign s0"
  proof -
    from s_sound show ?thesis
      unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by auto
  qed
  have "t \<in> sound_domain.gamma_state gamma_sign
       (td_analyse_ip pi ps main sign_tf (\<squnion>) bot s0
         (cfg_exit (compile_prog pi ps main)))"
    using collect_exit combine_reach edge_reach entry_reach fin_cfg fin_comb s_sound
      sign_sound_tf.sound_transfer_axioms sound_transfer.ip_sign_analysis_sound td_solve_dom
    by blast
  then show ?thesis
    unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by auto
qed

end
