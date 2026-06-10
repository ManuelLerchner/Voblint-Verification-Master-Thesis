theory Sign_Side_Soundness
  imports Sign_Domain TD_Side_Soundness
begin

(* Sign domain: side-effecting TD solver instantiation. *)

theorem side_sign_analysis_sound:
  fixes c :: com and s t :: store and s0 :: "sign abs_state"
  assumes s_sound: "s \<in> sign_domain.gamma_state s0"
  assumes exit_in_collect:
    "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
  assumes side_solve_dom:
    "side_cfg_solve_dom (to_cfg c) sign_tf bot s0 (cfg_exit (to_cfg c))"
  assumes s0_global_bot: "restrict_global s0 = bot"
  shows "t \<in> sign_domain.gamma_state
       (side_analyse c sign_tf bot s0 (cfg_exit (to_cfg c)))"
proof -
  have fin: "finite (edges (to_cfg c))" by (rule to_cfg_finite)
  obtain es where ep:
    "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
    using runs_to_imp_path[OF exit_in_collect[folded runs_to_def]] by blast
  show ?thesis
    by (smt (verit, del_insts) ep exit_in_collect fin s0_global_bot s_sound side_solve_dom
        sign_domain.sound_domain_axioms sign_sound_tf.sound_transfer_axioms sign_tf_mono
        sound_domain.side_solver_sound sound_transfer.tf_sound_assign sound_transfer.tf_sound_assume
        sound_transfer.tf_sound_assume_not sound_transfer.tf_sound_enter)
qed

end
