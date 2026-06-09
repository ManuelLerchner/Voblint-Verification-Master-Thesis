theory Sign_Side_Soundness
  imports Sign_Domain TD_Side_Soundness
begin

(* Sign domain: side-effecting TD solver instantiation. *)

theorem side_sign_analysis_sound:
  fixes c :: com and s t :: store and s0 :: "sign abs_state" and es :: "(edge_action * pp) list"
  assumes s_sound: "s \<in> sign_domain.gamma_state s0"
  assumes exit_in_collect:
    "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes entry_path:
    "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
  assumes side_solve_dom:
    "side_cfg_solve_dom (to_cfg c) sign_tf bot s0 (cfg_exit (to_cfg c))"
  assumes s0_global_bot: "restrict_global s0 = bot"
  shows "t \<in> sign_domain.gamma_state
       (side_analyse c sign_tf bot s0 (cfg_exit (to_cfg c)))"
  by (smt (verit, del_insts) entry_path exit_in_collect fin_cfg s0_global_bot s_sound side_solve_dom
      sign_domain.sound_domain_axioms sign_sound_tf.sound_transfer_axioms sign_tf_mono
      sound_domain.side_solver_sound sound_transfer.tf_sound_assign sound_transfer.tf_sound_assume
      sound_transfer.tf_sound_assume_not sound_transfer.tf_sound_enter)

end
