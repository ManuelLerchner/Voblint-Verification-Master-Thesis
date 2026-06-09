theory Sign_Soundness
  imports Sign_Domain TD_Soundness
begin

(* Sign domain: plain TD solver instantiation. *)

theorem sign_analysis_sound:
  fixes c :: com and s t :: store and s0 :: "sign abs_state" and es :: "(edge_action * pp) list"
  assumes s_sound: "s \<in> sign_domain.gamma_state s0"
  assumes exit_in_collect:
    "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes entry_path:
    "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) sign_tf (\<squnion>) bot s0) v"
  shows "t \<in> sign_domain.gamma_state
          (td_analyse c sign_tf (\<squnion>) bot s0 (cfg_exit (to_cfg c)))"
proof -
  have gs: "s \<in> sound_domain.gamma_state gamma_sign s0"
    using s_sound unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by auto
  have "t \<in> sound_domain.gamma_state gamma_sign
       (td_analyse c sign_tf (\<squnion>) bot s0 (cfg_exit (to_cfg c)))"
    using entry_path exit_in_collect fin_cfg s_sound sign_sound_tf.sound_transfer_axioms
      sound_transfer.td_solver_sound td_solve_dom by blast
    then show ?thesis
    unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by auto
qed

end
