theory Interval_Soundness
  imports Interval_Domain TD_Soundness
begin

(* Interval domain: plain TD solver instantiation. *)

theorem interval_analysis_sound:
  fixes c :: com and s t :: store and s0 :: "ivl abs_state" and es :: "(edge_action * pp) list"
  assumes s_sound: "s \<in> ivl_domain.gamma_state s0"
  assumes exit_in_collect:
    "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes entry_path:
    "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) ivl_tf (\<squnion>) bot s0) v"
  shows "t \<in> ivl_domain.gamma_state
          (td_analyse c ivl_tf (\<squnion>) bot s0 (cfg_exit (to_cfg c)))"
proof -
  have gs: "s \<in> sound_domain.gamma_state gamma_ivl s0"
    using s_sound unfolding ivl_domain.gamma_state_def sound_domain.gamma_state_def by auto
  have "t \<in> sound_domain.gamma_state gamma_ivl
       (td_analyse c ivl_tf (\<squnion>) bot s0 (cfg_exit (to_cfg c)))"
    using entry_path exit_in_collect fin_cfg ivl_sound_tf.sound_transfer_axioms s_sound
      sound_transfer.td_solver_sound td_solve_dom by blast
    then show ?thesis
    unfolding ivl_domain.gamma_state_def sound_domain.gamma_state_def by auto
qed

end
