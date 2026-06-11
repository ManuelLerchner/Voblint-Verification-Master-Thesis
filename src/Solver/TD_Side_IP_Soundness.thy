theory TD_Side_IP_Soundness
  imports TD_Side_IP_Interface Constraint_System_IP_Sound
begin

(*
  Collecting soundness of a side-effecting INTERPROCEDURAL post-solution.

  Mirrors the M3 intra theorem (TD_Side_CFG.side_collect_sound_at) and the
  plain IP theorem (TD_IP_Soundness.td_analyse_ip_collect_sound_at): the
  combined env of a side_cfg_T_ip post-solution soundly over-approximates the
  interprocedural CFG collecting semantics (cfg_collect_ip), which folds in the
  combine triples.

  Reuses the generic, solver-agnostic bridge post_fixpoint_sound_at_ip; the only
  IP-specific content is the per-edge bound (apply_tf_combined_le_ip) and the
  per-combine bound (combine_combined_le_ip) proved in TD_Side_IP_CFG.

  Coverage (every edge target / combine return point lies in the solved stable
  set vars) is taken as a hypothesis here, exactly as the plain reachability-form
  theorem takes edge/combine reachability; on the backward cone of the query node
  it is discharged by pruning (cf. TD_IP_Soundness).
*)

context sound_transfer
begin

theorem side_collect_sound_ip_at:
  fixes sigma :: "pp + unit => 'a abs_state"
    and bot0 s0 :: "'a abs_state" and v0 :: pp and S :: "store set"
  assumes pp: "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0) v0 sigma vars"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes entry: "S \<le> gamma_state (side_env sigma (cfg_entry g))"
  assumes edge_cov: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> w \<in> vars"
  assumes combine_cov: "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow> ret \<in> vars"
  shows "cfg_collect_ip g S v0 \<le> gamma_state (side_env sigma v0)"
proof -
  have step_le:
    "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> apply_tf tf a (side_env sigma u) \<le> side_env sigma w"
  proof -
    fix u a w assume ed: "(u, a, w) \<in> edges g"
    have wv: "w \<in> vars" by (rule edge_cov[OF ed])
    show "apply_tf tf a (side_env sigma u) \<le> side_env sigma w"
      by (rule apply_tf_combined_le_ip[OF pp wv ed fin])
  qed
  have combine_le:
    "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow>
       combine_abs (side_env sigma c) (side_env sigma ex) \<le> side_env sigma ret"
  proof -
    fix c ex ret assume cb: "(c, ex, ret) \<in> combines g"
    have rv: "ret \<in> vars" by (rule combine_cov[OF cb])
    show "combine_abs (side_env sigma c) (side_env sigma ex) \<le> side_env sigma ret"
      by (rule combine_combined_le_ip[OF pp rv cb finC])
  qed
  have entry_le: "side_env sigma (cfg_entry g) \<le> side_env sigma (cfg_entry g)" by (rule order_refl)
  show ?thesis
    by (rule post_fixpoint_sound_at_ip[where env = "side_env sigma",
          OF fin finC entry step_le combine_le entry_le])
qed

end

end
