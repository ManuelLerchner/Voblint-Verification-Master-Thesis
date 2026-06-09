theory Trace_IP_Analysis_Sound
  imports Analysis_Sound CFG_Trace_Collect_IP
begin

(*
  U4 (unified-analysis migration): the trace overlay as a soundness morphism.

  Composes M3.5's interprocedural projection
    alpha_last (cfg_collect_trace_ip g S v) \<subseteq> cfg_collect_ip g S v
  with U2's unified interprocedural soundness
    cfg_collect_ip g S v \<le> gamma_state (env v)
  to obtain: the analyzer is sound w.r.t. the interprocedural TRACE semantics,
  projected to last stores.  alpha_last is thus a soundness-preserving morphism --
  no separate trace soundness stack is needed.

  This is the M4 extension point: a digest-indexed combine_at refining
  cfg_collect_trace_ip keeps the same shape

      alpha_last (precise trace collecting) \<subseteq> cfg_collect_ip \<le> gamma_state env,

  so the global-read soundness M4 adds plugs in below the projection without
  forking a new soundness chain.  M4 itself is NOT implemented here.
*)

context sound_domain
begin

theorem trace_ip_analysis_sound:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes post_fp: "is_post_fixpoint_ip g tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> gamma_state s0"
  assumes tf_sound_assign:
    "\<forall>x a sigma. \<forall>s \<in> gamma_state sigma.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sigma)"
  assumes tf_sound_assume:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sigma)"
  assumes tf_sound_assume_not:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sigma)"
  assumes tf_sound_enter:
    "\<forall>sigma. \<forall>s \<in> gamma_state sigma.
       enter_state s \<in> gamma_state (tf_enter tf sigma)"
  shows "alpha_last (cfg_collect_trace_ip g S v) \<le> gamma_state (env v)"
proof -
  have proj: "alpha_last (cfg_collect_trace_ip g S v) \<le> cfg_collect_ip g S v"
    by (rule alpha_last_cfg_collect_trace_ip_le)
  have st: "cfg_collect_ip g S v \<le> gamma_state (env v)"
    by (rule unified_post_fixpoint_sound_ip[OF fin finC post_fp S_sound
          tf_sound_assign tf_sound_assume tf_sound_assume_not tf_sound_enter])
  from proj st show ?thesis by (rule subset_trans)
qed

end

end
