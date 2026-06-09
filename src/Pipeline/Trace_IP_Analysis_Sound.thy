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

(*
  M4 (core) -- history-sensitive read soundness over reaching traces.

  For ANY variable x (global or local) and ANY interprocedural trace tr reaching
  program point v, the value that x holds at the end of tr is contained in the
  analysis result's concretization gamma (env v x).  The "history" is the reaching
  trace itself: this is the soundness of reading a variable's value over the set
  of reaching interprocedural traces, which is exactly the flow-insensitive global
  read once specialised to a G-prefixed variable and joined over program points.

  It is an immediate consequence of trace_ip_analysis_sound (last tr is in
  alpha_last of the trace set, hence in gamma_state (env v)) and the per-coordinate
  shape of gamma_state.

  Scope: this is the SOUNDNESS half of M4.  The PRECISION half -- digest-indexed
  (context-sensitive) summaries that keep callers apart -- refines
  cfg_collect_trace_ip's combine via a digest hook on the unified collecting
  locale; it strengthens the trace set (smaller), so this soundness statement is
  preserved unchanged.  That precision refinement is future work.
*)
theorem reaching_global_read_sound:
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
  assumes tr: "tr \<in> cfg_collect_trace_ip g S v"
  shows "(last tr) x \<in> gamma (env v x)"
proof -
  have mem: "last tr \<in> alpha_last (cfg_collect_trace_ip g S v)"
    using tr unfolding alpha_last_def by blast
  have le: "alpha_last (cfg_collect_trace_ip g S v) \<le> gamma_state (env v)"
    by (rule trace_ip_analysis_sound[OF fin finC post_fp S_sound
          tf_sound_assign tf_sound_assume tf_sound_assume_not tf_sound_enter])
  from mem le have "last tr \<in> gamma_state (env v)" by blast
  thus ?thesis unfolding gamma_state_def by blast
qed

end

end
