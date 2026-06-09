theory Trace_Soundness
  imports Pipeline CFG_Trace_Collect
begin

(*
  Trace-level soundness corollaries.

  CFG_Trace_Collect.lift is an EQUALITY, so the trace collecting is
  interchangeable with the reachable-state path/lfp collecting for last-store
  properties.  The trace-level results below are therefore derived from the
  existing state-based soundness theorems through the projection alpha_last,
  leaving CFG/Collecting, Domains and Pipeline unchanged.

  Three results:
    1. cfg_collect_eq_alpha_last_trace  -- the master equation
                                           (cfg_collect = alpha_last o trace).
    2. pipeline_sound_trace             -- the analyzer over-approximates the
                                           last store of every reaching trace.
    3. runs_to_iff_exit_trace           -- operational reading: a terminating
                                           run ends in t iff some exit trace
                                           has last store t.
*)

(* \<midarrow>\<midarrow> Master equation \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  The fixpoint collecting at every program point equals the last-store
  projection of the trace collecting.  As an equality (not just an inclusion),
  so no precision is lost in either direction.
*)
lemma cfg_collect_eq_alpha_last_trace:
  "cfg_collect g S v = alpha_last (cfg_collect_trace g S v)"
  unfolding cfg_collect_eq_cfg_collect_paths by (rule lift[symmetric])

(* \<midarrow>\<midarrow> Pipeline soundness over traces \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  Trace-level analogue of pipeline_sound_path: the analyzer's environment at v
  soundly covers the last store of every trace reaching v.  Numeric domains
  (sign/interval/parity) compose unchanged -- the conclusion is verbatim the
  state-based one, applied to last tr.
*)
theorem pipeline_sound_trace:
  fixes cfg :: "'a::bounded_semilattice_sup_bot analysis_config"
  assumes sound:      "sound_domain (ac_gamma cfg)"
  assumes join_eq:    "ac_join cfg = (\<lambda>s1 s2. \<lambda>x. s1 x \<squnion> s2 x)"
  assumes bot_eq:     "ac_bot cfg = (\<lambda>_. bot)"
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"
  assumes s_in_gamma: "s \<in> sound_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg)) v"
  assumes tr: "tr \<in> cfg_collect_trace (to_cfg c) {s} v"
  shows "last tr \<in> sound_domain.gamma_state (ac_gamma cfg) (run_analysis cfg c v)"
proof -
  have lt: "last tr \<in> cfg_collect (to_cfg c) {s} v"
    unfolding cfg_collect_eq_alpha_last_trace alpha_last_def using tr by blast
  then have "last tr \<in> cfg_collect_paths (to_cfg c) {s} v"
    by (simp add: cfg_collect_eq_cfg_collect_paths)
  then obtain es where
        path: "(to_cfg c) \<turnstile> (cfg_entry (to_cfg c)) \<longrightarrow>\<^bsub>es\<^esub> v"
    and t_in: "last tr \<in> edges_collect es {s}"
    unfolding cfg_collect_paths_def by blast
  show ?thesis
    by (rule pipeline_sound_path[OF sound join_eq bot_eq tf_sound
          s_in_gamma td_solve_dom path t_in])
qed

(* \<midarrow>\<midarrow> Operational reading of exit traces \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  runs_to is exit membership in cfg_collect (runs_to_def).  Through the master
  equation it becomes: a terminating run c from s ends in t iff some trace
  reaching the exit has last store t.  Terminating runs thus correspond to
  exit reachability.
*)
theorem runs_to_iff_exit_trace:
  "runs_to c s t \<longleftrightarrow>
     (\<exists>tr. tr \<in> cfg_collect_trace (to_cfg c) {s} (cfg_exit (to_cfg c)) \<and> last tr = t)"
  unfolding runs_to_def cfg_collect_eq_alpha_last_trace alpha_last_def
  by blast

(* \<midarrow>\<midarrow> Concrete example: Sign analysis over traces \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  Witness that the existing concrete examples pass through the trace foundation
  unchanged.  sign_pipeline_invariant_sound is restated with the last-store
  projection of the trace collecting on the concrete side; the proof is the
  state-based theorem rewritten through the master equation.  Interval (and any
  other sound_domain instance) lift identically -- pipeline_sound_trace already
  covers the generic case.
*)
corollary sign_pipeline_invariant_sound_trace:
  assumes tf_ok:   "domain_transfer_sound gamma_sign (ac_tf (sign_analysis_config s))"
  assumes init_ok: "s \<in> sign_domain.gamma_state (ac_init (sign_analysis_config s))"
  assumes entry_reachable:
    "\<And>v. \<exists>es. cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) (ac_tf (sign_analysis_config s))
          (ac_join (sign_analysis_config s)) (ac_bot (sign_analysis_config s))
          (ac_init (sign_analysis_config s))) v"
  shows   "\<forall>v. alpha_last (cfg_collect_trace (to_cfg c) {s} v) \<le>
                    sign_domain.gamma_state
                      (run_analysis (sign_analysis_config s) c v)"
  using sign_pipeline_invariant_sound[OF tf_ok init_ok entry_reachable td_solve_dom]
  unfolding cfg_collect_eq_alpha_last_trace[symmetric] .

end
