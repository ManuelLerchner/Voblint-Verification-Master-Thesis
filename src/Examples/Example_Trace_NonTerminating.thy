section \<open>Example: Trace-Based Safety on a Non-Terminating Program\<close>

theory Example_Trace_NonTerminating
  imports Trace_Soundness Example_NonTerminating_Safe
begin

text \<open>
  The trace foundation's payoff on partial behaviour.  \<^const>\<open>nonterm_prog\<close>
  (\<open>x := 10; while True do skip\<close>) never terminates, so it has no exit
  trace --- yet per-program-point safety over the (partial) traces reaching
  every CFG-reachable point is both expressible and provable.  This is the
  trace-level analogue of @{thm nonterm_safe_at_every_pp}, derived from
  \<open>pipeline_sound_trace\<close>.
\<close>

(* Per-pp trace safety: the analyzer at v covers the last store of every trace
   reaching v, with no termination premise. *)
theorem nonterm_trace_safe_at_every_pp:
  fixes cfg :: "'a::bounded_semilattice_sup_bot analysis_config"
  assumes sound:      "sound_domain (ac_gamma cfg)"
  assumes join_eq:    "ac_join cfg = (\<lambda>s1 s2. \<lambda>x. s1 x \<squnion> s2 x)"
  assumes bot_eq:     "ac_bot cfg = (\<lambda>_. bot)"
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"
  assumes s_in_gamma: "s \<in> sound_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom
       (make_rhs_tree (to_cfg nonterm_prog) (ac_tf cfg) (ac_join cfg)
          (ac_bot cfg) (ac_init cfg)) v"
  assumes tr: "tr \<in> cfg_collect_trace (to_cfg nonterm_prog) {s} v"
  shows "last tr \<in> sound_domain.gamma_state (ac_gamma cfg) (run_analysis cfg nonterm_prog v)"
  by (rule pipeline_sound_trace[OF sound join_eq bot_eq tf_sound s_in_gamma td_solve_dom tr])

(* Divergence at the level of traces: no trace reaches the exit. *)
lemma nonterm_no_exit_trace:
  "cfg_collect_trace (to_cfg nonterm_prog) {s} (cfg_exit (to_cfg nonterm_prog)) = {}"
proof (rule ccontr)
  assume "cfg_collect_trace (to_cfg nonterm_prog) {s} (cfg_exit (to_cfg nonterm_prog)) \<noteq> {}"
  then obtain tr where
        tr: "tr \<in> cfg_collect_trace (to_cfg nonterm_prog) {s} (cfg_exit (to_cfg nonterm_prog))"
    by blast
  hence "last tr \<in> cfg_collect (to_cfg nonterm_prog) {s} (cfg_exit (to_cfg nonterm_prog))"
    unfolding cfg_collect_eq_alpha_last_trace alpha_last_def by blast
  hence "runs_to nonterm_prog s (last tr)"
    unfolding runs_to_def by blast
  with nonterm_prog_no_runs_to show False by blast
qed

end
