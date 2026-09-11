theory Dispatch_Matrix
  imports "Voblint_CLI.Dispatch_Config"
begin

section \<open>Config-driven dispatch agrees with each existing typed entry point\<close>

text \<open>
  The regression pattern \<open>new_dispatch cfg p = old_entry_point p\<close> at every
  currently-public configuration: config-driven dispatch is a routing
  layer over the untouched existing dispatchers, never a reimplementation
  that could silently drift from what the CLI already exercises.
\<close>

lemma analyse_config_sign_default:
  "analyse_config (default_config Sign_Analysis Ctx_None) p = Some (analyse Sign_Analysis p)"
  by (simp add: analyse_config_def default_config_def mk_analysis_config_def)

lemma analyse_config_interval_default:
  "analyse_config (default_config Interval_Analysis Ctx_None) p = Some (analyse Interval_Analysis p)"
  by (simp add: analyse_config_def default_config_def mk_analysis_config_def)

lemma analyse_config_int_default:
  "analyse_config (default_config Int_Analysis Ctx_None) p = Some (analyse Int_Analysis p)"
  by (simp add: analyse_config_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_interval_entrystate:
  "analyse_config_ctx (default_config Interval_Analysis Ctx_EntryState) p
     = Some (analyse_interval_entry_state p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

text \<open>
  An explicit solver alongside \<open>Ctx_EntryState\<close> is a valid, routed selection:
  the routed equation system underneath is exactly as solver-independent as
  the flat one.
\<close>

lemma analyse_config_ctx_interval_entrystate_explicit_join_valid:
  "analyse_config_ctx \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr> p
     = Some (analyse_interval_entry_state_join p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_interval_entrystate_explicit_per_origin_valid:
  "analyse_config_ctx \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr> p
     = Some (analyse_interval_entry_state_per_origin p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_interval_entrystate_explicit_warrow_valid:
  "analyse_config_ctx \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr> p
     = Some (analyse_interval_entry_state p)"
  by (simp add: analyse_config_ctx_def)

text \<open>
  The fourth discipline is pinned at both contexts because the resolver already
  accepts it there: a plan the resolver produces but this dispatcher does not
  match is a code-generated match failure, not a rejected configuration.
\<close>

lemma analyse_config_ctx_interval_entrystate_explicit_wpo_valid:
  "analyse_config_ctx \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_WarrowPerOrigin, cfg_context = Ctx_EntryState \<rparr> p
     = Some (analyse_interval_entry_state_wpo p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_interval_callstring_explicit_wpo_valid:
  "analyse_config_ctx \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_WarrowPerOrigin, cfg_context = Ctx_CallString (Suc k) \<rparr> p
     = Some (analyse_interval_call_string_report_wpo (Suc k) p)"
  by (simp add: analyse_config_ctx_def)

text \<open>
  Sign at \<open>Ctx_EntryState\<close>, pinned the same way \<open>Ctx_CallString\<close>'s own regressions are:
  valid at the implicit-default and explicit \<open>Solver_Join\<close> selections, invalid at the
  two solvers Sign's entry-state soundness does not prove.
\<close>

lemma analyse_config_ctx_sign_entrystate_default_valid:
  "analyse_config_ctx (default_config Sign_Analysis Ctx_EntryState) p
     = Some (analyse_sign_entry_state_report p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_sign_entrystate_explicit_join_valid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr> p
   = Some (analyse_sign_entry_state_report p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_sign_entrystate_per_origin_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_sign_entrystate_warrow_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

text \<open>
  Parity, the fourth domain, on the config-driven path: supported at \<open>Ctx_None\<close> under the
  two solvers it has tables for, and genuinely \<^const>\<open>None\<close> at the contexts it has no
  routed instance for -- the config resolver decides both, with no CLI-side table.
\<close>

lemma analyse_config_parity_default:
  "analyse_config (default_config Parity_Analysis Ctx_None) p = Some (analyse Parity_Analysis p)"
  by (simp add: analyse_config_def default_config_def mk_analysis_config_def)

lemma analyse_config_parity_per_origin_valid:
  "analyse_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_None \<rparr> p
   = Some (analyse_parity_report_per_origin p)"
  by (simp add: analyse_config_def)

lemma analyse_config_parity_warrow_invalid:
  "analyse_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_None \<rparr> p
   = None"
  by (simp add: analyse_config_def)

lemma analyse_config_ctx_parity_entrystate:
  "analyse_config_ctx (default_config Parity_Analysis Ctx_EntryState) p
   = Some (analyse_parity_entry_state_report p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

text \<open>A zero-length call string is the unit context spelled twice, so the
  resolver rejects it and the wrapper has nothing to route.\<close>

lemma analyse_config_ctx_parity_callstring:
  "analyse_config_ctx (default_config Parity_Analysis (Ctx_CallString k)) p
   = (if k = 0 then None else Some (analyse_parity_call_string_report k p))"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

text \<open>
  Int at \<open>Ctx_EntryState\<close>: the implicit default routes to the warrowing report, the
  explicit \<open>Solver_Warrow\<close>/\<open>Solver_Join\<close> selections to theirs, and the two solvers
  Int's own entry-state soundness does not certify stay invalid.
\<close>

lemma analyse_config_ctx_int_entrystate_default_valid:
  "analyse_config_ctx (default_config Int_Analysis Ctx_EntryState) p
     = Some (analyse_int_entry_state_report_warrow p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_int_entrystate_explicit_join_valid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr> p
   = Some (analyse_int_entry_state_report p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_int_entrystate_per_origin_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_int_entrystate_warrow_valid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr> p
   = Some (analyse_int_entry_state_report_warrow p)"
  by (simp add: analyse_config_ctx_def)

text \<open>
  Call-string: \<open>analyse_config_ctx\<close> at \<open>Ctx_CallString k\<close> is exactly
  \<^const>\<open>analyse_interval_call_string_report\<close> \<open>k\<close> -- the one generic,
  runtime-\<open>k\<close> pipeline, reachable through the public configuration path with
  no second implementation in between.
\<close>

lemma analyse_config_ctx_interval_callstring_eq_report:
  assumes "k \<noteq> 0"
  shows "analyse_config_ctx (default_config Interval_Analysis (Ctx_CallString k)) p
           = Some (analyse_interval_call_string_report k p)"
  using assms by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_interval_callstring_zero_invalid:
  "analyse_config_ctx (default_config Interval_Analysis (Ctx_CallString 0)) p = None"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

text \<open>
  An explicit solver alongside \<open>Ctx_CallString k\<close> (\<open>k \<ge> 1\<close>) is likewise a
  valid, routed selection now, mirroring \<open>Ctx_EntryState\<close>'s generalization
  above.
\<close>

lemma analyse_config_ctx_interval_callstring_explicit_warrow_valid:
  assumes "k \<noteq> 0"
  shows "analyse_config_ctx
           \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString k \<rparr> p
         = Some (analyse_interval_call_string_report k p)"
  using assms by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_interval_callstring_explicit_join_valid:
  assumes "k \<noteq> 0"
  shows "analyse_config_ctx
           \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString k \<rparr> p
         = Some (analyse_interval_call_string_report_join k p)"
  using assms by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_interval_callstring_explicit_per_origin_valid:
  assumes "k \<noteq> 0"
  shows "analyse_config_ctx
           \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString k \<rparr> p
         = Some (analyse_interval_call_string_report_per_origin k p)"
  using assms by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_interval_callstring_zero_explicit_solver_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 0 \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

text \<open>
  Sign at \<open>Ctx_CallString\<close>, pinned the same way \<open>Analysis_Config\<close>'s own
  resolver regressions are: valid at \<open>k \<ge> 1\<close> under the implicit-default and
  explicit \<open>Solver_Join\<close> selections, invalid at \<open>k = 0\<close> and at the two
  solvers Sign's call-string soundness does not prove.
\<close>

lemma analyse_config_ctx_sign_callstring_k1_valid:
  "analyse_config_ctx (default_config Sign_Analysis (Ctx_CallString 1)) p
     = Some (analyse_sign_call_string_report 1 p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_sign_callstring_k2_valid:
  "analyse_config_ctx (default_config Sign_Analysis (Ctx_CallString 2)) p
     = Some (analyse_sign_call_string_report 2 p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_sign_callstring_zero_invalid:
  "analyse_config_ctx (default_config Sign_Analysis (Ctx_CallString 0)) p = None"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_sign_callstring_explicit_join_valid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString 2 \<rparr> p
   = Some (analyse_sign_call_string_report 2 p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_sign_callstring_per_origin_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString 2 \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_sign_callstring_warrow_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 2 \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

text \<open>
  Int at \<open>Ctx_CallString\<close>: valid at \<open>k \<ge> 1\<close> under the implicit default (the warrowing
  report) and the explicit \<open>Solver_Warrow\<close>/\<open>Solver_Join\<close> selections, invalid at \<open>k = 0\<close>
  and at the two solvers Int's own call-string soundness does not certify.
\<close>

lemma analyse_config_ctx_int_callstring_k1_valid:
  "analyse_config_ctx (default_config Int_Analysis (Ctx_CallString 1)) p
     = Some (analyse_int_call_string_report_warrow 1 p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_int_callstring_k2_valid:
  "analyse_config_ctx (default_config Int_Analysis (Ctx_CallString 2)) p
     = Some (analyse_int_call_string_report_warrow 2 p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_int_callstring_zero_invalid:
  "analyse_config_ctx (default_config Int_Analysis (Ctx_CallString 0)) p = None"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_int_callstring_explicit_join_valid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString 2 \<rparr> p
   = Some (analyse_int_call_string_report 2 p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_int_callstring_per_origin_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString 2 \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_int_callstring_warrow_valid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 2 \<rparr> p
   = Some (analyse_int_call_string_report_warrow 2 p)"
  by (simp add: analyse_config_ctx_def)

subsubsection \<open>Dispatcher-path parity with the direct generic CallString core\<close>

text \<open>
  The public path (through \<^const>\<open>resolve_analysis_config\<close> and
  \<^const>\<open>analyse_config_ctx\<close>) reaches the identical values the CS1--CS3
  parity theory (\<open>Example_Interval_Call_String_Generic_Parity\<close>)
  already pinned against the fixed \<open>k=1\<close>/\<open>k=2\<close> examples -- restated here as
  a report-level, not a solved-state-level, witness: the dispatcher does not
  reimplement or re-derive anything, it only routes.

  \<^const>\<open>analyse_interval_call_string_report\<close> is the generated published
  report, an application of \<^const>\<open>routed_dg_pipeline.verdict_report\<close> at
  \<^term>\<open>cs_route k\<close>; the parity theory pins the same run's solved states
  through \<^const>\<open>cs_call_string_sol_prog\<close>, which applies the same pipeline
  at the same route.
\<close>

lemma analyse_config_ctx_interval_callstring_k1_reaches_generic_core:
  "analyse_config_ctx (default_config Interval_Analysis (Ctx_CallString 1)) p
     = Some (analyse_interval_call_string_report 1 p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_interval_callstring_k2_reaches_generic_core:
  "analyse_config_ctx (default_config Interval_Analysis (Ctx_CallString 2)) p
     = Some (analyse_interval_call_string_report 2 p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_with_state_sign_default:
  "analyse_config_with_state (default_config Sign_Analysis Ctx_None) p
     = Some (tag_states SignValue (analyse_sign_report_with_state p))"
  by (simp add: default_config_def mk_analysis_config_def)

lemma analyse_config_with_state_interval_default:
  "analyse_config_with_state (default_config Interval_Analysis Ctx_None) p
     = Some (tag_states IntervalValue (analyse_interval_report_with_state p))"
  by (simp add: default_config_def mk_analysis_config_def)

lemma analyse_config_with_state_int_default:
  "analyse_config_with_state (default_config Int_Analysis Ctx_None) p
     = Some (tag_states IntDomValue (analyse_int_report_with_state p))"
  by (simp add: default_config_def mk_analysis_config_def)

text \<open>
  An explicit solver at \<open>Ctx_None\<close> now answers with a state-carrying report of its
  own table, and a context selection still does not: the flat
  \<^const>\<open>analyse_config\<close> stays the only report shape for those callers that want
  one, never a degraded view of the contextual result.
\<close>

lemma analyse_config_with_state_interval_explicit_join:
  "analyse_config_with_state
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_None \<rparr> p
   = Some (tag_states IntervalValue (interval_join.report_with_state p))"
  by simp

lemma analyse_config_with_state_entrystate_none:
  "analyse_config_with_state (default_config Interval_Analysis Ctx_EntryState) p = None"
  by (simp add: default_config_def mk_analysis_config_def)



text \<open>
  \<open>Some Solver_Warrow\<close> alongside \<open>Ctx_EntryState\<close> is the case this migration
  is most likely to accidentally make valid: \<open>Solver_Warrow\<close> is the exact
  solver entry-state analysis already uses internally, so a resolver bug
  that special-cased "does the explicit solver already match the implicit
  one" would silently start accepting a combination the CLI has always
  rejected. Pinned above at the \<^const>\<open>resolve_analysis_config\<close> level, in
  \<open>Analysis_Config\<close>'s own resolver regressions, and again here through the
  wrapper actually reachable from the CLI.
\<close>

end
