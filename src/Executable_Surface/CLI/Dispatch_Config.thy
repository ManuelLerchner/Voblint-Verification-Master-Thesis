theory Dispatch_Config
  imports Analyse_Dispatch
begin

section \<open>Config-driven dispatch\<close>

text \<open>
  \<^const>\<open>analyse\<close>/\<^const>\<open>analyse_with_solver\<close>/
  \<^const>\<open>analyse_with_state\<close> above each decide legality over exactly two of
  \<^type>\<open>analysis_config\<close>'s three axes at a time (domain+solver, ...) and stay
  the lower-level, typed entry points every consumer keeps using.
  \<^const>\<open>resolve_analysis_config\<close>
  (\<^theory>\<open>Voblint_CLI.Analysis_Config\<close>) decides all three axes' legality
  and defaults together; the three wrappers below each consume its \<^type>\<open>analysis_plan\<close>
  result and pick the one existing dispatcher call that already produces
  their report shape, rather than re-deciding legality or re-implementing
  a domain/solver/context case split of their own. None of the three
  existing report shapes below is replaced by a fourth, artificially
  unified one: \<open>check_report_entry list\<close>, \<open>(pp \<times> exp \<times> contextual_verdict)
  list\<close>, and the \<^typ>\<open>abstract_value abs_state\<close>-carrying report genuinely
  differ, and forcing one shape on all three would either lose the
  \<^const>\<open>Dead\<close> distinction the contextual report exists for, or fabricate a
  per-variable state no flat report has ever carried.
\<close>

definition analyse_config :: "analysis_config \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list option" where
  "analyse_config cfg p =
     (case resolve_analysis_config cfg of
        None \<Rightarrow> None
      | Some (Plan_Sign s) \<Rightarrow> analyse_with_solver Sign_Analysis s p
      | Some (Plan_Interval s) \<Rightarrow> analyse_with_solver Interval_Analysis s p
      | Some (Plan_Int s) \<Rightarrow> analyse_with_solver Int_Analysis s p
      | Some (Plan_Interval_EntryState _) \<Rightarrow> None
      | Some (Plan_Sign_EntryState _) \<Rightarrow> None
      | Some (Plan_Interval_CallString _ _) \<Rightarrow> None
      | Some (Plan_Sign_CallString _ _) \<Rightarrow> None
      | Some (Plan_Int_CallString _ _) \<Rightarrow> None
      | Some (Plan_Int_EntryState _) \<Rightarrow> None
      | Some (Plan_Parity s) \<Rightarrow> analyse_with_solver Parity_Analysis s p
      | Some (Plan_Parity_EntryState _) \<Rightarrow> None
      | Some (Plan_Parity_CallString _ _) \<Rightarrow> None
      | Some (Plan_Congruence s) \<Rightarrow> analyse_with_solver Congruence_Analysis s p
      | Some (Plan_Congruence_EntryState _) \<Rightarrow> None
      | Some (Plan_Congruence_CallString _ _) \<Rightarrow> None)"

text \<open>
  \<open>Plan_Interval_EntryState\<close> answers \<^const>\<open>None\<close> here on purpose: entry-state
  analysis has no flat, context-free \<open>check_report_entry list\<close> in the first
  place (a check can be \<^const>\<open>Dead\<close> in one context and decided in another,
  which \<^typ>\<open>check_result\<close> alone cannot express) -- \<open>analyse_config_ctx\<close>
  below is the wrapper a caller with an \<^type>\<open>analysis_plan\<close> resolving there
  should use instead, not a degraded flat view of the same result.
\<close>

definition analyse_config_ctx ::
    "analysis_config \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list option" where
  "analyse_config_ctx cfg p =
     (case resolve_analysis_config cfg of
        None \<Rightarrow> None
      | Some (Plan_Interval_EntryState Solver_Warrow) \<Rightarrow> Some (analyse_interval_entry_state p)
      | Some (Plan_Interval_EntryState Solver_Join) \<Rightarrow> Some (analyse_interval_entry_state_join p)
      | Some (Plan_Interval_EntryState Solver_PerOrigin) \<Rightarrow>
          Some (analyse_interval_entry_state_per_origin p)
      | Some (Plan_Interval_CallString Solver_Warrow k) \<Rightarrow>
          Some (analyse_interval_call_string_report k p)
      | Some (Plan_Interval_CallString Solver_Join k) \<Rightarrow>
          Some (analyse_interval_call_string_report_join k p)
      | Some (Plan_Interval_CallString Solver_PerOrigin k) \<Rightarrow>
          Some (analyse_interval_call_string_report_per_origin k p)
      | Some (Plan_Interval_EntryState Solver_WarrowPerOrigin) \<Rightarrow>
          Some (analyse_interval_entry_state_wpo p)
      | Some (Plan_Interval_CallString Solver_WarrowPerOrigin k) \<Rightarrow>
          Some (analyse_interval_call_string_report_wpo k p)
      | Some (Plan_Sign_CallString Solver_Join k) \<Rightarrow> Some (analyse_sign_call_string_report k p)
      | Some (Plan_Sign_CallString Solver_PerOrigin _) \<Rightarrow> None
      | Some (Plan_Sign_CallString Solver_Warrow _) \<Rightarrow> None
      | Some (Plan_Sign_CallString Solver_WarrowPerOrigin _) \<Rightarrow> None
      | Some (Plan_Sign_EntryState Solver_Join) \<Rightarrow> Some (analyse_sign_entry_state_report p)
      | Some (Plan_Sign_EntryState Solver_PerOrigin) \<Rightarrow> None
      | Some (Plan_Sign_EntryState Solver_Warrow) \<Rightarrow> None
      | Some (Plan_Sign_EntryState Solver_WarrowPerOrigin) \<Rightarrow> None
      | Some (Plan_Int_CallString Solver_Join k) \<Rightarrow> Some (analyse_int_call_string_report k p)
      | Some (Plan_Int_CallString Solver_PerOrigin _) \<Rightarrow> None
      | Some (Plan_Int_CallString Solver_Warrow k) \<Rightarrow>
          Some (analyse_int_call_string_report_warrow k p)
      | Some (Plan_Int_CallString Solver_WarrowPerOrigin _) \<Rightarrow> None
      | Some (Plan_Int_EntryState Solver_Join) \<Rightarrow> Some (analyse_int_entry_state_report p)
      | Some (Plan_Int_EntryState Solver_PerOrigin) \<Rightarrow> None
      | Some (Plan_Int_EntryState Solver_Warrow) \<Rightarrow> Some (analyse_int_entry_state_report_warrow p)
      | Some (Plan_Int_EntryState Solver_WarrowPerOrigin) \<Rightarrow> None
      | Some (Plan_Sign s) \<Rightarrow> map_option decided_report (analyse_with_solver Sign_Analysis s p)
      | Some (Plan_Interval s) \<Rightarrow>
          map_option decided_report (analyse_with_solver Interval_Analysis s p)
      | Some (Plan_Int s) \<Rightarrow> map_option decided_report (analyse_with_solver Int_Analysis s p)
      | Some (Plan_Parity s) \<Rightarrow> map_option decided_report (analyse_with_solver Parity_Analysis s p)
      | Some (Plan_Parity_EntryState Solver_Join) \<Rightarrow>
          Some (analyse_parity_entry_state_report p)
      | Some (Plan_Parity_EntryState _) \<Rightarrow> None
      | Some (Plan_Parity_CallString Solver_Join k) \<Rightarrow>
          Some (analyse_parity_call_string_report k p)
      | Some (Plan_Parity_CallString _ _) \<Rightarrow> None
      | Some (Plan_Congruence s) \<Rightarrow>
          map_option decided_report (analyse_with_solver Congruence_Analysis s p)
      | Some (Plan_Congruence_EntryState Solver_Join) \<Rightarrow>
          Some (analyse_congruence_entry_state_report p)
      | Some (Plan_Congruence_EntryState _) \<Rightarrow> None
      | Some (Plan_Congruence_CallString Solver_Join k) \<Rightarrow>
          Some (analyse_congruence_call_string_report k p)
      | Some (Plan_Congruence_CallString _ _) \<Rightarrow> None)"

text \<open>
  \<^const>\<open>analyse_with_state\<close> decides legality over the domain and solver axes
  only, so this wrapper is \<^const>\<open>Some\<close> at every context-free plan whose pairing
  has a solved table -- the implicit default and every explicit solver alike -- and
  \<^const>\<open>None\<close> at every context plan: a \<open>Ctx_EntryState\<close>/\<open>Ctx_CallString\<close>
  selection has a contextual report (\<open>analyse_config_ctx\<close>), not a flat
  state-carrying one, and is not silently degraded to it.
\<close>

fun analyse_config_with_state ::
    "analysis_config \<Rightarrow> imp_prog \<Rightarrow>
      (pp \<times> exp \<times> check_result \<times> bool \<times> abstract_value abs_state) list option"
where
  "analyse_config_with_state cfg p =
     (case resolve_analysis_config cfg of
        Some (Plan_Sign s) \<Rightarrow> analyse_with_state Sign_Analysis s p
      | Some (Plan_Interval s) \<Rightarrow> analyse_with_state Interval_Analysis s p
      | Some (Plan_Int s) \<Rightarrow> analyse_with_state Int_Analysis s p
      | Some (Plan_Parity s) \<Rightarrow> analyse_with_state Parity_Analysis s p
      | Some (Plan_Congruence s) \<Rightarrow> analyse_with_state Congruence_Analysis s p
      | Some (Plan_Sign_EntryState _) \<Rightarrow> None
      | Some (Plan_Sign_CallString _ _) \<Rightarrow> None
      | Some (Plan_Interval_EntryState _) \<Rightarrow> None
      | Some (Plan_Interval_CallString _ _) \<Rightarrow> None
      | Some (Plan_Int_EntryState _) \<Rightarrow> None
      | Some (Plan_Int_CallString _ _) \<Rightarrow> None
      | Some (Plan_Parity_EntryState _) \<Rightarrow> None
      | Some (Plan_Parity_CallString _ _) \<Rightarrow> None
      | Some (Plan_Congruence_EntryState _) \<Rightarrow> None
      | Some (Plan_Congruence_CallString _ _) \<Rightarrow> None
      | None \<Rightarrow> None)"

end
