theory Voblint_Codegen
  imports
    "Voblint_CLI.State_Report_GraphViz"
begin

section "Code export surfaces"

text "
  This session owns executable exports. The examples session proves and
  demonstrates the exported definitions without materializing generated code.
"

export_code
  analyse Sign_Analysis Interval_Analysis Int_Analysis
  analyse_with_state SignValue IntervalValue IntDomValue
  analyse_ctx Ctx_None Ctx_EntryState
  mk_program proc_decl_of
  SKIP com.Call com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  exp.Not And Or Less exp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  compile_program prog_main_name cfg_intra_list cfg_calls_list cfg_entry
  EA_Nop EA_Assign EA_Special EA_Assume EA_AssumeNot EA_Ret EA_Check CallEdge Nondet_Int
  string_of_exp
  wf_program_compile_input_exec
  analyse_sign_result analyse_interval_td_result analyse_int_result
  analyse_interval_entry_state_result analyse_interval_entry_state_result_for
  result_keys contexts_at lookup_context lookup_joined_state node_live_ex
  is_reachable_point map_point_state normalize_point
  Dead Decided verdict_check_result aggregate_verdicts check_dead
  entry_state_check_projection
  in OCaml file_prefix "Voblint_Analyse_OCaml"

export_code
  analyse Sign_Analysis Interval_Analysis Int_Analysis
  analyse_ctx Ctx_None Ctx_EntryState Ctx_CallString
  analyse_with_state SignValue IntervalValue IntDomValue
  state_report_dot_auto state_report_graph_snapshot_auto
  full_state_dot_auto full_state_graph_snapshot_auto
  entry_state_report_dot_auto entry_state_report_graph_snapshot_auto
  entry_state_full_state_dot_auto entry_state_full_state_graph_snapshot_auto
  entry_state_ctx_dot_auto entry_state_ctx_graph_snapshot_auto
  exp_vnames_list string_of_abstract_value
  is_bottom_abstract_value program_vars
  mk_program proc_decl_of declared_global_vars pretty_string_of_program
  SKIP com.Call com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  exp.Not And Or Less exp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  string_of_exp
  wf_program_compile_input_exec
  analyse_with_solver Solver_Join Solver_PerOrigin Solver_Warrow
  mk_analysis_config
  Plan_Sign Plan_Sign_EntryState Plan_Sign_CallString Plan_Interval Plan_Interval_EntryState Plan_Interval_CallString Plan_Int Plan_Int_EntryState Plan_Int_CallString
  resolve_analysis_config valid_analysis_config
  analyse_config analyse_config_ctx analyse_config_with_state
  analyse_sign_result analyse_interval_td_result analyse_int_result
  analyse_interval_entry_state_result analyse_interval_entry_state_result_for
  analyse_interval_call_string_result analyse_interval_call_string_result_for
  analyse_interval_call_string_report
  analyse_sign_call_string_result analyse_sign_call_string_result_for
  analyse_sign_call_string_report
  analyse_sign_entry_state_result analyse_sign_entry_state_result_for
  analyse_sign_entry_state_report
  analyse_int_call_string_result analyse_int_call_string_result_for
  analyse_int_call_string_report
  analyse_int_entry_state_result analyse_int_entry_state_result_for
  analyse_int_entry_state_report
  result_keys contexts_at lookup_context lookup_joined_state node_live_ex
  is_reachable_point map_point_state normalize_point
  Dead Decided verdict_check_result aggregate_verdicts check_dead
  entry_state_check_projection
  in OCaml file_prefix "Voblint_CLI"

end


