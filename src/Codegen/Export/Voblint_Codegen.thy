theory Voblint_Codegen
  imports
    "Voblint_CLI.State_Report_GraphViz"
begin

section "Code export surface"

text \<open>
  This session owns executable exports; the examples session proves and demonstrates the
  exported definitions without materializing generated code.

  One export block, deliberately. There used to be a second, narrower one
  (\<open>Voblint_Analyse_OCaml\<close>) whose only consumer was the external OCaml regression driver
  under \<open>codegen/regression/ocaml/\<close>, which needs a handful of CFG-inspection constants
  the CLI itself never calls. Two blocks did not make that surface any narrower: Isabelle
  emits the reachable transitive closure of whatever is named, so both files carried
  essentially the same machinery, differing by exactly those CFG constants and costing
  around 8,400 duplicated generated lines. Naming the constants here instead and pointing
  the driver at this module keeps one generated artifact for one analysis.

  This is emphatically not the project's public API boundary. \<^emph>\<open>Nothing\<close> about an
  \<open>export_code\<close> list makes the emitted module narrow --- the serializer decides what comes
  along --- so a supported external surface, if one is wanted, belongs in a hand-written
  OCaml facade over this module rather than in the shape of this list.
\<close>

text \<open>
  The roots below are the \<^emph>\<open>intended callable surface\<close>: what handwritten OCaml under
  \<open>cli/\<close>, \<open>codegen/regression/ocaml/\<close> and \<open>tests/property/\<close> actually calls. Everything else
  in the emitted module is serializer-reachable implementation detail --- naming fewer
  roots would not remove it, since Isabelle emits the transitive closure regardless. That
  distinction is a documentation matter here, not one this project enforces at the type
  level: the generated module \<^emph>\<open>is\<close> the API, with no handwritten re-export layer in
  between that could reinterpret a constructor or a conversion.

  Analysis entry goes through \<^const>\<open>analyse_config\<close>/\<^const>\<open>analyse_config_ctx\<close>/
  \<^const>\<open>analyse_config_with_state\<close>, which consult
  \<^const>\<open>resolve_analysis_config\<close> internally, so the CLI never re-decides legality. The
  pre-configuration entry points \<open>analyse_with_state\<close>/\<open>analyse_with_solver\<close> are not
  roots: nothing handwritten calls them, and the configuration path supersedes them.
  \<^const>\<open>analyse\<close> stays, because the external regression oracle calls it directly
  as its domain-dispatch check.
\<close>

export_code
  analyse Sign_Analysis Interval_Analysis Int_Analysis Parity_Analysis
  Ctx_None Ctx_EntryState Ctx_CallString
  state_report_graph_snapshot_auto full_state_graph_snapshot_auto
  entry_state_report_graph_snapshot_auto entry_state_full_state_graph_snapshot_auto
  entry_state_ctx_graph_snapshot_auto cs_ctx_graph_snapshot_auto
  state_report_export_auto full_state_export_auto full_state_checked_payload_auto
  entry_state_report_export_auto entry_state_full_state_export_auto
  entry_state_full_state_checked_export_auto solver_checked_payload_auto
  entry_state_verdicts_for entry_state_globals_for solver_globals_for cs_globals_for
  entry_state_ctx_export_auto cs_ctx_export_auto
  xn_id xn_label xn_kind xn_status xn_lines
  xe_src xe_dst xe_kind xe_label
  xc_id xc_label xc_nodes
  xg_clusters xg_nodes xg_edges
  XN_Entry XN_Exit XN_ProcEntry XN_ProcExit XN_Point XN_Global XN_Source
  XE_Intra XE_Enter XE_Combine XE_CallToReturn XE_GlobalRead XE_GlobalWrite
  NS_Plain NS_Proved NS_Refuted NS_Unknown NS_Unreachable NS_Exit
  exp_vnames_list string_of_abstract_value
  check_cond_text check_state_text
  mk_program mk_program_typed TV proc_decl_of proc_decl_of_typed declared_global_vars pretty_string_of_program
  SKIP com.Call com.If Assign Seq While Return Check
  N V Plus Minus Times
  exp.Not And Or Less exp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  integer_of_char
  compile_program cfg_intra_list cfg_calls_list prog_stmt_post_order
  EA_Nop EA_Assign EA_Special EA_Assume EA_AssumeNot EA_Ret EA_Check CallEdge
  Nondet_Int Min Max
  TN TVar TPlus TMinus TTimes TCast TLess TEq TNot TAnd TOr texp_erase
  I8 U8 I16 U16 I32 U32 I64 U64
  string_of_exp
  wf_program_compile_input_exec
  Solver_Join Solver_PerOrigin Solver_Warrow Solver_WarrowPerOrigin
  mk_analysis_config valid_analysis_config
  analyse_config analyse_config_ctx analyse_config_with_state
  Dead Decided
  in OCaml file_prefix "Voblint_CLI"

end


