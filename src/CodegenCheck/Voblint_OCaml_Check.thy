theory Voblint_OCaml_Check
  imports Voblint_Codegen.Voblint_Codegen
begin

text \<open>
  CI-only OCaml compilation check for the \<open>export_code\<close> declarations in
  \<^theory>\<open>Voblint_Codegen.Voblint_Codegen\<close>. Kept in a separate
  session, built only by CI's Linux job (see \<open>.github/workflows/ci.yml\<close>),
  not by the default \<open>Voblint_Examples\<close> or \<open>Voblint_Codegen\<close> build.

  On Apple Silicon macOS, Isabelle's bundled \<open>opam\<close> (2.0.7) is an x86_64
  binary, so its managed OCaml toolchain links against an x86_64
  \<open>libgmp\<close> while the platform (and Homebrew's own \<open>libgmp\<close>) is arm64 ---
  an environment/toolchain mismatch, not evidence that the generated OCaml
  itself is broken. Isolating this check in its own session keeps the
  default \<open>Voblint_Examples\<close> and \<open>Voblint_Codegen\<close> builds free of it;
  CI only builds this session on Linux, where the architecture mismatch does
  not occur.

\<close>

text \<open>
  This list mirrors \<^theory>\<open>Voblint_Codegen.Voblint_Codegen\<close>'s own export roots, so the
  compilation check covers the surface actually shipped rather than the historical subset
  it began as. It drifted once already --- the shipped export grew context modes, solver
  selection, the configuration path, GraphViz entry points and a fourth domain while this
  list stayed at two domains and the pre-configuration entry points --- which meant the
  one check whose job is catching bad generated OCaml was checking code the CLI no longer
  calls. Keep the two lists in step.
\<close>

export_code
  analyse Sign_Analysis Interval_Analysis Int_Analysis Parity_Analysis
  Ctx_None Ctx_EntryState Ctx_CallString
  SignValue IntervalValue IntDomValue ParityValue
  state_report_dot_auto state_report_graph_snapshot_auto
  full_state_dot_auto full_state_graph_snapshot_auto
  entry_state_report_dot_auto entry_state_report_graph_snapshot_auto
  entry_state_full_state_dot_auto entry_state_full_state_graph_snapshot_auto
  entry_state_ctx_dot_auto entry_state_ctx_graph_snapshot_auto
  cs_ctx_dot_auto cs_ctx_graph_snapshot_auto
  exp_vnames_list string_of_abstract_value
  mk_program proc_decl_of declared_global_vars pretty_string_of_program
  SKIP com.Call com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  exp.Not And Or Less exp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  compile_program cfg_intra_list cfg_calls_list
  EA_Nop EA_Assign EA_Special EA_Assume EA_AssumeNot EA_Ret EA_Check CallEdge Nondet_Int
  string_of_exp
  wf_program_compile_input_exec
  Solver_Join Solver_PerOrigin Solver_Warrow
  mk_analysis_config valid_analysis_config
  analyse_config analyse_config_ctx analyse_config_with_state
  Dead Decided
  checking OCaml

end
