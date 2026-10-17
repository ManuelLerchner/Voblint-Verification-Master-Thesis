(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
record 's local_spec =
  ls_query :: "channel \<Rightarrow> 's \<Rightarrow> channel"
  ls_skip :: "channel \<Rightarrow> 's \<Rightarrow> 's"
  ls_assign :: "channel \<Rightarrow> var_id \<Rightarrow> exp \<Rightarrow> 's \<Rightarrow> 's"
  ls_special :: "channel \<Rightarrow> exp gspecial_call \<Rightarrow> var_id \<Rightarrow> 's \<Rightarrow> 's"
  ls_branch :: "channel \<Rightarrow> exp \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 's"
  ls_body :: "channel \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's"
  ls_return :: "channel \<Rightarrow> exp option \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's"
  ls_event :: "channel \<Rightarrow> analysis_event \<Rightarrow> 's \<Rightarrow> 's"
  ls_enter :: "channel \<Rightarrow> call_info \<Rightarrow> 's \<times> 's \<Rightarrow> ('s \<times> 's) list"
  ls_combine_env :: "channel \<Rightarrow> channel \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
  ls_combine_assign :: "channel \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
