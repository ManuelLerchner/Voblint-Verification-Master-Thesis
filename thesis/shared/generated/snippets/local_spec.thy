(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
record 's local_spec =
  ls_query :: "answers \<Rightarrow> 's \<Rightarrow> answers"
  ls_skip :: "answers \<Rightarrow> 's \<Rightarrow> 's"
  ls_assign :: "answers \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> 's \<Rightarrow> 's"
  ls_special :: "answers \<Rightarrow> special_call \<Rightarrow> vname \<Rightarrow> 's \<Rightarrow> 's"
  ls_branch :: "answers \<Rightarrow> exp \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 's"
  ls_body :: "answers \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's"
  ls_return :: "answers \<Rightarrow> exp option \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's"
  ls_event :: "answers \<Rightarrow> analysis_event \<Rightarrow> 's \<Rightarrow> 's"
  ls_enter :: "answers \<Rightarrow> call_info \<Rightarrow> 's \<times> 's \<Rightarrow> ('s \<times> 's) list"
  ls_combine_env :: "answers \<Rightarrow> answers \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
  ls_combine_assign :: "answers \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
