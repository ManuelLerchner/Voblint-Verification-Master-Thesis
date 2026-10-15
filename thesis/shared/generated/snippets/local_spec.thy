(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
record ('vr,'e,'s) glocal_spec =
  ls_query :: "'e gchannel \<Rightarrow> 's \<Rightarrow> 'e gchannel"
  ls_skip :: "'e gchannel \<Rightarrow> 's \<Rightarrow> 's"
  ls_assign :: "'e gchannel \<Rightarrow> 'vr \<Rightarrow> 'e \<Rightarrow> 's \<Rightarrow> 's"
  ls_special :: "'e gchannel \<Rightarrow> 'e gspecial_call \<Rightarrow> 'vr \<Rightarrow> 's \<Rightarrow> 's"
  ls_branch :: "'e gchannel \<Rightarrow> 'e \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 's"
  ls_body :: "'e gchannel \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's"
  ls_return :: "'e gchannel \<Rightarrow> 'e option \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's"
  ls_event :: "'e gchannel \<Rightarrow> 'e ganalysis_event \<Rightarrow> 's \<Rightarrow> 's"
  ls_enter :: "'e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<times> 's \<Rightarrow> ('s \<times> 's) list"
  ls_combine_env :: "'e gchannel \<Rightarrow> 'e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
  ls_combine_assign :: "'e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
