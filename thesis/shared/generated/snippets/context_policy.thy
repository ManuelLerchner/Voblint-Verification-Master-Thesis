(* src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy *)
type_synonym ('v, 'e, 'c) gcontext_policy =
  "cfg_node \<Rightarrow> 'c \<Rightarrow> ('v, 'e) gcall_info \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> 'c set"
