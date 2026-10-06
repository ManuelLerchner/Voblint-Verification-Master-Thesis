(* src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy *)
type_synonym 'c context_policy =
  "cfg_node \<Rightarrow> 'c \<Rightarrow> call_info \<Rightarrow> store \<Rightarrow> store \<Rightarrow> 'c set"
