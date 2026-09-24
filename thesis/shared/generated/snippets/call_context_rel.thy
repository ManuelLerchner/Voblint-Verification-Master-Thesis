(* src/Program_Model/CFG/Collecting/LTR_Activation_Context.thy *)
type_synonym 'c call_context_rel =
  "cfg_node \<Rightarrow> 'c \<Rightarrow> call_info \<Rightarrow> store \<Rightarrow> store \<Rightarrow> 'c \<Rightarrow> bool"
