(* src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy *)
inductive activation_context_rel ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'c context_policy \<Rightarrow> 'c \<Rightarrow> cfg \<Rightarrow> activation_trace \<Rightarrow> 'c \<Rightarrow> bool"
  for \<G> :: "vname \<Rightarrow> bool" and adm :: "'c context_policy" and c\<^sub>0 :: 'c and g :: cfg
where
  Root [intro]: "activation_context_rel \<G> adm c\<^sub>0 g (Root xs) c\<^sub>0"
| Call [intro]:
    "activation_context_rel \<G> adm c\<^sub>0 g caller c
     \<Longrightarrow> admits_call_context \<G> g adm (sink_node caller) c p (sink_store caller) es c'
     \<Longrightarrow> activation_context_rel \<G> adm c\<^sub>0 g (Call caller ((FunctionEntry p, es) # xs)) c'"
| Resume [intro]:
    "activation_context_rel \<G> adm c\<^sub>0 g current c
     \<Longrightarrow> activation_context_rel \<G> adm c\<^sub>0 g (Resume current callee xs) c"
