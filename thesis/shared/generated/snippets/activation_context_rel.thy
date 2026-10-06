(* src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy *)
inductive activation_context_rel ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'c context_policy \<Rightarrow> 'c \<Rightarrow> cfg \<Rightarrow> activation_trace \<Rightarrow> 'c \<Rightarrow> bool"
  for \<G> :: "vname \<Rightarrow> bool" and adm :: "'c context_policy" and c\<^sub>0 :: 'c and g :: cfg
where
  Root [intro]: "activation_context_rel \<G> adm c\<^sub>0 g (Root xs) c\<^sub>0"
| Call [intro]:
    "activation_context_rel \<G> adm c\<^sub>0 g parent ctx
     \<Longrightarrow> admits_call_context \<G> g adm (sink_node parent) ctx p (sink_store parent) es ctx'
     \<Longrightarrow> activation_context_rel \<G> adm c\<^sub>0 g (Call parent ((FunctionEntry p, es) # xs)) ctx'"
| Resume [intro]:
    "activation_context_rel \<G> adm c\<^sub>0 g current ctx
     \<Longrightarrow> activation_context_rel \<G> adm c\<^sub>0 g (Resume current callee xs) ctx"
