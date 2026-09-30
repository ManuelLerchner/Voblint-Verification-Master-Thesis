(* src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy *)
inductive activation_context_rel ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'c call_context_rel \<Rightarrow> 'c \<Rightarrow> cfg \<Rightarrow> activation_trace \<Rightarrow> 'c \<Rightarrow> bool"
  for \<G> :: "vname \<Rightarrow> bool" and R :: "'c call_context_rel" and c\<^sub>0 :: 'c and g :: cfg
where
  Root: "activation_context_rel \<G> R c\<^sub>0 g (Root xs) c\<^sub>0"
| Call:
    "activation_context_rel \<G> R c\<^sub>0 g parent ctx
     \<Longrightarrow> admits_call_context \<G> g R (sink_node parent) ctx p (sink_store parent) es ctx'
     \<Longrightarrow> activation_context_rel \<G> R c\<^sub>0 g (Call parent ((FunctionEntry p, es) # xs)) ctx'"
| Resume:
    "activation_context_rel \<G> R c\<^sub>0 g current ctx
     \<Longrightarrow> activation_context_rel \<G> R c\<^sub>0 g (Resume current callee xs) ctx"
