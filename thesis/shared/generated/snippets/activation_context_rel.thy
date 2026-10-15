(* src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy *)
inductive gactivation_context_rel ::
  "('v, 'e, 'c) gcontext_policy \<Rightarrow> 'c \<Rightarrow> ('v, 'e) gcfg \<Rightarrow> 'v gactivation_trace \<Rightarrow> 'c \<Rightarrow> bool"
  for adm :: "('v, 'e, 'c) gcontext_policy" and c\<^sub>0 :: 'c and g :: "('v, 'e) gcfg"
where
  Root [intro]: "gactivation_context_rel adm c\<^sub>0 g (Root xs) c\<^sub>0"
| Call [intro]:
    "gactivation_context_rel adm c\<^sub>0 g caller c
     \<Longrightarrow> gadmits_call_context g adm (sink_node caller) c p (sink_store caller) es c'
     \<Longrightarrow> gactivation_context_rel adm c\<^sub>0 g (Call caller ((FunctionEntry p, es) # xs)) c'"
| Resume [intro]:
    "gactivation_context_rel adm c\<^sub>0 g current c
     \<Longrightarrow> gactivation_context_rel adm c\<^sub>0 g (Resume current callee xs) c"
