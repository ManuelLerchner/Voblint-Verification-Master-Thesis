(* src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy *)
inductive activation_context_rel ::
  "kenv \<Rightarrow> 'c call_context_policy \<Rightarrow> 'c \<Rightarrow> (var_id, exp) gcfg \<Rightarrow> activation_trace \<Rightarrow> 'c \<Rightarrow> bool"
  for \<kappa> :: kenv and adm :: "'c call_context_policy" and c\<^sub>0 :: 'c and g :: "(var_id, exp) gcfg"
where
  Root [intro]: "activation_context_rel \<kappa> adm c\<^sub>0 g (Root xs) c\<^sub>0"
| Call [intro]:
    "activation_context_rel \<kappa> adm c\<^sub>0 g caller c
     \<Longrightarrow> admits_call_context \<kappa> g adm (sink_node caller) c p (sink_store caller) es c'
     \<Longrightarrow> activation_context_rel \<kappa> adm c\<^sub>0 g (Call caller ((FunctionEntry p, es) # xs)) c'"
| Resume [intro]:
    "activation_context_rel \<kappa> adm c\<^sub>0 g current c
     \<Longrightarrow> activation_context_rel \<kappa> adm c\<^sub>0 g (Resume current callee xs) c"
