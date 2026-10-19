(* src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy *)
definition activation_collect ::
  "kenv \<Rightarrow> 'c call_context_policy \<Rightarrow> 'c \<Rightarrow> (var_id, exp) gcfg
     \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> 'c \<Rightarrow> store set"
    ("\<A>\<^bsub>_,_,_,_,_\<^esub>") where
  "activation_collect \<kappa> adm c\<^sub>0 g S v c =
     {sink_store t | t. t \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub> \<and> sink_node t = v
                        \<and> activation_context_rel \<kappa> adm c\<^sub>0 g t c}"
