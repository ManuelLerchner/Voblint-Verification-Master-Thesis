(* src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy *)
definition activation_collect ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'c call_context_rel \<Rightarrow> 'c
     \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> 'c \<Rightarrow> store set"
    ("\<A>\<^bsub>_,_,_,_,_\<^esub>") where
  "\<A>\<^bsub>\<G>,R,c\<^sub>0,g,S\<^esub> v c =
     {sink_store t | t. t \<in> \<T>\<^bsub>\<G>,g,S\<^esub> \<and> sink_node t = v
                        \<and> activation_context_rel \<G> R c\<^sub>0 g t c}"
