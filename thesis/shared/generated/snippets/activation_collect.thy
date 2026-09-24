(* src/Program_Model/CFG/Collecting/LTR_Activation_Context.thy *)
definition activation_collect ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'c call_context_rel \<Rightarrow> 'c
     \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> 'c \<Rightarrow> store set"
    ("\<A>\<^bsub>_,_,_,_,_\<^esub>") where
  "\<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v c =
     {sink_store t | t. t \<in> \<T>\<^bsub>\<G>,g,S\<^esub> \<and> sink_node t = v
                        \<and> trace_context \<G> R startcontext g t c}"
