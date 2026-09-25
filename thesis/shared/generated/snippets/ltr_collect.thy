(* src/Program_Model/CFG/Collecting/LTR_Collect.thy *)
definition ltr_collect ::
    "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> store set"
    ("\<C>\<^bsub>_,_,_\<^esub>") where
  "\<C>\<^bsub>\<G>,g,S\<^esub> v =
     {sink_store t | t. t \<in> \<T>\<^bsub>\<G>,g,S\<^esub> \<and> sink_node t = v}"
