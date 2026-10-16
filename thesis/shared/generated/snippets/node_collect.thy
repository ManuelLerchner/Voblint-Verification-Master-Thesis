(* src/Program_Model/CFG/Collecting/Activation_Trace_Collect.thy *)
definition node_collect ::
    "kenv \<Rightarrow> (var_id, exp) gcfg \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> store set"
    ("\<C>\<^bsub>_,_,_\<^esub>") where
  "node_collect \<kappa> g S v =
     {sink_store t | t. t \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub> \<and> sink_node t = v}"
