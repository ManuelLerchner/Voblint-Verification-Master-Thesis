(* src/Program_Model/CFG/Collecting/Activation_Trace_Collect.thy *)
definition gnode_collect ::
    "('v, 'e) gcfg \<Rightarrow> ('v \<Rightarrow> int) set \<Rightarrow> cfg_node \<Rightarrow> ('v \<Rightarrow> int) set" where
  "gnode_collect g S v =
     {sink_store t | t. t \<in> gvalid_activation_trace g S \<and> sink_node t = v}"
