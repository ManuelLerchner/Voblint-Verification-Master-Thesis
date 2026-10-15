(* src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy *)
definition gactivation_collect ::
  "('v, 'e, 'c) gcontext_policy \<Rightarrow> 'c \<Rightarrow> ('v, 'e) gcfg
     \<Rightarrow> ('v \<Rightarrow> int) set \<Rightarrow> cfg_node \<Rightarrow> 'c \<Rightarrow> ('v \<Rightarrow> int) set" where
  "gactivation_collect adm c\<^sub>0 g S v c =
     {sink_store t | t. t \<in> gvalid_activation_trace g S \<and> sink_node t = v
                        \<and> gactivation_context_rel adm c\<^sub>0 g t c}"
