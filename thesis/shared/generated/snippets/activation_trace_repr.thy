(* src/Program_Model/Compile/Source_To_Trace.thy *)
definition gactivation_trace_repr ::
  "('v, 'e) gcfg \<Rightarrow> ('v \<Rightarrow> int) set \<Rightarrow> 'v gcconf \<Rightarrow> 'v gactivation_trace \<Rightarrow> bool" where
  "gactivation_trace_repr g S cf t = (case cf of (v, s, stk) \<Rightarrow>
     t \<in> gvalid_activation_trace g S \<and> sink_node t = v \<and> sink_store t = s \<and> stack_repr g stk t)"
