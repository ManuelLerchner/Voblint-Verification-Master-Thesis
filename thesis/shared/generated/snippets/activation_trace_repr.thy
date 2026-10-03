(* src/Program_Model/Compile/Source_To_Trace.thy *)
definition activation_trace_repr ::
  "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> cconf \<Rightarrow> activation_trace \<Rightarrow> bool" where
  "activation_trace_repr \<G> g S cf t = (case cf of (v, s, stk) \<Rightarrow>
     t \<in> \<T>\<^bsub>\<G>,g,S\<^esub> \<and> sink_node t = v \<and> sink_store t = s \<and> stack_repr g stk t)"
