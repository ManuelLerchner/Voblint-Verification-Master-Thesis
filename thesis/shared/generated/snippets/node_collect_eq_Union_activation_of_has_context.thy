(* src/Program_Model/CFG/Collecting/Activation_Trace_Collect.thy *)
theorem node_collect_eq_Union_activation_of_has_context:
  assumes has_ctx: "\<And>t. t \<in> \<T> \<Longrightarrow> \<exists>c. activation_context_rel \<G> adm c\<^sub>0 g t c"
  shows "\<C> v = (\<Union>c. \<A>\<^bsub>\<G>,adm,c\<^sub>0,g,S\<^esub> v c)"
