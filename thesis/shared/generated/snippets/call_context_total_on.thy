(* src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy *)
definition gcall_context_total_on ::
  "(cfg_node \<Rightarrow> 'c \<Rightarrow> ('v \<Rightarrow> int) set) \<Rightarrow> ('v, 'e, 'c) gcontext_policy \<Rightarrow> ('v, 'e) gcfg \<Rightarrow> bool"
where
  "gcall_context_total_on cover adm g \<longleftrightarrow>
     (\<forall>u dst pars args p cont ctx s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<longrightarrow> s \<in> cover u ctx
        \<longrightarrow> adm u ctx (call_info_of (CallEdge dst pars args) p) s
              (gcall_enter (CallEdge dst pars args) s) \<noteq> {})"
