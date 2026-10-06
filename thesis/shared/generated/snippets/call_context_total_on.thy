(* src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy *)
definition call_context_total_on ::
  "(cfg_node \<Rightarrow> 'c \<Rightarrow> store set) \<Rightarrow> 'c context_policy \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> bool"
where
  "call_context_total_on cover adm \<G> g \<longleftrightarrow>
     (\<forall>u dst pars args p cont ctx s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<longrightarrow> s \<in> cover u ctx
        \<longrightarrow> adm u ctx (call_info_of (CallEdge dst pars args) p) s
              (call_enter \<G> (CallEdge dst pars args) s) \<noteq> {})"
