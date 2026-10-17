(* src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy *)
inductive_set valid_activation_trace ::
    "kenv \<Rightarrow> (var_id, exp) gcfg \<Rightarrow> store set \<Rightarrow> activation_trace set"
    ("\<T>\<^bsub>_,_,_\<^esub>")
  for \<kappa> g and S where
  root:
    "s \<in> S
     \<Longrightarrow> Root [(cfg_entry g, s)] \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub>"
| intra:
    "t \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub>
     \<Longrightarrow> (sink_node t, a, v) \<in> intra g
     \<Longrightarrow> s' \<in> edge_step \<kappa> a (sink_store t)
     \<Longrightarrow> extend t (v, s') \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub>"
| call:
    "caller \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub>
     \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls g
     \<Longrightarrow> Call caller
           [(FunctionEntry p,
             call_enter \<kappa> (CallEdge dst pars args) (sink_store caller))]
         \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub>"
| ret:
    "callee \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub>
     \<Longrightarrow> caller_of callee = Some caller
     \<Longrightarrow> sink_node callee = FunctionResult p
     \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls g
     \<Longrightarrow> Resume caller callee
           (path_of caller
              @ [(cont, combine_collect \<kappa> dst
                          (sink_store caller) (sink_store callee))])
         \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub>"
