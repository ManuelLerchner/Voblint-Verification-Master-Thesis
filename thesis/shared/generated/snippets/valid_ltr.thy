(* src/Program_Model/CFG/Collecting/LTR_Def.thy *)
inductive_set valid_ltr ::
    "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> ltr set"
    ("\<T>\<^bsub>_,_,_\<^esub>")
  for \<G> and g and S where
  init:
    "s \<in> S
     \<Longrightarrow> Root [(cfg_entry g, s)] \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"
| intra:
    "t \<in> \<T>\<^bsub>\<G>,g,S\<^esub>
     \<Longrightarrow> (sink_node t, a, v) \<in> intra g
     \<Longrightarrow> s' \<in> edge_step a (sink_store t)
     \<Longrightarrow> extend t (v, s') \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"
| call:
    "caller \<in> \<T>\<^bsub>\<G>,g,S\<^esub>
     \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls g
     \<Longrightarrow> Call caller
           [(FunctionEntry p,
             call_enter \<G> (CallEdge dst pars args) (sink_store caller))]
         \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"
| ret:
    "callee \<in> \<T>\<^bsub>\<G>,g,S\<^esub>
     \<Longrightarrow> caller_of callee = Some caller
     \<Longrightarrow> sink_node callee = FunctionResult p
     \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls g
     \<Longrightarrow> Resume caller callee
           (path caller
              @ [(cont, combine_collect \<G> dst
                          (sink_store caller) (sink_store callee))])
         \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"
