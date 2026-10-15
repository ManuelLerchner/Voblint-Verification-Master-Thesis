(* src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy *)
inductive_set gvalid_activation_trace ::
    "('v, 'e) gcfg \<Rightarrow> ('v \<Rightarrow> int) set \<Rightarrow> 'v gactivation_trace set"
  for g and S where
  root:
    "s \<in> S
     \<Longrightarrow> Root [(cfg_entry g, s)] \<in> gvalid_activation_trace g S"
| intra:
    "t \<in> gvalid_activation_trace g S
     \<Longrightarrow> (sink_node t, a, v) \<in> intra g
     \<Longrightarrow> s' \<in> gedge_step a (sink_store t)
     \<Longrightarrow> extend t (v, s') \<in> gvalid_activation_trace g S"
| call:
    "caller \<in> gvalid_activation_trace g S
     \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls g
     \<Longrightarrow> Call caller
           [(FunctionEntry p,
             gcall_enter (CallEdge dst pars args) (sink_store caller))]
         \<in> gvalid_activation_trace g S"
| ret:
    "callee \<in> gvalid_activation_trace g S
     \<Longrightarrow> caller_of callee = Some caller
     \<Longrightarrow> sink_node callee = FunctionResult p
     \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls g
     \<Longrightarrow> Resume caller callee
           (path_of caller
              @ [(cont, gcombine_collect dst
                          (sink_store caller) (sink_store callee))])
         \<in> gvalid_activation_trace g S"
