(* src/Program_Model/CFG/Collecting/LTR_Activation_Context.thy *)
inductive trace_context ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'c call_context_rel \<Rightarrow> 'c \<Rightarrow> cfg \<Rightarrow> ltr \<Rightarrow> 'c \<Rightarrow> bool"
  for \<G> :: "vname \<Rightarrow> bool" and R :: "'c call_context_rel" and startcontext :: 'c and g :: cfg
where
  Root: "trace_context \<G> R startcontext g (Root xs) startcontext"
| Call:
    "trace_context \<G> R startcontext g parent ctx
     \<Longrightarrow> admits_call_context \<G> g R (sink_node parent) ctx p (sink_store parent) es ctx'
     \<Longrightarrow> trace_context \<G> R startcontext g (Call parent ((FunctionEntry p, es) # xs)) ctx'"
| Resume:
    "trace_context \<G> R startcontext g current ctx
     \<Longrightarrow> trace_context \<G> R startcontext g (Resume current callee xs) ctx"
