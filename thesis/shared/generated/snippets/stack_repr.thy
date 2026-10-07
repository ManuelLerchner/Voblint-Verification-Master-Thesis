(* src/Program_Model/Compile/Source_To_Trace.thy *)
inductive stack_repr :: "cfg \<Rightarrow> cframe list \<Rightarrow> activation_trace \<Rightarrow> bool" for g where
  empty [intro]: "caller_of t = None \<Longrightarrow> stack_repr g [] t"
| frame [intro]: "caller_of t = Some caller \<Longrightarrow> sink_store caller = s
          \<Longrightarrow> fst (hd (path_of t)) = FunctionEntry p
          \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
          \<Longrightarrow> stack_repr g stk caller
          \<Longrightarrow> stack_repr g ((cont, dst, s) # stk) t"
