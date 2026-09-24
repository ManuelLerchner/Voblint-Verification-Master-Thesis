(* src/Program_Model/Compile/Source_To_Trace.thy *)
inductive stack_repr :: "cfg \<Rightarrow> cframe list \<Rightarrow> ltr \<Rightarrow> bool" for g where
  empty: "caller_of t = None \<Longrightarrow> stack_repr g [] t"
| frame: "caller_of t = Some c \<Longrightarrow> sink_store c = caller
          \<Longrightarrow> fst (hd (path t)) = FunctionEntry p
          \<Longrightarrow> (sink_node c, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
          \<Longrightarrow> stack_repr g stk c
          \<Longrightarrow> stack_repr g ((cont, dst, caller) # stk) t"
