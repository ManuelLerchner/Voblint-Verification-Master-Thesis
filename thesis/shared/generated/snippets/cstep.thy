(* src/Program_Model/CFG/CFG_Exec.thy *)
inductive cstep :: "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> cconf \<Rightarrow> cconf \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>c/ _)" [51, 51, 51, 51] 50) for \<G> and g where
  Intra:
    "(u, a, v) \<in> intra g \<Longrightarrow> s' \<in> edge_step a s \<Longrightarrow>
     \<G>, g \<turnstile> (u, s, stk) \<rightarrow>\<^sub>c (v, s', stk)"
| Call:
    "(u, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls g \<Longrightarrow>
     \<G>, g \<turnstile> (u, s, stk)
       \<rightarrow>\<^sub>c (FunctionEntry q, call_enter \<G> (CallEdge dst pars actuals) s, (cont, dst, s) # stk)"
| Return:
    "\<G>, g \<turnstile> (FunctionResult q, t, (cont, dst, caller) # stk)
       \<rightarrow>\<^sub>c (cont, combine_collect \<G> dst caller t, stk)"
