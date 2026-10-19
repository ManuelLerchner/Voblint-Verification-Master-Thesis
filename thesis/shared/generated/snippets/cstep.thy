(* src/Program_Model/CFG/CFG_Exec.thy *)
inductive cstep :: "kenv \<Rightarrow> (var_id, exp) gcfg \<Rightarrow> cconf \<Rightarrow> cconf \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>c/ _)" [51, 51, 51, 51] 50) for \<kappa> g where
  Intra [intro]:
    "(u, a, v) \<in> intra g \<Longrightarrow> s' \<in> edge_step \<kappa> a s \<Longrightarrow> \<kappa>,g \<turnstile> (u, s, stk) \<rightarrow>\<^sub>c (v, s', stk)"
| Call [intro]:
    "(u, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls g \<Longrightarrow>
     \<kappa>,g \<turnstile> (u, s, stk)
       \<rightarrow>\<^sub>c (FunctionEntry q, call_enter \<kappa> (CallEdge dst pars actuals) s, (cont, dst, s) # stk)"
| Return [intro]:
    "\<kappa>,g \<turnstile> (FunctionResult q, t, (cont, dst, caller) # stk)
       \<rightarrow>\<^sub>c (cont, combine_collect \<kappa> dst caller t, stk)"
