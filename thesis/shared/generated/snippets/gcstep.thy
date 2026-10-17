(* src/Program_Model/CFG/CFG_Exec.thy *)
inductive gcstep :: "('v, 'e) gcfg \<Rightarrow> 'v gcconf \<Rightarrow> 'v gcconf \<Rightarrow> bool"
    ("(_ \<turnstile>/ _ \<rightarrow>\<^sub>c/ _)" [51, 51, 51] 50) for g where
  Intra [intro]:
    "(u, a, v) \<in> intra g \<Longrightarrow> s' \<in> gedge_step a s \<Longrightarrow> g \<turnstile> (u, s, stk) \<rightarrow>\<^sub>c (v, s', stk)"
| Call [intro]:
    "(u, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls g \<Longrightarrow>
     g \<turnstile> (u, s, stk)
       \<rightarrow>\<^sub>c (FunctionEntry q, gcall_enter (CallEdge dst pars actuals) s, (cont, dst, s) # stk)"
| Return [intro]:
    "g \<turnstile> (FunctionResult q, t, (cont, dst, caller) # stk)
       \<rightarrow>\<^sub>c (cont, gcombine_collect dst caller t, stk)"
