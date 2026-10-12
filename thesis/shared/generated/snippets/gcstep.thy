(* src/Program_Model/CFG/CFG_Exec.thy *)
inductive gcstep :: "('v, 'e) gcfg \<Rightarrow> 'v gcconf \<Rightarrow> 'v gcconf \<Rightarrow> bool" for g where
  Intra [intro]:
    "(u, a, v) \<in> intra g \<Longrightarrow> s' \<in> gedge_step a s \<Longrightarrow> gcstep g (u, s, stk) (v, s', stk)"
| Call [intro]:
    "(u, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls g \<Longrightarrow>
     gcstep g (u, s, stk)
       (FunctionEntry q, gcall_enter (CallEdge dst pars actuals) s, (cont, dst, s) # stk)"
| Return [intro]:
    "gcstep g (FunctionResult q, t, (cont, dst, caller) # stk)
       (cont, gcombine_collect dst caller t, stk)"
