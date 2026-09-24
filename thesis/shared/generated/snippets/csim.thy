(* src/Program_Model/Compile/Simulation/Simulation_Relation.thy *)
inductive csim :: "proc_table \<Rightarrow> cfg \<Rightarrow> com \<times> store \<times> frame list
                    \<Rightarrow> cfg_node \<times> store \<times> cframe list \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<approx>/ _)" [51, 51, 51, 51] 50) for \<Pi> g where
  Base:
    "control_at \<Pi> p c0 k n c v \<Longrightarrow> compiled_at \<Pi> g p c0 k n \<Longrightarrow>
     \<Pi>, g \<turnstile> (c, s, []) \<approx> (v, s, [])"
| Nested:
    "\<Pi>, g \<turnstile> (inner, s, frs) \<approx> (v, s, stk) \<Longrightarrow>
     control_at \<Pi> pc c0c kc nc (seq_after SKIP afters) cont \<Longrightarrow>
     compiled_at \<Pi> g pc c0c kc nc \<Longrightarrow>
     \<Pi>, g \<turnstile> (seq_after (Seq inner Restore) afters, s, frs @ [Frame caller dst]) \<approx> (v, s, stk @ [(cont, dst, caller)])"
| Returning:
    "pop_ready w \<Longrightarrow>
     control_at \<Pi> pc c0c kc nc (seq_after SKIP afters) cont \<Longrightarrow>
     compiled_at \<Pi> g pc c0c kc nc \<Longrightarrow>
     \<Pi>, g \<turnstile> (seq_after w afters, callee, [Frame caller dst]) \<approx> (FunctionResult p, callee, [(cont, dst, caller)])"
