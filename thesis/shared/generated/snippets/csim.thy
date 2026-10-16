(* src/Program_Model/Compile/Simulation/Simulation_Relation.thy *)
inductive csim :: "('a, var_id, exp) gptable \<Rightarrow> (var_id, exp) gcfg \<Rightarrow> pname
                    \<Rightarrow> ('a, var_id, exp) gcom \<times> store \<times> frame list
                    \<Rightarrow> cfg_node \<times> store \<times> cframe list \<Rightarrow> bool"
    ("(_,_,_ \<turnstile>/ _ \<approx>/ _)" [51, 51, 51, 51, 51] 50) for \<Pi> g where
  Base:
    "control_at \<Pi> p body_p k n c v \<Longrightarrow> compiled_at \<Pi> g p body_p k n \<Longrightarrow>
     \<Pi>, g, p \<turnstile> (c, s, []) \<approx> (v, s, [])"
| Nested:
    "\<Pi>, g, q \<turnstile> (inner, s, frs) \<approx> (v, s, stk) \<Longrightarrow>
     control_at \<Pi> pc body_pc kc nc (seq_after (SKIP i) afters) cont \<Longrightarrow>
     control_at \<Pi> pc body_pc kc nc (seq_after (Call i dst q args) afters) site \<Longrightarrow>
     compiled_at \<Pi> g pc body_pc kc nc \<Longrightarrow>
     \<Pi>, g, pc \<turnstile> (seq_after (Seq inner (Restore i)) afters, s, frs @ [Frame caller dst])
       \<approx> (v, s, stk @ [(cont, dst, caller)])"
| Returning:
    "pop_ready w \<Longrightarrow> pop_ann w = Some i \<Longrightarrow>
     control_at \<Pi> pc body_pc kc nc (seq_after (SKIP i) afters) cont \<Longrightarrow>
     control_at \<Pi> pc body_pc kc nc (seq_after (Call i dst q args) afters) site \<Longrightarrow>
     compiled_at \<Pi> g pc body_pc kc nc \<Longrightarrow>
     \<Pi>, g, pc \<turnstile> (seq_after w afters, callee, [Frame caller dst])
       \<approx> (FunctionResult q, callee, [(cont, dst, caller)])"
