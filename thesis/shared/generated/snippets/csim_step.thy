(* src/Program_Model/Compile/Simulation/Simulation_Preservation.thy *)
theorem csim_step:
  assumes SIM: "\<Pi>, g \<turnstile> (c, s, frs) \<approx> (v, t, stk)"
      and PC: "procs_embedded \<Pi> g"
      and WF: "return_safe c"
      and STEP: "\<G>, \<Pi> \<turnstile> (c, s, frs) \<rightarrow>\<^sub>p src'"
  shows "\<exists>cfg'. \<G>, g \<turnstile> (v, t, stk) \<rightarrow>\<^sub>c\<^sup>* cfg' \<and> \<Pi>, g \<turnstile> src' \<approx> cfg'"
