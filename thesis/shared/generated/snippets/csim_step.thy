(* src/Program_Model/Compile/Simulation/Simulation_Preservation.thy *)
theorem csim_step:
  assumes SIM: "\<Pi>, g, \<rho> \<turnstile> (c, s, frs) \<approx> (v, t, stk)"
      and PC: "procs_embedded \<Pi> g"
      and WF: "return_safe c"
      and STEP: "gpstep \<Pi> (c, s, frs) src'"
  shows "\<exists>cfg'. star (gcstep g) (v, t, stk) cfg' \<and> \<Pi>, g, \<rho> \<turnstile> src' \<approx> cfg'"
