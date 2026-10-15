(* src/Program_Model/Compile/Source_To_Trace.thy *)
theorem source_run_has_activation_trace:
  assumes wf: "gwf_compile_input vars rv glob \<Pi> ps"
    and s0: "s0 \<in> S"
    and run: "star (gpstep \<Pi>) (main_body \<Pi>, s0, []) (residual, s, frs)"
  shows "\<exists>v stk t. \<Pi>, compile_prog \<Pi> ps, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                   \<and> gactivation_trace_repr (compile_prog \<Pi> ps) S (v, s, stk) t"
