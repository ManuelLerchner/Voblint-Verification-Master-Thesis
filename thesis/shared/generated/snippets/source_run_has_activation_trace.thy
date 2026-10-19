(* src/Program_Model/Compile/Source_To_Trace.thy *)
theorem compile_prog_run_has_activation_trace:
  assumes wf: "gwf_compile_input vars ReturnVar is_global \<Pi> ps"
    and s0: "s0 \<in> S"
    and run: "\<kappa>,\<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
  shows "\<exists>v stk t. \<Pi>, compile_prog \<Pi> ps, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                   \<and> activation_trace_repr \<kappa> (compile_prog \<Pi> ps) S (v, s, stk) t"
