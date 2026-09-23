(* src/Program_Model/Compile/Source_To_Trace.thy *)
theorem source_run_has_ltr:
  assumes wf: "wf_compile_input \<G> \<Pi> ps"
    and s0: "s0 \<in> S"
    and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
  shows "\<exists>v stk t.
                   \<Pi>, compile_prog \<Pi> ps \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                   \<and> ltr_repr \<G> (compile_prog \<Pi> ps) S (v, s, stk) t"
