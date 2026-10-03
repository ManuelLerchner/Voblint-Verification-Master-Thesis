(* src/Program_Model/Compile/Source_To_Trace.thy *)
lemma cstep_preserves_activation_trace_repr:
  assumes wf: "wf_compile_input \<G> \<Pi> ps"
    and step: "\<G>, compile_prog \<Pi> ps \<turnstile> cf \<rightarrow>\<^sub>c cf'"
    and rep: "activation_trace_repr \<G> (compile_prog \<Pi> ps) S cf t"
  shows "\<exists>t'. activation_trace_repr \<G> (compile_prog \<Pi> ps) S cf' t'"
