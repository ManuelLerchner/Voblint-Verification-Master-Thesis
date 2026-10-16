(* src/Program_Model/Compile/Source_To_Trace.thy *)
lemma cstep_preserves_activation_trace_repr:
  assumes wf: "gwf_compile_input vars ReturnVar is_global \<Pi> ps"
    and step: "\<kappa>,(compile_prog \<Pi> ps) \<turnstile> cf \<rightarrow>\<^sub>c cf'"
    and rep: "activation_trace_repr \<kappa> (compile_prog \<Pi> ps) S cf t"
  shows "\<exists>t'. activation_trace_repr \<kappa> (compile_prog \<Pi> ps) S cf' t'"
