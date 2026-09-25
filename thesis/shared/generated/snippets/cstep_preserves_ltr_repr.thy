(* src/Program_Model/Compile/Source_To_Trace.thy *)
lemma cstep_preserves_ltr_repr:
  assumes wf: "wf_compile_input \<G> \<Pi> ps"
    and step: "\<G>, compile_prog \<Pi> ps \<turnstile> cf \<rightarrow>\<^sub>c cf'"
    and rep: "ltr_repr \<G> (compile_prog \<Pi> ps) S cf t"
  shows "\<exists>t'. ltr_repr \<G> (compile_prog \<Pi> ps) S cf' t'"
