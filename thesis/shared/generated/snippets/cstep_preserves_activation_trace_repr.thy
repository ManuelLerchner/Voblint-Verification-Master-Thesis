(* src/Program_Model/Compile/Source_To_Trace.thy *)
lemma cstep_preserves_activation_trace_repr:
  assumes wf: "gwf_compile_input vars rv glob \<Pi> ps"
    and step: "gcstep (compile_prog \<Pi> ps) cf cf'"
    and rep: "gactivation_trace_repr (compile_prog \<Pi> ps) S cf t"
  shows "\<exists>t'. gactivation_trace_repr (compile_prog \<Pi> ps) S cf' t'"
