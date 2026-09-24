(* src/Program_Model/Compile/Simulation/Source_Progress.thy *)
theorem source_progress:
  assumes wf: "wf_source_program \<G> \<Pi>"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (c, s, frs)"
  shows "(c = SKIP \<and> frs = []) \<or> (\<exists>cfg'. \<G>, \<Pi> \<turnstile> (c, s, frs) \<rightarrow>\<^sub>p cfg')"
