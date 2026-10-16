(* src/Program_Model/Compile/Simulation/Source_Progress.thy *)
theorem source_progress:
  assumes wf: "gwf_source_program vars ReturnVar is_global \<Pi>"
      and run: "\<kappa>,\<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (c, s, frs)"
  shows "(is_SKIP c \<and> frs = []) \<or> (\<exists>cfg'. \<kappa>,\<Pi> \<turnstile> (c, s, frs) \<rightarrow>\<^sub>p cfg')"
