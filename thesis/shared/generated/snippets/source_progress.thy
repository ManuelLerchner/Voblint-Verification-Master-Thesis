(* src/Program_Model/Compile/Simulation/Source_Progress.thy *)
theorem source_progress:
  assumes wf: "gwf_source_program vars rv glob \<Pi>"
      and run: "star (gpstep \<Pi>) (main_body \<Pi>, s0, []) (c, s, frs)"
  shows "(is_SKIP c \<and> frs = []) \<or> (\<exists>cfg'. gpstep \<Pi> (c, s, frs) cfg')"
