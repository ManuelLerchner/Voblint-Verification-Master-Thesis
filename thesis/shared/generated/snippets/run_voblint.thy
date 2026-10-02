(* src/Executable_Surface/CLI/Analysis_Run.thy *)
definition run_voblint :: "analysis_config \<Rightarrow> imp_prog \<Rightarrow> analysis_report analysis_answer"
where
  "run_voblint config p =
     (if \<not> valid_config config then Invalid_Activation
      else if \<not> wf_program_compile_input_exec p then Malformed_Program
      else case analysis_report_of config p of
             None \<Rightarrow> No_Answer
           | Some res \<Rightarrow> Analysed res)"
