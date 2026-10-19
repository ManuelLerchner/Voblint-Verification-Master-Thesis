(* src/Executable_Surface/CLI/Run_Voblint.thy *)
definition run_voblint :: "voblint_conf \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> report analysis_answer" where
  "run_voblint conf ds p =
     (if \<not> valid_activation (conf_analyses conf) then Invalid_Activation
      else if \<not> wf_program_compile_input_exec p then Malformed_Program
      else case report_run conf ds p of
             None \<Rightarrow> No_Answer
           | Some res \<Rightarrow> Analysed res)"
