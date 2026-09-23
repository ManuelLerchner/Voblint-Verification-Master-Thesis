(* src/Executable_Surface/CLI/Analysis_Run.thy *)
definition run_voblint ::
    "analysis_domain \<Rightarrow> globals_rule \<Rightarrow> context_mode \<Rightarrow> imp_prog
       \<Rightarrow> String.literal analysis_answer" where
  "run_voblint kind rule ctx p =
     map_analysis_answer string_of_abstract_value
       (analyse_program kind rule ctx p)"
