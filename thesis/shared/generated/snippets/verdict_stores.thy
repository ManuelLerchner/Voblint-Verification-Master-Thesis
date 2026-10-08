(* src/Executable_Surface/CLI/Analysis_Report.thy *)
definition verdict_stores :: "analysis_report \<Rightarrow> pp \<Rightarrow> store set" ("\<V>\<^bsub>_\<^esub>") where
  "\<V>\<^bsub>res\<^esub> v = (\<Inter>c \<in> report_checks_at res v. check_stores c)"
