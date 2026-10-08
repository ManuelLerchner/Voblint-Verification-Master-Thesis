(* src/Executable_Surface/CLI/Analysis_Report.thy *)
definition check_stores :: "result_check \<Rightarrow> store set" where
  "check_stores c = (case check_verdict c of
                       Decided r \<Rightarrow> {s. verdict_holds r (check_exp c) s}
                     | Dead \<Rightarrow> UNIV)"
