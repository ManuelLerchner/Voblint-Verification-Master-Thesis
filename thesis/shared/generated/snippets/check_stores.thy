(* src/Executable_Surface/CLI/Analysis_Report.thy *)
definition check_stores :: "('e \<Rightarrow> 't \<Rightarrow> int) \<Rightarrow> 'e result_check \<Rightarrow> 't set" where
  "check_stores ev c = (case check_verdict c of
                          Decided r \<Rightarrow> {s. verdict_holds ev r (check_exp c) s}
                        | Dead \<Rightarrow> UNIV)"
