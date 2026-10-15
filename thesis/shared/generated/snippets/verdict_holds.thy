(* src/Executable_Surface/CLI/Analysis_Report.thy *)
fun verdict_holds :: "('e \<Rightarrow> 't \<Rightarrow> int) \<Rightarrow> check_result \<Rightarrow> 'e \<Rightarrow> 't \<Rightarrow> bool" where
  "verdict_holds ev Check_Proved e s = truthy (ev e s)"
| "verdict_holds ev Check_Refuted e s = (\<not> truthy (ev e s))"
| "verdict_holds ev Check_Unknown e s = True"
