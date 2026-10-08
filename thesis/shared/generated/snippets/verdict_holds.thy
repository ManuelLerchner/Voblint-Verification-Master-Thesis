(* src/Executable_Surface/CLI/Analysis_Report.thy *)
fun verdict_holds :: "check_result \<Rightarrow> exp \<Rightarrow> store \<Rightarrow> bool" where
  "verdict_holds Check_Proved e s = truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
| "verdict_holds Check_Refuted e s = (\<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))"
| "verdict_holds Check_Unknown e s = True"
