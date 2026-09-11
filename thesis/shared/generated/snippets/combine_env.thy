(* src/Program_Model/VIMP/VIMP_Globals.thy *)
definition combine_env :: "('k \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('k \<Rightarrow> 'a)" where
  "combine_env gs s t = (\<lambda>n. if gs n then t n else s n)"
