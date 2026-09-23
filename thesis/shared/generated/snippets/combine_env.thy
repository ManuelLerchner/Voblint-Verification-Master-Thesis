(* src/Program_Model/VIMP/VIMP_Globals.thy *)
definition combine_env ::
    "('k \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('k \<Rightarrow> 'a)" where
  "combine_env \<G> s t = (\<lambda>n. if \<G> n then t n else s n)"
