(* vendor/td-verification/Basics.thy *)
inductive_set reach for T \<sigma> x where
  base: "x \<in> reach T \<sigma> x"
| step: "y \<in> reach T \<sigma> x \<Longrightarrow> z \<in> dep T \<sigma> y \<Longrightarrow> z \<in> reach T \<sigma> x"
