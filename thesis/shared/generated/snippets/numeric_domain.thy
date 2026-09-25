(* src/Abstract_Interpreter/Domain/Abstract_Domain.thy *)
class numeric_domain = executable_domain +
  fixes gamma :: "'a \<Rightarrow> int set" ("\<gamma>")
  assumes gamma_bot[simp]: "\<gamma> \<bottom> = {}"
  assumes gamma_top[simp]: "\<gamma> \<top> = UNIV"
  assumes gamma_mono: "a \<le> b \<Longrightarrow> \<gamma> a \<subseteq> \<gamma> b"
  assumes is_empty_correct: "is_empty a \<longleftrightarrow> \<gamma> a = {}"
