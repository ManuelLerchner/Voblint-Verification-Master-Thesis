(* src/Abstract_Interpreter/Domain/Eval/Numeric_Queries.thy *)
locale sound_numeric_queries =
  fixes less :: "'a::numeric_domain \<Rightarrow> 'a \<Rightarrow> bool option"
    and eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
  assumes less_sound[intro]:
      "less a b = Some r \<Longrightarrow> i \<in> \<gamma> a \<Longrightarrow> j \<in> \<gamma> b \<Longrightarrow> (i < j) = r"
    and eq_sound[intro]:
      "eq a b = Some r \<Longrightarrow> i \<in> \<gamma> a \<Longrightarrow> j \<in> \<gamma> b \<Longrightarrow> (i = j) = r"
